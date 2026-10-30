section \<open>Атаки на леммы: исполняемые негативные свидетели\<close>

theory Zircon_Attacks
  imports
    Zircon
    Zircon_MMIO
    "HOL-Library.Code_Target_Nat"
    "HOL-Library.Code_Test"
begin

text \<open>
  Набор сценариев, которые \<^emph>\<open>пытаются\<close> обойти security-леммы: передать
  без @{text TRANSFER}, запросить лишние права, прочитать своё сообщение,
  записать VMO без @{text WRITE}, сдублировать без @{text DUPLICATE}, создать
  «битую» маску и~т.д. Константа истинна, если атака \<^emph>\<open>отбита\<close>
  (syscall вернул @{text None} или получатель не эскалировал).

  Исключение --- @{text bypass_mmio_store}: это известный обход
  \<^emph>\<open>изоляции store\<close> через poke; capability-леммы при этом живы.
  Сборка (@{text "value [code]"} / @{text eval} / @{text test_code})
  падает, если какой-то страж перестал срабатывать.
\<close>

definition atk_base :: system_state where
  "atk_base = init_process 1 (init_process 0 empty_state)"

definition atk_vmo_full :: rights where
  "atk_vmo_full = {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}"

definition atk_vmo_dup :: rights where
  "atk_vmo_dup = {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER, ZX_RIGHT_DUPLICATE}"

text \<open>
  Стандартный мир: два процесса, пиры канала, VMO с полными правами у~0.
  @{text None} здесь означал~бы поломку \<^emph>\<open>постановки\<close>, а не успех атаки.
\<close>

definition atk_world ::
    "(handle_id \<times> handle_id \<times> handle_id \<times> obj_id \<times> system_state) option" where
  "atk_world =
    (case create_channel_pair 0 1 example_channel_rights example_channel_rights atk_base of
       None \<Rightarrow> None
     | Some (ch0, ch1, _, s1) \<Rightarrow>
         (case create_vmo 0 atk_vmo_full 42 s1 of
            None \<Rightarrow> None
          | Some (hid, oid, s2) \<Rightarrow> Some (ch0, ch1, hid, oid, s2)))"

subsection \<open>Атаки, которые обязаны получить None\<close>

text \<open>\<^bold>\<open>1.\<close> Передача без @{text TRANSFER} --- @{text channel_write_requires_transfer}.\<close>

definition attack_no_transfer :: bool where
  "attack_no_transfer =
    (case create_channel_pair 0 1 example_channel_rights example_channel_rights atk_base of
       None \<Rightarrow> False
     | Some (ch0, ch1, _, s1) \<Rightarrow>
         (case create_vmo 0 {ZX_RIGHT_READ, ZX_RIGHT_WRITE} 42 s1 of
            None \<Rightarrow> False
          | Some (hid, _, s2) \<Rightarrow>
              transfer_via_channel 0 1 ch0 ch1 hid {ZX_RIGHT_READ} s2 = None))"

text \<open>\<^bold>\<open>2.\<close> Писать в канал без @{text WRITE} на endpoint.\<close>

definition attack_no_channel_write :: bool where
  "attack_no_channel_write =
    (case create_channel_pair 0 1 {ZX_RIGHT_READ} example_channel_rights atk_base of
       None \<Rightarrow> False
     | Some (ch0, ch1, _, s1) \<Rightarrow>
         (case create_vmo 0 atk_vmo_full 42 s1 of
            None \<Rightarrow> False
          | Some (hid, _, s2) \<Rightarrow>
              transfer_via_channel 0 1 ch0 ch1 hid {ZX_RIGHT_READ} s2 = None))"

text \<open>
  \<^bold>\<open>3.\<close> Запрос сверх источника (@{text SIGNAL} не было у payload) ---
  @{text channel_write_fails_unless_subset}.
\<close>

definition attack_widen_request :: bool where
  "attack_widen_request =
    (case atk_world of
       None \<Rightarrow> False
     | Some (ch0, ch1, hid, _, s) \<Rightarrow>
         transfer_via_channel 0 1 ch0 ch1 hid {ZX_RIGHT_SIGNAL} s = None)"

text \<open>\<^bold>\<open>4.\<close> Отправить канал в самого себя --- @{text ZX_ERR_NOT_SUPPORTED}.\<close>

definition attack_self_send :: bool where
  "attack_self_send =
    (let rs = {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER} in
     case create_channel_pair 0 1 rs rs atk_base of
       None \<Rightarrow> False
     | Some (ch0, _, _, s1) \<Rightarrow>
         zx_channel_write 0 ch0 ch0 {ZX_RIGHT_READ} s1 = None)"

text \<open>\<^bold>\<open>5.\<close> Self-read: после write своя очередь пуста, читает пир.\<close>

definition attack_self_read :: bool where
  "attack_self_read =
    (case atk_world of
       None \<Rightarrow> False
     | Some (ch0, ch1, hid, _, s) \<Rightarrow>
         (case zx_channel_write 0 ch0 hid {ZX_RIGHT_READ} s of
            None \<Rightarrow> False
          | Some s' \<Rightarrow>
              zx_channel_read 0 ch0 s' = None \<and>
              (case zx_channel_read 1 ch1 s' of None \<Rightarrow> False | Some _ \<Rightarrow> True)))"

text \<open>\<^bold>\<open>6.\<close> Duplicate без @{text DUPLICATE}.\<close>

definition attack_no_duplicate :: bool where
  "attack_no_duplicate =
    (case atk_world of
       None \<Rightarrow> False
     | Some (_, _, hid, _, s) \<Rightarrow>
         zx_handle_duplicate 0 hid {ZX_RIGHT_READ} s = None)"

text \<open>\<^bold>\<open>7.\<close> Duplicate с запросом шире источника.\<close>

definition attack_dup_widen :: bool where
  "attack_dup_widen =
    (case create_channel_pair 0 1 example_channel_rights example_channel_rights atk_base of
       None \<Rightarrow> False
     | Some (_, _, _, s1) \<Rightarrow>
         (case create_vmo 0 atk_vmo_dup 42 s1 of
            None \<Rightarrow> False
          | Some (hid, _, s2) \<Rightarrow>
              zx_handle_duplicate 0 hid {ZX_RIGHT_SIGNAL} s2 = None))"

text \<open>\<^bold>\<open>8.\<close> Запись в VMO без @{text WRITE} после передачи только @{text READ}.\<close>

definition attack_vmo_write_no_write :: bool where
  "attack_vmo_write_no_write =
    (case atk_world of
       None \<Rightarrow> False
     | Some (ch0, ch1, hid, oid, s) \<Rightarrow>
         (case transfer_via_channel 0 1 ch0 ch1 hid {ZX_RIGHT_READ} s of
            None \<Rightarrow> False
          | Some (hid_b, s') \<Rightarrow>
              vmo_write 1 hid_b 99 s' = None \<and> vmo_content oid s' = Some 42))"

text \<open>\<^bold>\<open>9.\<close> Создать VMO с @{text WRITE} без @{text READ} --- инвариант не даёт войти.\<close>

definition attack_illformed_create :: bool where
  "attack_illformed_create =
    (create_vmo 0 {ZX_RIGHT_WRITE} 1 atk_base = None)"

text \<open>\<^bold>\<open>10.\<close> Пустые права на канал: ни write, ни read.\<close>

definition attack_empty_channel :: bool where
  "attack_empty_channel =
    (case create_channel_pair 0 1 {} example_channel_rights atk_base of
       None \<Rightarrow> False
     | Some (ch0, _, _, s1) \<Rightarrow>
         (case create_vmo 0 atk_vmo_full 42 s1 of
            None \<Rightarrow> False
          | Some (hid, _, s2) \<Rightarrow>
              zx_channel_write 0 ch0 hid {ZX_RIGHT_READ} s2 = None \<and>
              zx_channel_read 0 ch0 s2 = None))"

subsection \<open>Атака «попросить WRITE» --- не эскалация\<close>

text \<open>
  Источник well-formed и содержит @{text WRITE}. Запрос @{text "{WRITE}"} замыкается
  в @{text "{READ, WRITE}"}; оба бита уже были у источника. Это не обход
  no-escalation, а проверка, что «вернуть READ» не чеканит новое право.
\<close>

definition attack_write_request_no_escalate :: bool where
  "attack_write_request_no_escalate =
    (case atk_world of
       None \<Rightarrow> False
     | Some (ch0, ch1, hid, _, s) \<Rightarrow>
         (case transfer_via_channel 0 1 ch0 ch1 hid {ZX_RIGHT_WRITE} s of
            None \<Rightarrow> False
          | Some (hid_b, s') \<Rightarrow>
              (case (lookup_handle 0 hid s, lookup_handle 1 hid_b s') of
                 (Some h_src, Some h_dst) \<Rightarrow>
                   ZX_RIGHT_WRITE \<in> h_rights h_dst \<and>
                   ZX_RIGHT_READ \<in> h_rights h_dst \<and>
                   h_rights h_dst \<subseteq> h_rights h_src
               | _ \<Rightarrow> False)))"

text \<open>
  Без инварианта замыкание \<^emph>\<open>было бы\<close> эскалацией. Syscall так создать
  маску не даёт (см.\ @{text attack_illformed_create}); это свойство
  оператора, не трассы.
\<close>

definition attack_closure_on_illformed :: bool where
  "attack_closure_on_illformed \<longleftrightarrow>
     \<not> rights_wf {ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER} \<and>
     \<not> (reduce_rights_wf {ZX_RIGHT_WRITE}
          {ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}
        \<subseteq> {ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER})"

subsection \<open>Обход, который модель не обещает закрыть\<close>

definition bypass_mmio_store :: bool where
  "bypass_mmio_store = mmio_leak_witness"

subsection \<open>Сводка\<close>

definition attacks_blocked_all :: bool where
  "attacks_blocked_all \<longleftrightarrow>
     attack_no_transfer \<and>
     attack_no_channel_write \<and>
     attack_widen_request \<and>
     attack_self_send \<and>
     attack_self_read \<and>
     attack_no_duplicate \<and>
     attack_dup_widen \<and>
     attack_vmo_write_no_write \<and>
     attack_illformed_create \<and>
     attack_empty_channel \<and>
     attack_write_request_no_escalate \<and>
     attack_closure_on_illformed"

lemma bypass_mmio_store_true:
  "bypass_mmio_store"
  by (simp add: bypass_mmio_store_def mmio_leak_witness_true)

value [code] attacks_blocked_all
value [code] bypass_mmio_store
value [code] attack_no_transfer
value [code] attack_self_read
value [code] attack_write_request_no_escalate
value [code] attack_closure_on_illformed

lemma attacks_blocked_all_by_eval:
  "attacks_blocked_all"
  by eval

lemma bypass_mmio_store_by_eval:
  "bypass_mmio_store"
  by eval

test_code "attacks_blocked_all" in OCaml
test_code "bypass_mmio_store" in OCaml

end
