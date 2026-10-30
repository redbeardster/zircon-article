section \<open>Привилегированный обход MMIO (безопасность vs совместимость)\<close>

theory Zircon_MMIO
imports
  Zircon
  Zircon_Traces
begin

text \<open>
  Промышленные ядра иногда выдают драйверам прямой доступ к регистрам / MMIO,
  не опосредованный теми же capability-проверками, что обычные handles
  (ср.\ стеки модемов, слои совместимости вроде Starnix). Мы моделируем этот
  компромисс как один привилегированный poke в @{text vmo_store} по сырому
  @{typ obj_id}, \<^emph>\<open>без\<close> @{const lookup_handle} и без шлюза @{text WRITE}.

  Это \<^emph>\<open>гипотетический\<close> обход, а не описание Fuchsia: там MMIO выдаётся через
  ресурс @{text ZX_RSRC_KIND_MMIO} и физический VMO, а DMA ограничен IOMMU
  через BTI (@{text zx_bti_pin}). Poke моделирует ситуацию, когда такой
  медиации \<^emph>\<open>нет\<close> --- например, из-за компромисса совместимости.

  Цель~--- отрицательная: как только такой путь существует, дисциплина
  capability уже не влечёт целостность чужого содержимого VMO. Мы предъявляем
  явный свидетель, а не универсальную теорему безопасности.
\<close>

subsection \<open>Объект Hardware и привилегированный poke\<close>

text \<open>
  @{text Hardware} расширяет @{typ kernel_obj_type} (объявлен в основной
  модели). Compatibility-shim может mint'ить такие объекты; опасна не сама
  метка типа, а неопосредованное обновление store ниже.
\<close>

definition privileged_vmo_poke ::
  "obj_id \<Rightarrow> nat \<Rightarrow> system_state \<Rightarrow> system_state" where
  "privileged_vmo_poke oid content s =
     s\<lparr> vmo_store := (vmo_store s)(oid \<mapsto> content) \<rparr>"

text \<open>
  В отличие от @{const vmo_write}, poke никогда не возвращает @{text None}:
  нет handle, нет проверки типа и нет проверки прав.
\<close>

lemma privileged_vmo_poke_always:
  "vmo_content oid (privileged_vmo_poke oid content s) = Some content"
  by (simp add: privileged_vmo_poke_def vmo_content_def)

lemma privileged_preserves_handles_wf:
  assumes "handles_wf s"
  shows "handles_wf (privileged_vmo_poke oid content s)"
  using assms by (simp add: handles_wf_def privileged_vmo_poke_def)

lemma privileged_preserves_channels_wf:
  assumes "channels_caps_wf s"
  shows "channels_caps_wf (privileged_vmo_poke oid content s)"
  using assms by (simp add: channels_caps_wf_def privileged_vmo_poke_def)

lemma privileged_preserves_peers_wf:
  assumes "peers_wf s"
  shows "peers_wf (privileged_vmo_poke oid content s)"
  by (rule peers_wf_cong[OF assms]) (simp_all add: privileged_vmo_poke_def)

lemma privileged_preserves_state_wf:
  assumes "state_wf s"
  shows "state_wf (privileged_vmo_poke oid content s)"
  using assms privileged_preserves_handles_wf privileged_preserves_channels_wf
        privileged_preserves_peers_wf
  by (simp add: state_wf_def)

subsection \<open>Capability-шлюз vs привилегированный обход\<close>

text \<open>
  Если процесс держит VMO-handle без @{text WRITE}, обычный
  @{const vmo_write} отказывает~--- но привилегированный poke всё равно
  перезаписывает запись store для этого @{text obj_id}.
\<close>

lemma capability_denies_but_privileged_writes:
  assumes "lookup_handle pid hid s = Some h"
  assumes "obj_type (h_obj h) = VMO"
  assumes "ZX_RIGHT_WRITE \<notin> h_rights h"
  assumes "obj_id (h_obj h) = oid"
  shows "vmo_write pid hid content s = None"
    and "vmo_content oid (privileged_vmo_poke oid content s) = Some content"
  using assms
  by (simp_all add: vmo_write_denied_without_write_right privileged_vmo_poke_always)

subsection \<open>Конкретный свидетель утечки (учебный сценарий)\<close>

text \<open>
  Стартуем с обычной постановки: процесс~0 создаёт VMO с содержимым~42 и
  передаёт процессу~1 только @{text READ}. Процесс~1 не может мутировать
  через @{const vmo_write}, однако привилегированный poke (модель MMIO /
  DMA драйвера в тот же backing store) меняет содержимое на~99, пока у
  процесса~1 по-прежнему нет @{text WRITE}.
\<close>

definition mmio_leak_witness :: bool where
  "mmio_leak_witness =
    (let s0 = init_process 1 (init_process 0 empty_state);
         rights_a = {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}
     in case create_channel_pair 0 1 example_channel_rights example_channel_rights s0 of
          None \<Rightarrow> False
        | Some (ch0, ch1, _, s1) \<Rightarrow>
            (case create_vmo 0 rights_a 42 s1 of
               None \<Rightarrow> False
             | Some (hid_a, oid, s2) \<Rightarrow>
                 (case transfer_via_channel 0 1 ch0 ch1 hid_a {ZX_RIGHT_READ} s2 of
                    None \<Rightarrow> False
                  | Some (hid_b, s3) \<Rightarrow>
                      (case lookup_handle 1 hid_b s3 of
                         None \<Rightarrow> False
                       | Some h_b \<Rightarrow>
                           ZX_RIGHT_WRITE \<notin> h_rights h_b \<and>
                           vmo_write 1 hid_b 99 s3 = None \<and>
                           vmo_content oid s3 = Some 42 \<and>
                           (let s4 = privileged_vmo_poke oid 99 s3
                            in vmo_content oid s4 = Some 99 \<and>
                               lookup_handle 1 hid_b s4 = Some h_b \<and>
                               ZX_RIGHT_WRITE \<notin> h_rights h_b)))))"

lemma mmio_leak_witness_true:
  "mmio_leak_witness"
  unfolding mmio_leak_witness_def example_channel_rights_def
            empty_state_def init_process_def create_channel_pair_def
            create_vmo_def transfer_via_channel_def zx_channel_write_def
            zx_channel_read_def alloc_hid_def set_table_def get_table_def
            lookup_handle_def reduce_rights_def reduce_rights_wf_def
            close_rights_def rights_wf_def
            vmo_write_def vmo_content_def privileged_vmo_poke_def Let_def
  by simp

text \<open>
  \<^bold>\<open>Архитектурное прочтение.\<close>
  @{thm mmio_leak_witness_true}~--- не баг в capability-леммах: они по-прежнему
  верны для опосредованных syscall'ов. Он показывает, что \<^emph>\<open>добавление\<close>
  неопосредованного пути делает «нет чужой мутации VMO без WRITE»
  недоказуемым как общесистемное утверждение. Compatibility-shortcuts,
  пишущие в память в обход таблицы handles, имеют ту же форму.
\<close>

subsection \<open>Почему трассовая изоляция ломается, когда poke~--- шаг\<close>

datatype step_compat =
    Mediated "step"
  | Privileged_Poke "obj_id" "nat"

fun exec_step_compat :: "step_compat \<Rightarrow> system_state \<Rightarrow> system_state option" where
  "exec_step_compat (Mediated st) s = exec_step st s"
| "exec_step_compat (Privileged_Poke oid content) s =
     Some (privileged_vmo_poke oid content s)"

inductive reachable_compat :: "system_state \<Rightarrow> system_state \<Rightarrow> bool" where
  reflc: "reachable_compat s s"
| stepc: "reachable_compat s s1 \<Longrightarrow> exec_step_compat st s1 = Some s2 \<Longrightarrow>
            reachable_compat s s2"

text \<open>
  Корректность масок прав по-прежнему переживает привилегированные poke,
  поэтому один @{const state_wf} не фиксирует изоляцию store.
\<close>

lemma exec_step_compat_preserves_state_wf:
  assumes "state_wf s"
  assumes "exec_step_compat st s = Some s'"
  shows "state_wf s'"
  using assms
proof (cases st)
  case (Mediated st')
  with assms show ?thesis
    using exec_step_preserves_wf by simp
next
  case (Privileged_Poke oid content)
  with assms have "s' = privileged_vmo_poke oid content s" by simp
  with assms(1) show ?thesis
    using privileged_preserves_state_wf by simp
qed

definition vmo_write_gate_holds :: "system_state \<Rightarrow> bool" where
  "vmo_write_gate_holds s \<longleftrightarrow>
     (\<forall>pid hid content h.
        lookup_handle pid hid s = Some h \<longrightarrow>
        obj_type (h_obj h) = VMO \<longrightarrow>
        ZX_RIGHT_WRITE \<notin> h_rights h \<longrightarrow>
        vmo_write pid hid content s = None)"

lemma vmo_write_gate_holds_unconditionally:
  "vmo_write_gate_holds s"
  by (auto simp: vmo_write_gate_holds_def vmo_write_def)

text \<open>
  Опосредованный шлюз в порядке; целостность @{text vmo_store} при
  @{const reachable_compat}~--- нет: свидетель утечки~--- конкретный
  контрпример к любому утверждению вида «содержимое меняется только через
  успешный @{const vmo_write}».
\<close>

definition store_only_via_vmo_write :: "system_state \<Rightarrow> system_state \<Rightarrow> bool" where
  "store_only_via_vmo_write s s' \<longleftrightarrow>
     (vmo_store s' \<noteq> vmo_store s \<longrightarrow>
       (\<exists>pid hid content. vmo_write pid hid content s = Some s'))"

lemma privileged_poke_changes_store:
  assumes "vmo_store s oid = Some old"
  assumes "content \<noteq> old"
  shows "vmo_store (privileged_vmo_poke oid content s) \<noteq> vmo_store s"
proof
  assume "vmo_store (privileged_vmo_poke oid content s) = vmo_store s"
  then have "((vmo_store s)(oid \<mapsto> content)) oid = vmo_store s oid"
    by (simp add: privileged_vmo_poke_def)
  hence "Some content = Some old" using assms(1) by simp
  with assms(2) show False by simp
qed

lemma vmo_write_needs_handle:
  assumes "vmo_write pid hid content s = Some s'"
  shows "\<exists>h. lookup_handle pid hid s = Some h"
  using assms by (auto simp: vmo_write_def split: option.splits if_splits)

lemma privileged_poke_not_only_via_vmo_write:
  assumes "vmo_store s oid = Some old"
  assumes "content \<noteq> old"
  assumes "proc_tables s = Map.empty"
  shows "\<not> store_only_via_vmo_write s (privileged_vmo_poke oid content s)"
proof
  assume only: "store_only_via_vmo_write s (privileged_vmo_poke oid content s)"
  from privileged_poke_changes_store[OF assms(1,2)] only
  obtain pid hid c where
    w: "vmo_write pid hid c s = Some (privileged_vmo_poke oid content s)"
    by (auto simp: store_only_via_vmo_write_def)
  from vmo_write_needs_handle[OF w] obtain h where
    "lookup_handle pid hid s = Some h" by blast
  with assms(3) show False
    by (simp add: lookup_handle_def)
qed

lemma mmio_breaks_store_only_via_vmo_write:
  "\<exists>s oid. vmo_store s oid = Some 42 \<and>
           \<not> store_only_via_vmo_write s (privileged_vmo_poke oid 99 s)"
proof -
  let ?s = "empty_state\<lparr> vmo_store := [0 \<mapsto> 42] \<rparr>"
  have "vmo_store ?s 0 = Some 42" by (simp add: empty_state_def)
  moreover have "proc_tables ?s = Map.empty" by (simp add: empty_state_def)
  ultimately have
    "\<not> store_only_via_vmo_write ?s (privileged_vmo_poke 0 99 ?s)"
    by (simp add: privileged_poke_not_only_via_vmo_write)
  then show ?thesis using \<open>vmo_store ?s 0 = Some 42\<close> by blast
qed

end
