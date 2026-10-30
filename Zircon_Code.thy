theory Zircon_Code
  imports
    Zircon
    "HOL-Library.Code_Target_Nat"
    "HOL-Library.Code_Test"
begin

text \<open>
  Экстракция исполняемого кода из верифицированной модели.
  Команда @{text export_code} порождает OCaml-модуль; @{text value}~[code]
  и тактика @{text eval} проверяют те~же константы внутри Isabelle;
  @{text test_code} прогоняет их внешним компилятором OCaml.
\<close>

definition example_setup :: system_state where
  "example_setup = init_process 1 (init_process 0 empty_state)"

definition example_rights_a :: rights where
  "example_rights_a = {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}"

definition example_exec_ok :: bool where
  "example_exec_ok =
    (case create_channel_pair 0 1 example_channel_rights example_channel_rights
            example_setup of
      None \<Rightarrow> False
    | Some (ch0, ch1, _, s1) \<Rightarrow>
        (case create_vmo 0 example_rights_a 42 s1 of
           None \<Rightarrow> False
         | Some (hid_a, oid, s2) \<Rightarrow>
             (case transfer_via_channel 0 1 ch0 ch1 hid_a {ZX_RIGHT_READ} s2 of
                None \<Rightarrow> False
              | Some (hid_b, s3) \<Rightarrow>
                  lookup_handle 0 hid_a s3 = None \<and>
                  vmo_write 1 hid_b 99 s3 = None \<and>
                  vmo_content oid s3 = Some 42)))"

lemma example_exec_ok_true:
  "example_exec_ok"
  unfolding example_exec_ok_def example_setup_def example_rights_a_def
            example_channel_rights_def
  by (simp add: example_scenario_def create_vmo_def create_channel_pair_def
        transfer_via_channel_def zx_channel_write_def zx_channel_read_def
        alloc_hid_def set_table_def get_table_def empty_state_def
        init_process_def lookup_handle_def reduce_rights_def
        reduce_rights_wf_def close_rights_def rights_wf_def
        vmo_write_def vmo_content_def Let_def)

definition example_empty_exec_ok :: bool where
  "example_empty_exec_ok = example_empty_rights_ok"

lemma example_empty_exec_ok_true:
  "example_empty_exec_ok"
  by (simp add: example_empty_exec_ok_def example_empty_rights_ok_true)

subsection \<open>Вычисление утверждений: value и eval\<close>

text \<open>
  Нормальные формы кодогенератора для ключевых свидетелей. В PIDE команды
  @{text value} печатают результат; леммы ниже фиксируют те~же равенства
  через тактику @{text eval}, так что сборка сессии падает при расхождении.
\<close>

value [code] example_exec_ok
value [code] example_empty_exec_ok
value [code] example_scenario
value [code] example_empty_rights_ok
value [code]
  "reduce_rights_wf {ZX_RIGHT_WRITE}
     {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}"

lemma example_exec_ok_by_eval:
  "example_exec_ok"
  by eval

lemma example_empty_exec_ok_by_eval:
  "example_empty_exec_ok"
  by eval

lemma example_scenario_by_eval:
  "example_scenario"
  by eval

lemma example_empty_rights_ok_by_eval:
  "example_empty_rights_ok"
  by eval

lemma example_wf_reduce_by_eval:
  "reduce_rights_wf {ZX_RIGHT_WRITE}
     {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}
   = {ZX_RIGHT_READ, ZX_RIGHT_WRITE}"
  by eval

export_code
  empty_state init_process
  create_channel_pair create_vmo
  zx_channel_write zx_channel_read
  transfer_via_channel vmo_write vmo_content lookup_handle
  zx_handle_duplicate zx_handle_close
  example_setup example_rights_a example_channel_rights
  example_exec_ok example_empty_exec_ok
  example_scenario example_empty_rights_ok
  in OCaml module_name Zircon file \<open>generated/Zircon.ml\<close>

test_code "example_exec_ok" in OCaml
test_code "example_empty_exec_ok" in OCaml

end
