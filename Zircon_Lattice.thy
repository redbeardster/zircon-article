section \<open>Алгебраическая структура прав: решётка\<close>

theory Zircon_Lattice
imports
  Zircon
  Portable_Capability
begin

text \<open>
  Тип @{typ rights} (= @{typ "right set"}) уже несёт дистрибутивную
  решёточную структуру из @{text Main}: встреча @{const inf} совпадает с
  пересечением, соединение @{const sup}~--- с объединением, порядок
  @{text "\<le>"}~--- с @{text "\<subseteq>"}. Мы \<^emph>\<open>не\<close> вводим отдельный
  @{text instantiation} для type synonym (это ни возможно, ни нужно).
  Вместо этого связываем @{const reduce_rights} с законами решётки и
  показываем, что security-свойства модели~--- их частные случаи.
\<close>

subsection \<open>Сокращение прав как встреча решётки\<close>

lemma reduce_rights_eq_inf:
  "reduce_rights new_rights old_rights = inf new_rights old_rights"
  by (simp add: reduce_rights_def)

text \<open>
  Следовательно @{const reduce_rights} наследует коммутативность,
  ассоциативность, идемпотентность и поглощение из класса @{class lattice}.
\<close>

lemma reduce_rights_commute:
  "reduce_rights A B = reduce_rights B A"
  by (simp add: reduce_rights_eq_inf inf_commute)

lemma reduce_rights_assoc:
  "reduce_rights A (reduce_rights B C) = reduce_rights (reduce_rights A B) C"
  by (simp add: reduce_rights_eq_inf inf_assoc)

lemma reduce_rights_idem:
  "reduce_rights A A = A"
  by (simp add: reduce_rights_eq_inf)

text \<open>
  Ранее доказанная @{text reduce_rights_compose}~--- это ассоциативность
  встречи:
  @{term "reduce_rights R1 (reduce_rights R2 R) = inf (inf R1 R2) R"}.
\<close>

lemma reduce_rights_assoc_via_lattice:
  "reduce_rights R1 (reduce_rights R2 R) = reduce_rights (inf R1 R2) R"
  by (simp add: reduce_rights_eq_inf inf_assoc)

subsection \<open>Частичный порядок и отсутствие эскалации\<close>

text \<open>
  Порядок на правах: @{term "A \<le> B"} означает @{term "A \<subseteq> B"}. Пустое
  множество~--- нижний элемент; @{term "UNIV :: rights"}~--- верхний
  (полное множество атомарных флагов типа @{typ right} в этой модели).
\<close>

lemma reduce_rights_le_old:
  "reduce_rights new_rights old_rights \<le> old_rights"
  by (simp add: reduce_rights_eq_inf)

lemma reduce_rights_le_new:
  "reduce_rights new_rights old_rights \<le> new_rights"
  by (simp add: reduce_rights_eq_inf)

text \<open>
  Встреча~--- наибольшая нижняя грань: любое множество прав, лежащее ниже
  и запроса, и источника, лежит ниже результата сокращения.
\<close>

lemma reduce_rights_greatest:
  assumes "C \<le> new_rights" "C \<le> old_rights"
  shows "C \<le> reduce_rights new_rights old_rights"
  using assms by (simp add: reduce_rights_eq_inf)

text \<open>
  \<^bold>\<open>Отсутствие эскалации как закон решётки.\<close>
  Получатель не может обрести право, отсутствующее у источника: это
  @{thm reduce_rights_le_old}.
\<close>

lemma no_escalation_via_meet:
  "\<not>(\<exists>r. r \<in> reduce_rights req src \<and> r \<notin> src)"
  using reduce_rights_le_old[of req src] by (auto simp: reduce_rights_def)

subsection \<open>Монотонность по правам отправителя\<close>

text \<open>
  Расширение прав отправителя (в смысле @{text "\<le>"}) не может сузить
  встречу с фиксированным запросом. Это монотонность @{const inf} по одному
  аргументу.
\<close>

lemma reduce_rights_mono_old:
  assumes "old_rights \<le> old_rights'"
  shows "reduce_rights req old_rights \<le> reduce_rights req old_rights'"
  using assms by (auto simp: reduce_rights_eq_inf)

lemma transfer_rights_eq_meet:
  assumes "transfer_via_channel src dst src_ch dst_ch pay_hid req_rights s =
             Some (hid', s')"
  assumes "lookup_handle src pay_hid s = Some h_src"
  assumes "lookup_handle dst hid' s' = Some h_dst"
  shows "h_rights h_dst = reduce_rights_wf req_rights (h_rights h_src)"
  using transfer_via_channel_cap[OF assms(1,2)] assms(3)
  by simp

text \<open>
  Отсюда no-escalation при передаче следует из @{thm reduce_rights_wf_le_old}
  при корректной маске источника (на достижимых состояниях её даёт
  @{text state_wf}):
\<close>

theorem channel_transfer_no_escalation_via_lattice:
  assumes "transfer_via_channel src dst src_ch dst_ch pay_hid req_rights s =
             Some (hid', s')"
  assumes "lookup_handle src pay_hid s = Some h_src"
  assumes "lookup_handle dst hid' s' = Some h_dst"
  assumes "rights_wf (h_rights h_src)"
  shows "h_rights h_dst \<le> h_rights h_src"
  using transfer_via_channel_no_escalation[OF assms] by (simp add: less_eq_set_def)

theorem channel_transfer_respects_request_via_lattice:
  assumes "transfer_via_channel src dst src_ch dst_ch pay_hid req_rights s =
             Some (hid', s')"
  assumes "lookup_handle src pay_hid s = Some h_src"
  assumes "lookup_handle dst hid' s' = Some h_dst"
  shows "h_rights h_dst \<le> close_rights req_rights"
  using transfer_rights_eq_meet[OF assms]
  by (auto simp: reduce_rights_wf_def close_rights_def reduce_rights_def)

subsection \<open>Алгебраическая проверка учебного сценария\<close>

text \<open>
  Для @{term "R_src = {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}"} и
  @{term "R_req = {ZX_RIGHT_READ}"} встреча равна @{term "{ZX_RIGHT_READ}"},
  что одновременно:
  \<^item> @{text "\<le>"} прав источника (нет эскалации);
  \<^item> @{text "\<le>"} запроса (не выше запрошенного);
  \<^item> наибольшая нижняя грань обоих ограничений.
\<close>

lemma example_meet_computation:
  "reduce_rights {ZX_RIGHT_READ}
      {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER} = {ZX_RIGHT_READ}"
  by (simp add: reduce_rights_def)

lemma example_meet_is_glb:
  "reduce_rights {ZX_RIGHT_READ}
      {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}
   = inf {ZX_RIGHT_READ} {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}"
  by (simp add: reduce_rights_eq_inf)

lemma example_no_escalation_algebraically:
  "reduce_rights {ZX_RIGHT_READ}
      {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}
   \<le> {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}"
  by (simp add: reduce_rights_eq_inf)

subsection \<open>Соединение: агрегация прав\<close>

text \<open>
  Соединение (join) на правах~--- объединение / @{const sup}. Оно моделирует
  агрегацию (наследование, слияние пространств имён): результат~--- верхняя
  грань обоих аргументов. В отличие от встречи, join \<^emph>\<open>не\<close> является
  операцией no-escalation относительно одного родителя~--- он может внести
  права из другого операнда.
\<close>

definition combine_rights :: "rights \<Rightarrow> rights \<Rightarrow> rights" where
  "combine_rights A B = (A \<union> B)"

lemma combine_rights_eq_sup:
  "combine_rights A B = (sup A B :: rights)"
  by (simp add: combine_rights_def)

lemma combine_rights_ge_left:
  "A \<le> combine_rights A B"
  by (simp add: combine_rights_eq_sup)

lemma combine_rights_ge_right:
  "B \<le> combine_rights A B"
  by (simp add: combine_rights_eq_sup)

lemma combine_rights_least:
  assumes "A \<le> C" "B \<le> C"
  shows "combine_rights A B \<le> C"
  using assms by (simp add: combine_rights_eq_sup)

text \<open>
  Двойственное security-прочтение: join может превзойти любого из родителей,
  поэтому агрегации нужна явная политика; закон no-escalation в стиле meet
  на неё не переносится.
\<close>

lemma reduce_rights_distrib_join:
  "reduce_rights (combine_rights A B) C =
     combine_rights (reduce_rights A C) (reduce_rights B C)"
  unfolding reduce_rights_def combine_rights_def by blast

lemma reduce_rights_distrib_join_via_lattice:
  "reduce_rights (sup A B) C = (sup (reduce_rights A C) (reduce_rights B C) :: rights)"
  by (metis combine_rights_eq_sup reduce_rights_distrib_join reduce_rights_eq_inf
            inf_sup_distrib2)

lemma combine_may_exceed_left:
  "\<not> (combine_rights {} {ZX_RIGHT_READ} \<le> {})"
  by (simp add: combine_rights_def)

subsection \<open>Зависимые права и корректные маски\<close>

text \<open>
  Определения @{const rights_wf}, @{const close_rights} и
  @{const reduce_rights_wf} введены в основной теории модели и используются
  @{const zx_channel_write}. Здесь фиксируем алгебраические факты и контраст
  с сырой встречей.
\<close>

lemma reduce_rights_may_break_wf:
  "rights_wf {ZX_RIGHT_READ, ZX_RIGHT_WRITE} \<and>
   \<not> rights_wf (reduce_rights {ZX_RIGHT_WRITE}
        {ZX_RIGHT_READ, ZX_RIGHT_WRITE})"
  by (simp add: rights_wf_def reduce_rights_def)

lemma reduce_rights_wf_le_old_order:
  assumes "rights_wf src"
  shows "reduce_rights_wf req src \<le> src"
  using reduce_rights_wf_le_old[OF assms] by (simp add: less_eq_set_def)

lemma no_escalation_via_wf_reduce:
  assumes "rights_wf src"
  shows "\<not>(\<exists>r. r \<in> reduce_rights_wf req src \<and> r \<notin> src)"
  using reduce_rights_wf_le_old[OF assms] by blast

lemma combine_rights_wf:
  assumes "rights_wf A" "rights_wf B"
  shows "rights_wf (combine_rights A B)"
  using assms by (auto simp: rights_wf_def combine_rights_def)

lemma example_wf_reduce_write_request:
  "reduce_rights_wf {ZX_RIGHT_WRITE}
      {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}
   = {ZX_RIGHT_READ, ZX_RIGHT_WRITE}"
  by (simp add: reduce_rights_wf_def close_rights_def reduce_rights_def)

subsection \<open>Zircon как экземпляр @{locale portable_capability}\<close>

text \<open>
  Учебный фрагмент Zircon интерпретирует portable attenuation locale:
  порядок~--- @{text "(\<subseteq>)"}, @{const reduce_rights}~--- встреча,
  @{const close_rights}~--- замыкание зависимостей, @{const rights_wf}~---
  предикат неподвижных точек. Ключевая лемма
  @{thm portable_capability.reduce_wf_le_old} специализируется до
  @{thm reduce_rights_wf_le_old}.
\<close>

interpretation zircon_portable:
  portable_capability reduce_rights close_rights rights_wf "(\<subseteq>)"
proof
  fix r s :: rights
  show "reduce_rights r s \<subseteq> s"
    by (rule reduce_rights_le_old)
next
  fix c r s :: rights
  assume "c \<subseteq> r" "c \<subseteq> s"
  then show "c \<subseteq> reduce_rights r s"
    by (rule reduce_rights_greatest)
next
  fix r :: rights
  show "close_rights (close_rights r) = close_rights r"
    by (rule close_rights_idem)
next
  fix r :: rights
  show "r \<subseteq> close_rights r"
    by (rule close_rights_infl)
next
  fix r s :: rights
  assume "r \<subseteq> s"
  then show "close_rights r \<subseteq> close_rights s"
    by (rule close_rights_mono)
next
  fix r :: rights
  show "rights_wf r \<longleftrightarrow> close_rights r = r"
    by (rule close_rights_fix_wf)
qed

lemma zircon_portable_reduce_wf_eq:
  "zircon_portable.reduce_wf req src = reduce_rights_wf req src"
  by (simp add: zircon_portable.reduce_wf_def reduce_rights_wf_def)

lemma reduce_rights_wf_le_old_via_locale:
  assumes "rights_wf src"
  shows "reduce_rights_wf req src \<subseteq> src"
  using zircon_portable.reduce_wf_le_old[OF assms]
  by (simp add: zircon_portable_reduce_wf_eq)

end
