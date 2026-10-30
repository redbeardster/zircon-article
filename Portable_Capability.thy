section \<open>Переносимый интерфейс attenuation capability\<close>

theory Portable_Capability
  imports Main
begin

text \<open>
  Абстрактный интерфейс \<^emph>\<open>монотонного сокращения\<close> (attenuation)
  capability-масок с опциональным замыканием зависимостей. Инстанцирование
  locale (с конкретным порядком @{text le}, операциями сокращения и
  замыкания и предикатом корректности) даёт
  @{text reduce_wf_le_old} бесплатно.

  Это \<^emph>\<open>не\<close> универсальный каркас контроля доступа: ACL/DAC, RBAC,
  information-flow, полный seL4 CSpace (mint/badge/деревья revoke) и
  concurrent-ядра требуют собственных моделей.
\<close>

locale portable_capability =
  fixes reduce :: "'r \<Rightarrow> 'r \<Rightarrow> 'r"
    and close  :: "'r \<Rightarrow> 'r"
    and wf     :: "'r \<Rightarrow> bool"
    and le     :: "'r \<Rightarrow> 'r \<Rightarrow> bool"  (infix "\<sqsubseteq>" 50)
  assumes reduce_le_old:
    "reduce r s \<sqsubseteq> s"
  assumes reduce_greatest:
    "c \<sqsubseteq> r \<Longrightarrow> c \<sqsubseteq> s \<Longrightarrow> c \<sqsubseteq> reduce r s"
  assumes close_idem:
    "close (close r) = close r"
  assumes close_infl:
    "r \<sqsubseteq> close r"
  assumes close_mono:
    "r \<sqsubseteq> s \<Longrightarrow> close r \<sqsubseteq> close s"
  assumes close_fix_wf:
    "wf r \<longleftrightarrow> close r = r"
begin

definition reduce_wf :: "'r \<Rightarrow> 'r \<Rightarrow> 'r" where
  "reduce_wf req src = close (reduce req src)"

lemma reduce_wf_le_old:
  assumes "wf src"
  shows "reduce_wf req src \<sqsubseteq> src"
proof -
  have "reduce req src \<sqsubseteq> src"
    by (rule reduce_le_old)
  hence "close (reduce req src) \<sqsubseteq> close src"
    by (rule close_mono)
  moreover have "close src = src"
    using assms by (simp add: close_fix_wf)
  ultimately show ?thesis
    unfolding reduce_wf_def by simp
qed

end

end
