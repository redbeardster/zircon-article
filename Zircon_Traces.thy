section \<open>Достижимость и трассовые инварианты\<close>

theory Zircon_Traces
imports
  Zircon
begin

text \<open>
  Размеченные переходы оборачивают syscall'ы модели; достижимость~--- их
  рефлексивно-транзитивное замыкание. Инвариант @{text state_wf} состоит из
  трёх частей: у каждого handle и каждой capability «в полёте» корректная
  маска прав (@{text handles_wf}, @{text channels_caps_wf}) и связь концов
  канала симметрична с существующими очередями (@{text peers_wf}). Он
  сохраняется каждым успешным шагом и, следовательно, любой конечной трассой.

  Именно отсюда пошаговые леммы no-escalation получают посылку
  @{const rights_wf} источника: syscall'ы её не проверяют (как и Zircon),
  но на достижимых состояниях она верна.
\<close>

subsection \<open>Метки и одношаговое исполнение\<close>

datatype step =
    Create_VMO "process_id" "rights" "nat"
  | Create_Channel "process_id" "process_id" "rights" "rights"
  | Channel_Write "process_id" "handle_id" "handle_id" "rights"
  | Channel_Read "process_id" "handle_id"
  | Transfer "process_id" "process_id" "handle_id" "handle_id" "handle_id" "rights"
  | Vmo_Write "process_id" "handle_id" "nat"
  | Duplicate "process_id" "handle_id" "rights"
  | Close "process_id" "handle_id"

fun exec_step :: "step \<Rightarrow> system_state \<Rightarrow> system_state option" where
  "exec_step (Create_VMO pid rs content) s =
     (case create_vmo pid rs content s of
        None \<Rightarrow> None
      | Some (_, _, s') \<Rightarrow> Some s')"
| "exec_step (Create_Channel p0 p1 r0 r1) s =
     (case create_channel_pair p0 p1 r0 r1 s of
        None \<Rightarrow> None
      | Some (_, _, _, s') \<Rightarrow> Some s')"
| "exec_step (Channel_Write pid ch pay req) s =
     zx_channel_write pid ch pay req s"
| "exec_step (Channel_Read pid ch) s =
     (case zx_channel_read pid ch s of
        None \<Rightarrow> None
      | Some (_, s') \<Rightarrow> Some s')"
| "exec_step (Transfer src dst sch dch pay req) s =
     (case transfer_via_channel src dst sch dch pay req s of
        None \<Rightarrow> None
      | Some (_, s') \<Rightarrow> Some s')"
| "exec_step (Vmo_Write pid hid content) s =
     vmo_write pid hid content s"
| "exec_step (Duplicate pid hid req) s =
     (case zx_handle_duplicate pid hid req s of
        None \<Rightarrow> None
      | Some (_, s') \<Rightarrow> Some s')"
| "exec_step (Close pid hid) s =
     zx_handle_close pid hid s"

inductive reachable :: "system_state \<Rightarrow> system_state \<Rightarrow> bool" where
  refl: "reachable s s"
| step: "reachable s s1 \<Longrightarrow> exec_step st s1 = Some s2 \<Longrightarrow> reachable s s2"

text \<open>Последовательное исполнение списка меток; успех всего списка даёт достижимость.\<close>

fun run_steps :: "step list \<Rightarrow> system_state \<Rightarrow> system_state option" where
  "run_steps [] s = Some s"
| "run_steps (st # sts) s =
     (case exec_step st s of
        None \<Rightarrow> None
      | Some s1 \<Rightarrow> run_steps sts s1)"

lemma reachable_trans:
  assumes "reachable s s1" "reachable s1 s2"
  shows "reachable s s2"
  using assms(2,1)
proof (induction rule: reachable.induct)
  case (refl t)
  then show ?case .
next
  case (step t t1 st t2)
  from step.IH[OF step.prems] have "reachable s t1" .
  from reachable.step[OF this step.hyps(2)] show ?case .
qed

lemma run_steps_reachable:
  assumes "run_steps sts s = Some s'"
  shows "reachable s s'"
  using assms
proof (induction sts arbitrary: s)
  case Nil
  then show ?case by (simp add: reachable.refl)
next
  case (Cons st sts)
  from Cons.prems obtain s1 where
    ex: "exec_step st s = Some s1" and rest: "run_steps sts s1 = Some s'"
    by (auto split: option.splits)
  have "reachable s s1"
    using reachable.step[OF reachable.refl ex] .
  from reachable_trans[OF this Cons.IH[OF rest]] show ?case .
qed

subsection \<open>Корректные состояния\<close>

definition handles_wf :: "system_state \<Rightarrow> bool" where
  "handles_wf s \<longleftrightarrow>
     (\<forall>pid ht hid h.
        proc_tables s pid = Some ht \<longrightarrow> ht hid = Some h \<longrightarrow>
        rights_wf (h_rights h))"

definition channels_caps_wf :: "system_state \<Rightarrow> bool" where
  "channels_caps_wf s \<longleftrightarrow>
     (\<forall>oid q cap.
        channels s oid = Some q \<longrightarrow> cap \<in> set q \<longrightarrow>
        rights_wf (h_rights cap))"

text \<open>
  Связь концов канала: отношение @{text channel_peer} симметрично, у обоих
  концов есть очереди, и все упомянутые id уже выделены (ниже
  @{text next_obj_id}). Последнее нужно, чтобы свежая пара endpoint'ов не
  могла перезаписать чужую связь. Это Zircon-утверждение «сообщение попадает
  к противоположному концу, и у него есть очередь», доказанное как инвариант
  трассы, а не только обеспеченное конструкцией @{const create_channel_pair}.
\<close>

definition peers_wf :: "system_state \<Rightarrow> bool" where
  "peers_wf s \<longleftrightarrow>
     (\<forall>a b. channel_peer s a = Some b \<longrightarrow>
        channel_peer s b = Some a \<and>
        channels s a \<noteq> None \<and> channels s b \<noteq> None \<and>
        a < next_obj_id s \<and> b < next_obj_id s)"

definition state_wf :: "system_state \<Rightarrow> bool" where
  "state_wf s \<longleftrightarrow> handles_wf s \<and> channels_caps_wf s \<and> peers_wf s"

lemma state_wfE:
  assumes "state_wf s"
  obtains "handles_wf s" "channels_caps_wf s" "peers_wf s"
  using assms by (simp add: state_wf_def)

lemma state_wfI:
  assumes "handles_wf s" "channels_caps_wf s" "peers_wf s"
  shows "state_wf s"
  using assms by (simp add: state_wf_def)

text \<open>
  \<^emph>\<open>Техническое замечание.\<close> Раскрытое @{const peers_wf} даёт симметричное
  условное правило @{text "channel_peer s a = Some b \<Longrightarrow> channel_peer s b = Some a"};
  если отдать его симплификатору вместе с посылкой @{text "peers_wf s"},
  @{text simp}/@{text auto} зацикливаются. Поэтому факты из инварианта
  извлекаем только деструктором @{text peers_wfD} (через @{text blast}), а
  сохранение доказываем через конгруэнцию @{text peers_wf_cong}.
\<close>

lemma peers_wfD:
  assumes "peers_wf s" "channel_peer s a = Some b"
  shows "channel_peer s b = Some a"
    and "channels s a \<noteq> None" and "channels s b \<noteq> None"
    and "a < next_obj_id s" and "b < next_obj_id s"
  using assms unfolding peers_wf_def by blast+

lemma peer_symmetric:
  assumes "peers_wf s" "channel_peer s a = Some b"
  shows "channel_peer s b = Some a"
  by (rule peers_wfD[OF assms])

lemma peers_wfI:
  assumes "\<And>a b. channel_peer s a = Some b \<Longrightarrow>
             channel_peer s b = Some a \<and>
             channels s a \<noteq> None \<and> channels s b \<noteq> None \<and>
             a < next_obj_id s \<and> b < next_obj_id s"
  shows "peers_wf s"
  using assms unfolding peers_wf_def by blast

text \<open>
  Конгруэнция: если связь концов не менялась, очереди не исчезали и счётчик
  объектов не убывал, инвариант пиров переносится на новое состояние.
\<close>

lemma peers_wf_cong:
  assumes pw: "peers_wf s"
  assumes cp: "channel_peer s' = channel_peer s"
  assumes ch: "\<And>a. channels s a \<noteq> None \<Longrightarrow> channels s' a \<noteq> None"
  assumes no: "next_obj_id s \<le> next_obj_id s'"
  shows "peers_wf s'"
proof (rule peers_wfI)
  fix a b assume "channel_peer s' a = Some b"
  with cp have ab: "channel_peer s a = Some b" by simp
  from peers_wfD[OF pw ab]
  have sym: "channel_peer s b = Some a" and
       qa: "channels s a \<noteq> None" and qb: "channels s b \<noteq> None" and
       la: "a < next_obj_id s" and lb: "b < next_obj_id s" .
  from la no have la': "a < next_obj_id s'" by (rule less_le_trans)
  from lb no have lb': "b < next_obj_id s'" by (rule less_le_trans)
  from sym cp ch[OF qa] ch[OF qb] la' lb'
  show "channel_peer s' b = Some a \<and>
        channels s' a \<noteq> None \<and> channels s' b \<noteq> None \<and>
        a < next_obj_id s' \<and> b < next_obj_id s'"
    by simp
qed

lemma handles_wf_lookup:
  assumes "handles_wf s" "lookup_handle pid hid s = Some h"
  shows "rights_wf (h_rights h)"
  using assms by (auto simp: handles_wf_def lookup_handle_def split: option.splits)

lemma empty_state_wf:
  "state_wf empty_state"
  by (simp add: state_wf_def handles_wf_def channels_caps_wf_def peers_wf_def
                empty_state_def)

lemma init_process_preserves_wf:
  assumes "state_wf s"
  shows "state_wf (init_process pid s)"
  using assms(1)
proof (rule state_wfE)
  assume h: "handles_wf s" and c: "channels_caps_wf s" and p: "peers_wf s"
  have "handles_wf (init_process pid s)"
    using h by (auto simp: handles_wf_def init_process_def)
  moreover have "channels_caps_wf (init_process pid s)"
    using c by (simp add: channels_caps_wf_def init_process_def)
  moreover have "peers_wf (init_process pid s)"
    by (rule peers_wf_cong[OF p]) (simp_all add: init_process_def)
  ultimately show ?thesis by (rule state_wfI)
qed

subsection \<open>Сохранение на одном шаге\<close>

text \<open>
  Каждую из трёх компонент @{const state_wf} доказываем отдельно: так
  расщепление гипотезы о syscall'е не умножается на три
  универсально-квантифицированные цели. Для @{const peers_wf} используем
  только @{thm peers_wf_cong}: от syscall'а требуются три селекторных факта.
\<close>

paragraph \<open>create\_vmo\<close>

lemma create_vmo_handles_wf:
  assumes "handles_wf s" "create_vmo pid rs content s = Some (hid, oid, s')"
  shows "handles_wf s'"
  using assms
  by (auto simp: handles_wf_def create_vmo_def set_table_def alloc_hid_def
                 get_table_def Let_def
           split: option.splits prod.splits if_splits)

lemma create_vmo_channels_caps_wf:
  assumes "channels_caps_wf s" "create_vmo pid rs content s = Some (hid, oid, s')"
  shows "channels_caps_wf s'"
  using assms
  by (auto simp: channels_caps_wf_def create_vmo_def set_table_def alloc_hid_def
                 get_table_def Let_def
           split: option.splits prod.splits if_splits)

lemma create_vmo_peers_wf:
  assumes "peers_wf s" "create_vmo pid rs content s = Some (hid, oid, s')"
  shows "peers_wf s'"
proof (rule peers_wf_cong[OF assms(1)])
  show "channel_peer s' = channel_peer s"
    using assms(2)
    by (auto simp: create_vmo_def set_table_def alloc_hid_def get_table_def Let_def
             split: option.splits prod.splits if_splits)
  show "\<And>a. channels s a \<noteq> None \<Longrightarrow> channels s' a \<noteq> None"
    using assms(2)
    by (auto simp: create_vmo_def set_table_def alloc_hid_def get_table_def Let_def
             split: option.splits prod.splits if_splits)
  show "next_obj_id s \<le> next_obj_id s'"
    using assms(2)
    by (auto simp: create_vmo_def set_table_def alloc_hid_def get_table_def Let_def
             split: option.splits prod.splits if_splits)
qed

lemma create_vmo_preserves_wf:
  assumes "state_wf s"
  assumes "create_vmo pid rs content s = Some (hid, oid, s')"
  shows "state_wf s'"
  using assms(1)
proof (rule state_wfE)
  assume h: "handles_wf s" and c: "channels_caps_wf s" and p: "peers_wf s"
  show ?thesis
    by (rule state_wfI[OF create_vmo_handles_wf[OF h assms(2)]
                          create_vmo_channels_caps_wf[OF c assms(2)]
                          create_vmo_peers_wf[OF p assms(2)]])
qed

paragraph \<open>create\_channel\_pair\<close>

lemma create_channel_pair_handles_wf:
  assumes "handles_wf s" "create_channel_pair p0 p1 r0 r1 s = Some (h0, h1, oid, s')"
  shows "handles_wf s'"
  using assms
  by (auto simp: handles_wf_def create_channel_pair_def set_table_def alloc_hid_def
                 get_table_def Let_def
           split: option.splits prod.splits if_splits)

lemma create_channel_pair_channels_caps_wf:
  assumes "channels_caps_wf s" "create_channel_pair p0 p1 r0 r1 s = Some (h0, h1, oid, s')"
  shows "channels_caps_wf s'"
  using assms
  by (auto simp: channels_caps_wf_def create_channel_pair_def set_table_def
                 alloc_hid_def get_table_def Let_def
           split: option.splits prod.splits if_splits)

text \<open>
  Свежая пара: оба новых id не меньше @{text next_obj_id}, поэтому старые
  связи не перезаписываются, а новые симметричны по построению.
\<close>

lemma peers_wf_fresh_pair:
  assumes pw: "peers_wf s"
  assumes ch: "channels s' =
                 (channels s)(next_obj_id s \<mapsto> [], Suc (next_obj_id s) \<mapsto> [])"
  assumes cp: "channel_peer s' =
                 (channel_peer s)(next_obj_id s \<mapsto> Suc (next_obj_id s),
                                  Suc (next_obj_id s) \<mapsto> next_obj_id s)"
  assumes no: "next_obj_id s' = Suc (Suc (next_obj_id s))"
  shows "peers_wf s'"
proof -
  let ?n = "next_obj_id s"
  { fix a b
    assume ab: "channel_peer s' a = Some b"
    have "channel_peer s' b = Some a \<and>
          channels s' a \<noteq> None \<and> channels s' b \<noteq> None \<and>
          a < next_obj_id s' \<and> b < next_obj_id s'"
    proof (cases "a = Suc ?n")
      case True
      with ab cp show ?thesis by (simp add: ch no)
    next
      case neq1: False
      show ?thesis
      proof (cases "a = ?n")
        case True
        with ab cp neq1 show ?thesis by (simp add: ch no)
      next
        case False
        with ab cp neq1 have old: "channel_peer s a = Some b" by simp
        from peers_wfD[OF pw old] have
          sym: "channel_peer s b = Some a" and
          qa: "channels s a \<noteq> None" and qb: "channels s b \<noteq> None" and
          la: "a < ?n" and lb: "b < ?n" .
        from lb have nb: "b \<noteq> ?n" "b \<noteq> Suc ?n" by auto
        from sym qa qb la lb nb neq1 False show ?thesis
          by (simp add: ch cp no)
      qed
    qed
  }
  then show ?thesis by (rule peers_wfI)
qed

text \<open>Три селекторных равенства извлекаются из определения по отдельности.\<close>

lemma create_channel_pair_channels:
  assumes "create_channel_pair p0 p1 r0 r1 s = Some (h0, h1, oid, s')"
  shows "channels s' = (channels s)(next_obj_id s \<mapsto> [], Suc (next_obj_id s) \<mapsto> [])"
  using assms
  by (auto simp: create_channel_pair_def Let_def alloc_hid_def set_table_def
                 get_table_def
           split: option.splits prod.splits if_splits)

lemma create_channel_pair_peer:
  assumes "create_channel_pair p0 p1 r0 r1 s = Some (h0, h1, oid, s')"
  shows "channel_peer s' = (channel_peer s)(next_obj_id s \<mapsto> Suc (next_obj_id s),
                                            Suc (next_obj_id s) \<mapsto> next_obj_id s)"
  using assms
  by (auto simp: create_channel_pair_def Let_def alloc_hid_def set_table_def
                 get_table_def
           split: option.splits prod.splits if_splits)

lemma create_channel_pair_next_obj_id:
  assumes "create_channel_pair p0 p1 r0 r1 s = Some (h0, h1, oid, s')"
  shows "next_obj_id s' = Suc (Suc (next_obj_id s))"
  using assms
  by (auto simp: create_channel_pair_def Let_def alloc_hid_def set_table_def
                 get_table_def
           split: option.splits prod.splits if_splits)

lemma create_channel_pair_peers_wf:
  assumes "peers_wf s" "create_channel_pair p0 p1 r0 r1 s = Some (h0, h1, oid, s')"
  shows "peers_wf s'"
  by (rule peers_wf_fresh_pair[OF assms(1)
        create_channel_pair_channels[OF assms(2)]
        create_channel_pair_peer[OF assms(2)]
        create_channel_pair_next_obj_id[OF assms(2)]])

lemma create_channel_pair_preserves_wf:
  assumes "state_wf s"
  assumes "create_channel_pair p0 p1 r0 r1 s = Some (h0, h1, oid, s')"
  shows "state_wf s'"
  using assms(1)
proof (rule state_wfE)
  assume h: "handles_wf s" and c: "channels_caps_wf s" and p: "peers_wf s"
  show ?thesis
    by (rule state_wfI[OF create_channel_pair_handles_wf[OF h assms(2)]
                          create_channel_pair_channels_caps_wf[OF c assms(2)]
                          create_channel_pair_peers_wf[OF p assms(2)]])
qed

paragraph \<open>zx\_channel\_write\<close>

lemma zx_channel_write_handles_wf:
  assumes "handles_wf s" "zx_channel_write pid ch pay req s = Some s'"
  shows "handles_wf s'"
  using assms
  by (auto simp: handles_wf_def zx_channel_write_def set_table_def get_table_def
                 lookup_handle_def Let_def
           split: option.splits if_splits)

lemma zx_channel_write_channels_caps_wf:
  assumes "channels_caps_wf s" "zx_channel_write pid ch pay req s = Some s'"
  shows "channels_caps_wf s'"
  using assms
  by (auto simp: channels_caps_wf_def zx_channel_write_def set_table_def get_table_def
                 lookup_handle_def reduce_rights_wf_wf Let_def
           split: option.splits if_splits)

lemma zx_channel_write_peers_wf:
  assumes "peers_wf s" "zx_channel_write pid ch pay req s = Some s'"
  shows "peers_wf s'"
proof (rule peers_wf_cong[OF assms(1)])
  show "channel_peer s' = channel_peer s"
    using assms(2)
    by (auto simp: zx_channel_write_def set_table_def get_table_def lookup_handle_def
                   Let_def
             split: option.splits if_splits)
  show "\<And>a. channels s a \<noteq> None \<Longrightarrow> channels s' a \<noteq> None"
    using assms(2)
    by (auto simp: zx_channel_write_def set_table_def get_table_def lookup_handle_def
                   Let_def
             split: option.splits if_splits)
  show "next_obj_id s \<le> next_obj_id s'"
    using assms(2)
    by (auto simp: zx_channel_write_def set_table_def get_table_def lookup_handle_def
                   Let_def
             split: option.splits if_splits)
qed

lemma zx_channel_write_preserves_wf:
  assumes "state_wf s"
  assumes "zx_channel_write pid ch pay req s = Some s'"
  shows "state_wf s'"
  using assms(1)
proof (rule state_wfE)
  assume h: "handles_wf s" and c: "channels_caps_wf s" and p: "peers_wf s"
  show ?thesis
    by (rule state_wfI[OF zx_channel_write_handles_wf[OF h assms(2)]
                          zx_channel_write_channels_caps_wf[OF c assms(2)]
                          zx_channel_write_peers_wf[OF p assms(2)]])
qed

paragraph \<open>zx\_channel\_read\<close>

text \<open>Новый handle получателя берётся из очереди, поэтому нужна корректность очередей.\<close>

lemma zx_channel_read_handles_wf:
  assumes "handles_wf s" "channels_caps_wf s"
  assumes "zx_channel_read pid ch s = Some (hid', s')"
  shows "handles_wf s'"
  using assms
  by (auto simp: handles_wf_def channels_caps_wf_def zx_channel_read_def
                 set_table_def get_table_def lookup_handle_def alloc_hid_def Let_def
           split: option.splits list.splits if_splits prod.splits)

lemma zx_channel_read_channels_caps_wf:
  assumes "channels_caps_wf s" "zx_channel_read pid ch s = Some (hid', s')"
  shows "channels_caps_wf s'"
  using assms
  by (auto simp: channels_caps_wf_def zx_channel_read_def
                 set_table_def get_table_def lookup_handle_def alloc_hid_def Let_def
           split: option.splits list.splits if_splits prod.splits)

lemma zx_channel_read_peers_wf:
  assumes "peers_wf s" "zx_channel_read pid ch s = Some (hid', s')"
  shows "peers_wf s'"
proof (rule peers_wf_cong[OF assms(1)])
  show "channel_peer s' = channel_peer s"
    using assms(2)
    by (auto simp: zx_channel_read_def set_table_def get_table_def lookup_handle_def
                   alloc_hid_def Let_def
             split: option.splits list.splits if_splits prod.splits)
  show "\<And>a. channels s a \<noteq> None \<Longrightarrow> channels s' a \<noteq> None"
    using assms(2)
    by (auto simp: zx_channel_read_def set_table_def get_table_def lookup_handle_def
                   alloc_hid_def Let_def
             split: option.splits list.splits if_splits prod.splits)
  show "next_obj_id s \<le> next_obj_id s'"
    using assms(2)
    by (auto simp: zx_channel_read_def set_table_def get_table_def lookup_handle_def
                   alloc_hid_def Let_def
             split: option.splits list.splits if_splits prod.splits)
qed

lemma zx_channel_read_preserves_wf:
  assumes "state_wf s"
  assumes "zx_channel_read pid ch s = Some (hid', s')"
  shows "state_wf s'"
  using assms(1)
proof (rule state_wfE)
  assume h: "handles_wf s" and c: "channels_caps_wf s" and p: "peers_wf s"
  show ?thesis
    by (rule state_wfI[OF zx_channel_read_handles_wf[OF h c assms(2)]
                          zx_channel_read_channels_caps_wf[OF c assms(2)]
                          zx_channel_read_peers_wf[OF p assms(2)]])
qed

paragraph \<open>zx\_handle\_duplicate и zx\_handle\_close\<close>

lemma zx_handle_duplicate_handles_wf:
  assumes "handles_wf s" "zx_handle_duplicate pid hid req s = Some (hid', s')"
  shows "handles_wf s'"
  using assms
  by (auto simp: handles_wf_def zx_handle_duplicate_def set_table_def get_table_def
                 lookup_handle_def alloc_hid_def reduce_rights_wf_wf Let_def
           split: option.splits if_splits prod.splits)

text \<open>Duplicate и close трогают только таблицу handles.\<close>

lemma zx_handle_duplicate_fields:
  assumes "zx_handle_duplicate pid hid req s = Some (hid', s')"
  shows "channels s' = channels s" "channel_peer s' = channel_peer s"
    and "next_obj_id s' = next_obj_id s"
  using assms
  by (auto simp: zx_handle_duplicate_def set_table_def get_table_def
                 lookup_handle_def alloc_hid_def Let_def
           split: option.splits if_splits prod.splits)

lemma zx_handle_duplicate_preserves_wf:
  assumes "state_wf s"
  assumes dup: "zx_handle_duplicate pid hid req s = Some (hid', s')"
  shows "state_wf s'"
  using assms(1)
proof (rule state_wfE)
  assume h: "handles_wf s" and c: "channels_caps_wf s" and p: "peers_wf s"
  have "channels_caps_wf s'"
    using c by (simp add: channels_caps_wf_def zx_handle_duplicate_fields[OF dup])
  moreover have "peers_wf s'"
    by (rule peers_wf_cong[OF p]) (simp_all add: zx_handle_duplicate_fields[OF dup])
  ultimately show ?thesis
    using zx_handle_duplicate_handles_wf[OF h dup] by (intro state_wfI)
qed

lemma zx_handle_close_handles_wf:
  assumes "handles_wf s" "zx_handle_close pid hid s = Some s'"
  shows "handles_wf s'"
  using assms
  by (auto simp: handles_wf_def zx_handle_close_def set_table_def get_table_def
                 lookup_handle_def
           split: option.splits if_splits)

lemma zx_handle_close_fields:
  assumes "zx_handle_close pid hid s = Some s'"
  shows "channels s' = channels s" "channel_peer s' = channel_peer s"
    and "next_obj_id s' = next_obj_id s"
  using assms
  by (auto simp: zx_handle_close_def set_table_def get_table_def lookup_handle_def
           split: option.splits)

lemma zx_handle_close_preserves_wf:
  assumes "state_wf s"
  assumes cl: "zx_handle_close pid hid s = Some s'"
  shows "state_wf s'"
  using assms(1)
proof (rule state_wfE)
  assume h: "handles_wf s" and c: "channels_caps_wf s" and p: "peers_wf s"
  have "channels_caps_wf s'"
    using c by (simp add: channels_caps_wf_def zx_handle_close_fields[OF cl])
  moreover have "peers_wf s'"
    by (rule peers_wf_cong[OF p]) (simp_all add: zx_handle_close_fields[OF cl])
  ultimately show ?thesis
    using zx_handle_close_handles_wf[OF h cl] by (intro state_wfI)
qed

lemma transfer_preserves_wf:
  assumes "state_wf s"
  assumes "transfer_via_channel src dst sch dch pay req s = Some (hid', s')"
  shows "state_wf s'"
proof -
  from assms(2) obtain s1 where
    w: "zx_channel_write src sch pay req s = Some s1" and
    r: "zx_channel_read dst dch s1 = Some (hid', s')"
    by (auto simp: transfer_via_channel_def split: option.splits if_splits list.splits)
  from zx_channel_write_preserves_wf[OF assms(1) w] have s1wf: "state_wf s1" .
  from zx_channel_read_preserves_wf[OF s1wf r] show ?thesis .
qed

lemma vmo_write_fields:
  assumes "vmo_write pid hid content s = Some s'"
  shows "proc_tables s' = proc_tables s" "channels s' = channels s"
    and "channel_peer s' = channel_peer s" "next_obj_id s' = next_obj_id s"
  using assms by (auto simp: vmo_write_def split: option.splits if_splits)

lemma vmo_write_preserves_wf:
  assumes "state_wf s"
  assumes vw: "vmo_write pid hid content s = Some s'"
  shows "state_wf s'"
  using assms(1)
proof (rule state_wfE)
  assume h: "handles_wf s" and c: "channels_caps_wf s" and p: "peers_wf s"
  have "handles_wf s'"
    using h by (simp add: handles_wf_def vmo_write_fields[OF vw])
  moreover have "channels_caps_wf s'"
    using c by (simp add: channels_caps_wf_def vmo_write_fields[OF vw])
  moreover have "peers_wf s'"
    by (rule peers_wf_cong[OF p]) (simp_all add: vmo_write_fields[OF vw])
  ultimately show ?thesis by (rule state_wfI)
qed

lemma exec_step_preserves_wf:
  assumes "state_wf s"
  assumes "exec_step st s = Some s'"
  shows "state_wf s'"
  using assms
proof (cases st)
  case (Create_VMO pid rs content)
  with assms obtain hid oid where cv:
    "create_vmo pid rs content s = Some (hid, oid, s')"
    by (auto split: option.splits)
  from create_vmo_preserves_wf[OF assms(1) cv] show ?thesis .
next
  case (Create_Channel p0 p1 r0 r1)
  with assms obtain h0 h1 oid where cc:
    "create_channel_pair p0 p1 r0 r1 s = Some (h0, h1, oid, s')"
    by (auto split: option.splits)
  from create_channel_pair_preserves_wf[OF assms(1) cc] show ?thesis .
next
  case (Channel_Write pid ch pay req)
  with assms have "zx_channel_write pid ch pay req s = Some s'" by simp
  from zx_channel_write_preserves_wf[OF assms(1) this] show ?thesis .
next
  case (Channel_Read pid ch)
  with assms obtain hid' where
    "zx_channel_read pid ch s = Some (hid', s')"
    by (auto split: option.splits)
  from zx_channel_read_preserves_wf[OF assms(1) this] show ?thesis .
next
  case (Transfer src dst sch dch pay req)
  with assms obtain hid' where
    "transfer_via_channel src dst sch dch pay req s = Some (hid', s')"
    by (auto split: option.splits)
  from transfer_preserves_wf[OF assms(1) this] show ?thesis .
next
  case (Vmo_Write pid hid content)
  with assms have "vmo_write pid hid content s = Some s'" by simp
  from vmo_write_preserves_wf[OF assms(1) this] show ?thesis .
next
  case (Duplicate pid hid req)
  with assms obtain hid' where
    "zx_handle_duplicate pid hid req s = Some (hid', s')"
    by (auto split: option.splits)
  from zx_handle_duplicate_preserves_wf[OF assms(1) this] show ?thesis .
next
  case (Close pid hid)
  with assms have "zx_handle_close pid hid s = Some s'" by simp
  from zx_handle_close_preserves_wf[OF assms(1) this] show ?thesis .
qed

subsection \<open>Инвариант трассы\<close>

theorem reachable_preserves_wf:
  assumes "state_wf s"
  assumes "reachable s s'"
  shows "state_wf s'"
  using assms(2,1)
proof (induction arbitrary: rule: reachable.induct)
  case (refl s)
  then show ?case by simp
next
  case (step s s1 st s2)
  from step.IH[OF step.prems] have "state_wf s1" .
  from exec_step_preserves_wf[OF this step.hyps(2)] show ?case .
qed

subsection \<open>No-escalation на каждом Transfer-шаге трассы\<close>

text \<open>
  Здесь @{text state_wf} работает по существу. Пошаговая лемма
  @{thm transfer_via_channel_no_escalation} требует @{const rights_wf} у
  источника; syscall эту маску не проверяет. На достижимом из корректного
  старта состоянии её даёт @{thm reachable_preserves_wf} через
  @{text handles_wf}. Таким образом трассовая теорема --- не упаковка
  пошаговой, а то место, где закрывается её посылка.
\<close>

theorem reachable_transfer_no_escalation:
  assumes wf0: "state_wf s0"
  assumes reach: "reachable s0 s"
  assumes tr: "transfer_via_channel src dst sch dch pay req s = Some (hid', s')"
  assumes src_l: "lookup_handle src pay s = Some h_src"
  assumes dst_l: "lookup_handle dst hid' s' = Some h_dst"
  shows "h_rights h_dst \<subseteq> h_rights h_src"
proof -
  from reachable_preserves_wf[OF wf0 reach] have "handles_wf s"
    by (simp add: state_wf_def)
  from handles_wf_lookup[OF this src_l] have "rights_wf (h_rights h_src)" .
  from transfer_via_channel_no_escalation[OF tr src_l dst_l this]
  show ?thesis .
qed

text \<open>
  Та же теорема в терминах размеченного шага: успешный @{text Transfer}
  даёт handle получателя, чьи права сокращены относительно payload
  отправителя.
\<close>

theorem reachable_transfer_step_no_escalation:
  assumes wf0: "state_wf s0"
  assumes reach: "reachable s0 s"
  assumes ex: "exec_step (Transfer src dst sch dch pay req) s = Some s'"
  assumes src_l: "lookup_handle src pay s = Some h_src"
  shows "\<exists>hid' h_dst.
           transfer_via_channel src dst sch dch pay req s = Some (hid', s') \<and>
           lookup_handle dst hid' s' = Some h_dst \<and>
           h_rights h_dst \<subseteq> h_rights h_src"
proof -
  from ex obtain hid' where
    tr: "transfer_via_channel src dst sch dch pay req s = Some (hid', s')"
    by (auto split: option.splits)
  from transfer_via_channel_cap[OF tr src_l]
  have dst_lookup:
    "lookup_handle dst hid' s' =
       Some \<lparr>h_obj = h_obj h_src,
              h_rights = reduce_rights_wf req (h_rights h_src)\<rparr>" .
  let ?h_dst =
    "\<lparr>h_obj = h_obj h_src,
      h_rights = reduce_rights_wf req (h_rights h_src)\<rparr>"
  have le: "h_rights ?h_dst \<subseteq> h_rights h_src"
    by (rule reachable_transfer_no_escalation[OF wf0 reach tr src_l dst_lookup])
  from tr dst_lookup le show ?thesis
    by (rule_tac x=hid' in exI, rule_tac x="?h_dst" in exI, simp)
qed

text \<open>То же для duplicate: @{const rights_wf} источника берётся из трассы.\<close>

theorem reachable_duplicate_no_escalation:
  assumes wf0: "state_wf s0"
  assumes reach: "reachable s0 s"
  assumes dup: "zx_handle_duplicate pid hid req s = Some (hid', s')"
  assumes src_l: "lookup_handle pid hid s = Some h"
  assumes dst_l: "lookup_handle pid hid' s' = Some h'"
  shows "h_rights h' \<subseteq> h_rights h"
proof -
  from reachable_preserves_wf[OF wf0 reach] have "handles_wf s"
    by (simp add: state_wf_def)
  from handles_wf_lookup[OF this src_l] have "rights_wf (h_rights h)" .
  from zx_handle_duplicate_no_escalation[OF dup src_l dst_l this]
  show ?thesis by (simp add: less_eq_set_def)
qed

subsection \<open>Учебный сценарий как достижимая трасса\<close>

text \<open>
  Конкретная начальная точка учебных примеров: два пустых процесса.
\<close>

definition example_start :: system_state where
  "example_start = init_process 1 (init_process 0 empty_state)"

lemma example_start_wf:
  "state_wf example_start"
  by (simp add: example_start_def empty_state_wf init_process_preserves_wf)

text \<open>
  Сценарий @{const example_scenario} записан как список меток с конкретными
  id (handle'ы нумеруются с~1 в каждом процессе; канал --- объекты 0 и 1,
  VMO --- объект 2). Лемма ниже показывает, что он \<^emph>\<open>исполняется\<close> из
  @{const example_start}, а значит, итоговое состояние достижимо и, по
  @{thm reachable_preserves_wf}, корректно; при этом у получателя нет
  @{text WRITE}, а содержимое VMO не тронуто.
\<close>

definition example_steps :: "step list" where
  "example_steps =
     [Create_Channel 0 1 example_channel_rights example_channel_rights,
      Create_VMO 0 {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER} 42,
      Transfer 0 1 1 1 2 {ZX_RIGHT_READ}]"

definition example_steps_ok :: bool where
  "example_steps_ok =
    (case run_steps example_steps example_start of
       None \<Rightarrow> False
     | Some s' \<Rightarrow>
         lookup_handle 0 2 s' = None \<and>
         (case lookup_handle 1 2 s' of
            None \<Rightarrow> False
          | Some h \<Rightarrow> ZX_RIGHT_WRITE \<notin> h_rights h) \<and>
         vmo_content 2 s' = Some 42)"

lemma example_steps_ok_true:
  "example_steps_ok"
  by (simp add: example_steps_ok_def example_steps_def example_start_def
                example_channel_rights_def
                empty_state_def init_process_def create_channel_pair_def
                create_vmo_def transfer_via_channel_def zx_channel_write_def
                zx_channel_read_def alloc_hid_def set_table_def get_table_def
                lookup_handle_def reduce_rights_def reduce_rights_wf_def
                close_rights_def rights_wf_def vmo_content_def Let_def)

lemma example_steps_run:
  "\<exists>s'. run_steps example_steps example_start = Some s' \<and>
        lookup_handle 0 2 s' = None \<and>
        (\<exists>h. lookup_handle 1 2 s' = Some h \<and> ZX_RIGHT_WRITE \<notin> h_rights h) \<and>
        vmo_content 2 s' = Some 42"
  using example_steps_ok_true
  unfolding example_steps_ok_def
  by (auto split: option.splits)

theorem example_trace_reachable_wf:
  "\<exists>s'. reachable example_start s' \<and> state_wf s' \<and>
        lookup_handle 0 2 s' = None \<and>
        (\<exists>h. lookup_handle 1 2 s' = Some h \<and> ZX_RIGHT_WRITE \<notin> h_rights h) \<and>
        vmo_content 2 s' = Some 42"
proof -
  from example_steps_run obtain s' where
    run: "run_steps example_steps example_start = Some s'" and
    props: "lookup_handle 0 2 s' = None"
           "\<exists>h. lookup_handle 1 2 s' = Some h \<and> ZX_RIGHT_WRITE \<notin> h_rights h"
           "vmo_content 2 s' = Some 42"
    by blast
  from run_steps_reachable[OF run] have r: "reachable example_start s'" .
  from reachable_preserves_wf[OF example_start_wf r] have "state_wf s'" .
  with r props show ?thesis by blast
qed

end
