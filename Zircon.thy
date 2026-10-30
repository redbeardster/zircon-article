section \<open>Zircon\<close>

theory Zircon
imports
  Main
begin

text \<open>
  \<^bold>\<open>Учебная модель\<close> передачи capability в стиле микроядра Zircon (Fuchsia OS)
  на Isabelle/HOL.

  Мы моделируем: процессы с таблицами дескрипторов (handles), каналы как
  kernel objects с очередями capabilities (доступ через handle на endpoint),
  пересечение прав и \<^emph>\<open>move\<close>-семантику при @{text zx_channel_write},
  проверку @{text ZX_RIGHT_WRITE} при записи в VMO.

  \<^bold>\<open>Важно.\<close> Это не верификация реального ядра Zircon и не доказательство
  безопасности TCB Fuchsia. Это формализация небольшого фрагмента идей
  capability-модели для обучения.
\<close>

subsection \<open>1. Базовые типы (что мы постулируем)\<close>

text \<open>
  \<^emph>\<open>Постулат о типах объектов.\<close> Ядро оперирует конечным набором видов
  объектов. Мы фиксируем учебный перечень; в реальном Zircon типов больше.
\<close>

datatype kernel_obj_type =
    Process
  | Thread
  | Channel
  | VMO
  | Hardware
  | Other_Obj "string"

text \<open>
  \<^emph>\<open>Постулат о правах.\<close> Право --- атомарный флаг доступа. Набор прав у
  дескриптора --- множество таких флагов. Список сокращён относительно
  настоящего Zircon (нет, например, WAIT, DESTROY, property/policy rights).

  Для handle на @{text Channel}: @{text ZX_RIGHT_WRITE} разрешает класть
  сообщения в очередь, @{text ZX_RIGHT_READ} --- забирать. Для @{text VMO}:
  @{text ZX_RIGHT_WRITE} разрешает менять содержимое в @{text vmo_store}.
\<close>

datatype right =
    ZX_RIGHT_READ
  | ZX_RIGHT_WRITE
  | ZX_RIGHT_EXECUTE
  | ZX_RIGHT_MAP
  | ZX_RIGHT_TRANSFER
  | ZX_RIGHT_DUPLICATE
  | ZX_RIGHT_SIGNAL

type_synonym rights = "right set"

text \<open>
  \<^emph>\<open>Постулат об идентификаторах.\<close> Вместо 32-битных слов Zircon используем
  @{typ nat}: так проще выделять свежие id и доказывать свойства. Это
  абстракция кодирования, а не модель битовой раскладки handles.
\<close>

type_synonym handle_id = nat
type_synonym obj_id = nat
type_synonym process_id = nat

text \<open>
  \<^emph>\<open>Постулат о kernel object.\<close> Объект в модели --- пара (тип, уникальный id).
  Семантика содержимого (кроме VMO, см. ниже) не раскрывается.
\<close>

record kernel_obj =
  obj_type :: kernel_obj_type
  obj_id   :: obj_id

text \<open>
  \<^emph>\<open>Постулат о handle.\<close> Дескриптор --- ссылка на объект плюс маска прав.
  Именно маска проверяется при syscall и уменьшается при передаче.
\<close>

record handle =
  h_obj    :: kernel_obj
  h_rights :: rights

text \<open>
  Таблица дескрипторов процесса --- частичная функция из id в handle
  (@{text "\<rightharpoonup>"} = option-valued map).
\<close>

type_synonym handle_table = "handle_id \<rightharpoonup> handle"

text \<open>
  Capability в пути по каналу представляем тем же типом, что и handle:
  объект + права (без локального handle id получателя --- id появится при read).
\<close>

type_synonym capability = handle

text \<open>
  \<^emph>\<open>Постулат о глобальном состоянии.\<close> Всё ядро в модели --- одна запись
  @{text system_state}:
  \<^item> @{text proc_tables} --- таблицы handles процессов;
  \<^item> @{text next_hids} --- счётчики свежих handle id;
  \<^item> @{text channels} --- очереди capabilities, ключ --- @{text obj_id}
    \<^emph>\<open>конца\<close> канала (у каждого endpoint своя очередь);
  \<^item> @{text channel_peer} --- связь конца с противоположным
    (@{text "channel_peer a = Some b"} и обратно);
  \<^item> @{text vmo_store} --- абстрактное содержимое VMO;
  \<^item> @{text next_obj_id} --- счётчик идентификаторов объектов.

  Канал --- пара endpoint-объектов: @{text zx_channel_write} кладёт
  сообщение в очередь \<^emph>\<open>пира\<close>, @{text zx_channel_read} забирает из
  \<^emph>\<open>своей\<close> очереди (как в Zircon: сообщение уходит на противоположный конец).
  Доступ только через handle с нужными правами.

  \<^emph>\<open>Учебное отличие от Zircon.\<close> При отказе @{text zx_channel_write}
  состояние не меняется (@{text None}). В реальном Zircon передаваемые
  handles уничтожаются и при ошибке (\<guillemotleft>on success or failure\<guillemotright>); чтобы
  сохранить их, нужен @{text zx_channel_write_etc}. Мы оставляем
  \<guillemotleft>отказ = нет мутаций\<guillemotright> ради локальных доказательств.
\<close>

record system_state =
  proc_tables  :: "process_id \<rightharpoonup> handle_table"
  next_hids    :: "process_id \<rightharpoonup> handle_id"
  channels     :: "obj_id \<rightharpoonup> capability list"
  channel_peer :: "obj_id \<rightharpoonup> obj_id"
  vmo_store    :: "obj_id \<rightharpoonup> nat"
  next_obj_id  :: obj_id

definition empty_state :: system_state where
  "empty_state = \<lparr>
     proc_tables  = Map.empty,
     next_hids    = Map.empty,
     channels     = Map.empty,
     channel_peer = Map.empty,
     vmo_store    = Map.empty,
     next_obj_id  = 0
   \<rparr>"

subsection \<open>2. Вспомогательные функции\<close>

text \<open>
  \<^emph>\<open>Определение уменьшения прав.\<close> Запрошенные права пересекаются с
  имеющимися: @{term "reduce_rights R_new R_old = R_new \<inter> R_old"}
  (@{text definition}, не аксиома).
  Отсюда позже следует отсутствие эскалации: результат всегда
  @{text "\<subseteq>"} старых прав.
  Замкнутое сокращение @{text reduce_rights_wf} вводится сразу ниже и
  используется в syscall-пути.
\<close>

definition reduce_rights :: "rights \<Rightarrow> rights \<Rightarrow> rights" where
  "reduce_rights new_rights old_rights = (new_rights \<inter> old_rights)"

definition rights_wf :: "rights \<Rightarrow> bool" where
  "rights_wf R \<equiv>
     (ZX_RIGHT_WRITE \<in> R \<longrightarrow> ZX_RIGHT_READ \<in> R) \<and>
     (ZX_RIGHT_EXECUTE \<in> R \<longrightarrow> ZX_RIGHT_READ \<in> R)"

definition close_rights :: "rights \<Rightarrow> rights" where
  "close_rights R =
     (if ZX_RIGHT_WRITE \<in> R \<or> ZX_RIGHT_EXECUTE \<in> R
      then insert ZX_RIGHT_READ R else R)"

definition reduce_rights_wf :: "rights \<Rightarrow> rights \<Rightarrow> rights" where
  "reduce_rights_wf req src = close_rights (reduce_rights req src)"

text \<open>
  \<^emph>\<open>Зависимые права.\<close> @{text WRITE} и @{text EXECUTE} требуют @{text READ}.
  Сырое пересечение может нарушить зависимость; @{const reduce_rights_wf}
  замыкает результат. Добавить @{text READ} к маске с @{text WRITE}
  безопасно для no-escalation только если источник уже был
  @{const rights_wf}: тогда @{text READ} у него уже был, и замыкание
  ничего не изобретает. Если источника с @{text WRITE} без @{text READ}
  допустить, замыкание как раз и даст эскалацию
  (@{text transfer_without_wf_source_may_escalate}).
  Операции передачи используют именно замкнутое сокращение.

  Корректность маски \<^emph>\<open>источника\<close> (@{const rights_wf}) syscall'ы
  \<^emph>\<open>не проверяют\<close> --- как и ядро Zircon, которое не валидирует маски при
  передаче. Она гарантируется инвариантом состояния @{text state_wf}
  (теория @{text Zircon_Traces}): создающие операции отклоняют некорректные
  начальные маски, а передающие кладут в таблицы и очереди только замкнутые.
  Поэтому пошаговые леммы no-escalation принимают @{const rights_wf}
  источника как посылку, а трассовая теорема выводит её из достижимости.
\<close>

lemma close_rights_wf:
  "rights_wf (close_rights R)"
  by (auto simp: rights_wf_def close_rights_def)

lemma close_rights_idem:
  "close_rights (close_rights R) = close_rights R"
  by (auto simp: close_rights_def)

lemma close_rights_fix_wf:
  "rights_wf R \<longleftrightarrow> close_rights R = R"
  by (auto simp: rights_wf_def close_rights_def)

lemma close_rights_infl:
  "R \<subseteq> close_rights R"
  by (auto simp: close_rights_def)

lemma close_rights_mono:
  assumes "R \<subseteq> S"
  shows "close_rights R \<subseteq> close_rights S"
  using assms by (auto simp: close_rights_def)

lemma reduce_rights_wf_wf:
  "rights_wf (reduce_rights_wf req src)"
  by (simp add: reduce_rights_wf_def close_rights_wf)

lemma reduce_rights_subset:
  "reduce_rights R_new R_old \<subseteq> R_old"
  by (simp add: reduce_rights_def)

lemma reduce_rights_wf_le_old:
  assumes "rights_wf src"
  shows "reduce_rights_wf req src \<subseteq> src"
proof -
  have "reduce_rights req src \<subseteq> src"
    by (simp add: reduce_rights_def)
  show ?thesis
  proof (cases "ZX_RIGHT_WRITE \<in> reduce_rights req src \<or>
                ZX_RIGHT_EXECUTE \<in> reduce_rights req src")
    case True
    then have "ZX_RIGHT_READ \<in> src"
      using assms by (auto simp: rights_wf_def reduce_rights_def)
    with \<open>reduce_rights req src \<subseteq> src\<close> show ?thesis
      by (auto simp: reduce_rights_wf_def close_rights_def)
  next
    case False
    with \<open>reduce_rights req src \<subseteq> src\<close> show ?thesis
      by (auto simp: reduce_rights_wf_def close_rights_def)
  qed
qed

definition has_right_h :: "handle \<Rightarrow> right \<Rightarrow> bool" where
  "has_right_h h r = (r \<in> h_rights h)"

text \<open>Поиск handle в таблице процесса; @{text None}, если процесса или id нет.\<close>

definition lookup_handle ::
  "process_id \<Rightarrow> handle_id \<Rightarrow> system_state \<Rightarrow> handle option" where
  "lookup_handle pid hid s =
    (case proc_tables s pid of
      None \<Rightarrow> None
    | Some ht \<Rightarrow> ht hid)"

definition get_table ::
  "process_id \<Rightarrow> system_state \<Rightarrow> handle_table option" where
  "get_table pid s = proc_tables s pid"

definition set_table ::
  "process_id \<Rightarrow> handle_table \<Rightarrow> system_state \<Rightarrow> system_state" where
  "set_table pid ht s = s\<lparr> proc_tables := (proc_tables s)(pid \<mapsto> ht) \<rparr>"

text \<open>
  Выделение свежего handle id: монотонный счётчик на процесс. Нумерация
  начинается с @{term "1::nat"}: в Zircon значение @{text 0} зарезервировано
  как @{text ZX_HANDLE_INVALID}.
\<close>

definition alloc_hid ::
  "process_id \<Rightarrow> system_state \<Rightarrow> handle_id \<times> system_state" where
  "alloc_hid pid s =
    (let hid = (case next_hids s pid of None \<Rightarrow> 1 | Some n \<Rightarrow> n);
         s'  = s\<lparr> next_hids := (next_hids s)(pid \<mapsto> Suc hid) \<rparr>
     in (hid, s'))"

subsection \<open>3. Инициализация процессов и каналов\<close>

definition init_process ::
  "process_id \<Rightarrow> system_state \<Rightarrow> system_state" where
  "init_process pid s =
    s\<lparr> proc_tables := (proc_tables s)(pid \<mapsto> Map.empty),
       next_hids   := (next_hids s)(pid \<mapsto> 1) \<rparr>"

text \<open>
  \<^bold>\<open>create\_channel\_pair.\<close> Создаёт \<^emph>\<open>два\<close> endpoint-объекта @{text Channel}
  с пустыми очередями и взаимной связью @{text channel_peer}. Процесс
  @{text pid0} получает handle на первый конец, @{text pid1} --- на второй.
  Возвращаемый @{text obj_id} --- id конца @{text pid0} (для удобства сценариев).

  \<^emph>\<open>Учебное отличие от Zircon.\<close> @{text zx_channel_create} возвращает
  \<^emph>\<open>оба\<close> конца создателю, с одинаковыми правами по умолчанию
  (@{text "TRANSFER | READ | WRITE | WAIT | INSPECT | SIGNAL | SIGNAL_PEER"});
  второй конец попадает в другой процесс через bootstrap-handle при
  @{text zx_process_start} или через уже существующий канал. Мы склеиваем
  \<guillemotleft>создать + доставить второй конец\<guillemotright> в один шаг и разрешаем задать маски
  независимо.
\<close>

definition create_channel_pair ::
  "process_id \<Rightarrow> process_id \<Rightarrow> rights \<Rightarrow> rights \<Rightarrow> system_state \<Rightarrow>
   (handle_id \<times> handle_id \<times> obj_id \<times> system_state) option" where
  "create_channel_pair pid0 pid1 rights0 rights1 s =
    (case get_table pid0 s of
      None \<Rightarrow> None
    | Some ht0 \<Rightarrow>
        (case get_table pid1 s of
          None \<Rightarrow> None
        | Some _ \<Rightarrow>
            if \<not> rights_wf rights0 \<or> \<not> rights_wf rights1 then None
            else
              (let oid0 = next_obj_id s;
                   oid1 = Suc oid0;
                   obj0 = \<lparr> obj_type = Channel, obj_id = oid0 \<rparr>;
                   obj1 = \<lparr> obj_type = Channel, obj_id = oid1 \<rparr>;
                   h0  = \<lparr> h_obj = obj0, h_rights = rights0 \<rparr>;
                   h1  = \<lparr> h_obj = obj1, h_rights = rights1 \<rparr>;
                   (hid0, s1) = alloc_hid pid0 s;
                   s2 = set_table pid0 (ht0(hid0 \<mapsto> h0)) s1;
                   (hid1, s3) = alloc_hid pid1 s2
               in (case get_table pid1 s3 of
                     None \<Rightarrow> None
                   | Some ht1 \<Rightarrow>
                       (let s4 = set_table pid1 (ht1(hid1 \<mapsto> h1)) s3;
                            s5 = s4\<lparr>
                              channels := (channels s4)
                                (oid0 \<mapsto> [], oid1 \<mapsto> []),
                              channel_peer := (channel_peer s4)
                                (oid0 \<mapsto> oid1, oid1 \<mapsto> oid0),
                              next_obj_id := Suc oid1 \<rparr>
                        in Some (hid0, hid1, oid0, s5))))))"

subsection \<open>4. Создание объектов и системные вызовы\<close>

text \<open>
  \<^bold>\<open>create\_vmo.\<close> Создаёт VMO с заданным содержимым и ставит handle в таблицу
  процесса @{text pid} с @{text initial_rights}.

  \<^emph>\<open>Постулат (ограничение модели).\<close> Политика \<guillemotleft>кто имеет право чеканить
  какие права при создании\<guillemotright> \<^emph>\<open>вне scope\<close>.
\<close>

definition create_vmo ::
  "process_id \<Rightarrow> rights \<Rightarrow> nat \<Rightarrow> system_state \<Rightarrow>
   (handle_id \<times> obj_id \<times> system_state) option" where
  "create_vmo pid initial_rights content s =
    (case get_table pid s of
      None \<Rightarrow> None
    | Some ht \<Rightarrow>
        if \<not> rights_wf initial_rights then None
        else
          (let oid = next_obj_id s;
               obj = \<lparr> obj_type = VMO, obj_id = oid \<rparr>;
               h   = \<lparr> h_obj = obj, h_rights = initial_rights \<rparr>;
               (hid, s1) = alloc_hid pid s;
               ht' = ht(hid \<mapsto> h);
               s2  = set_table pid ht' s1;
               s3  = s2\<lparr> vmo_store := (vmo_store s2)(oid \<mapsto> content),
                         next_obj_id := Suc oid \<rparr>
           in Some (hid, oid, s3)))"

text \<open>
  \<^bold>\<open>zx\_channel\_write.\<close> Кладёт capability в очередь \<^emph>\<open>противоположного\<close>
  конца и \<^emph>\<open>удаляет\<close> payload-handle у отправителя (move).

  Прообраз в Zircon --- @{text zx_channel_write_etc} с одной записью
  @{text "zx_handle_disposition_t {operation = ZX_HANDLE_OP_MOVE, rights = req}"}:
  там @{text rights} --- \<guillemotleft>desired final rights (not a mask)\<guillemotright>, и запрос сверх
  прав источника даёт @{text ZX_ERR_INVALID_ARGS}.

  Условия успеха:
  \<^item> @{text ch_hid} --- handle типа @{text Channel} с @{text ZX_RIGHT_WRITE}
    (иначе @{text ZX_ERR_ACCESS_DENIED} / @{text ZX_ERR_WRONG_TYPE});
  \<^item> @{text "ch_hid \<noteq> pay_hid"} (в Zircon --- @{text ZX_ERR_NOT_SUPPORTED}:
    канал нельзя отправить в самого себя);
  \<^item> @{text pay_hid} --- handle с @{text ZX_RIGHT_TRANSFER} и
    @{term "req_rights \<subseteq> h_rights h_pay"};
  \<^item> у конца есть пир (иначе @{text ZX_ERR_PEER_CLOSED}), очередь пира существует.

  Права в сообщении~--- @{term "reduce_rights_wf req_rights (h_rights h_pay)"}
  (при @{text "req \<subseteq> src"} это @{term "close_rights req_rights"}).
  Пустая запрошенная маска допускается; @{text TRANSFER} в запросе можно
  опустить --- тогда получатель не сможет переслать handle дальше (как в
  @{text write_etc}).

  \<^emph>\<open>Постулат move-into-message.\<close> После успеха
  @{text "lookup_handle pid pay_hid s' = None"}.
\<close>

definition zx_channel_write ::
  "process_id \<Rightarrow> handle_id \<Rightarrow> handle_id \<Rightarrow> rights \<Rightarrow> system_state \<Rightarrow>
   system_state option" where
  "zx_channel_write pid ch_hid pay_hid req_rights s =
    (case (lookup_handle pid ch_hid s, lookup_handle pid pay_hid s, get_table pid s) of
      (Some h_ch, Some h_pay, Some ht) \<Rightarrow>
        if ch_hid = pay_hid then None
        else if obj_type (h_obj h_ch) \<noteq> Channel then None
        else if ZX_RIGHT_WRITE \<notin> h_rights h_ch then None
        else if ZX_RIGHT_TRANSFER \<notin> h_rights h_pay then None
        else if \<not> (req_rights \<subseteq> h_rights h_pay) then None
        else
          (case channel_peer s (obj_id (h_obj h_ch)) of
            None \<Rightarrow> None
          | Some peer \<Rightarrow>
              (case channels s peer of
                None \<Rightarrow> None
              | Some q \<Rightarrow>
                  (let actual = reduce_rights_wf req_rights (h_rights h_pay);
                       cap = \<lparr> h_obj = h_obj h_pay, h_rights = actual \<rparr>;
                       ht' = ht(pay_hid := None);
                       s1  = set_table pid ht' s;
                       s2  = s1\<lparr> channels := (channels s1)(peer \<mapsto> q @ [cap]) \<rparr>
                   in Some s2)))
    | _ \<Rightarrow> None)"

text \<open>
  \<^bold>\<open>zx\_channel\_read.\<close> Забирает голову \<^emph>\<open>своей\<close> очереди через handle на
  endpoint с @{text ZX_RIGHT_READ} и ставит capability как новый handle.
\<close>

definition zx_channel_read ::
  "process_id \<Rightarrow> handle_id \<Rightarrow> system_state \<Rightarrow>
   (handle_id \<times> system_state) option" where
  "zx_channel_read pid ch_hid s =
    (case (lookup_handle pid ch_hid s, get_table pid s) of
      (Some h_ch, Some ht) \<Rightarrow>
        if obj_type (h_obj h_ch) \<noteq> Channel then None
        else if ZX_RIGHT_READ \<notin> h_rights h_ch then None
        else
          (case channels s (obj_id (h_obj h_ch)) of
            Some (cap # rest) \<Rightarrow>
              (let oid = obj_id (h_obj h_ch);
                   (hid, s1) = alloc_hid pid s;
                   ht' = ht(hid \<mapsto> cap);
                   s2  = set_table pid ht' s1;
                   s3  = s2\<lparr> channels := (channels s2)(oid \<mapsto> rest) \<rparr>
               in Some (hid, s3))
          | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"

text \<open>
  \<^bold>\<open>transfer\_via\_channel.\<close> Композиция write+read. Endpoint'ы должны быть
  \<^emph>\<open>пирами\<close> (@{text channel_peer}); очередь получателя перед передачей
  пуста.
\<close>

definition transfer_via_channel ::
  "process_id \<Rightarrow> process_id \<Rightarrow> handle_id \<Rightarrow> handle_id \<Rightarrow> handle_id \<Rightarrow> rights \<Rightarrow>
   system_state \<Rightarrow> (handle_id \<times> system_state) option" where
  "transfer_via_channel src dst src_ch dst_ch pay_hid req_rights s =
    (case (lookup_handle src src_ch s, lookup_handle dst dst_ch s) of
      (Some h_src_ch, Some h_dst_ch) \<Rightarrow>
        if obj_type (h_obj h_src_ch) \<noteq> Channel \<or>
           obj_type (h_obj h_dst_ch) \<noteq> Channel then None
        else if channel_peer s (obj_id (h_obj h_src_ch)) \<noteq>
                Some (obj_id (h_obj h_dst_ch)) then None
        else
          (case channels s (obj_id (h_obj h_dst_ch)) of
            Some [] \<Rightarrow>
              (case zx_channel_write src src_ch pay_hid req_rights s of
                None \<Rightarrow> None
              | Some s1 \<Rightarrow> zx_channel_read dst dst_ch s1)
          | _ \<Rightarrow> None)
    | _ \<Rightarrow> None)"

text \<open>
  \<^bold>\<open>vmo\_write.\<close> Меняет содержимое VMO в @{text vmo_store}.
  Успех только если: handle валиден, тип объекта VMO, есть
  @{text ZX_RIGHT_WRITE}.
\<close>

definition vmo_write ::
  "process_id \<Rightarrow> handle_id \<Rightarrow> nat \<Rightarrow> system_state \<Rightarrow> system_state option" where
  "vmo_write pid hid content s =
    (case lookup_handle pid hid s of
      None \<Rightarrow> None
    | Some h \<Rightarrow>
        if obj_type (h_obj h) \<noteq> VMO then None
        else if ZX_RIGHT_WRITE \<notin> h_rights h then None
        else
          Some (s\<lparr> vmo_store :=
            (vmo_store s)(obj_id (h_obj h) \<mapsto> content) \<rparr>))"

definition vmo_content ::
  "obj_id \<Rightarrow> system_state \<Rightarrow> nat option" where
  "vmo_content oid s = vmo_store s oid"

text \<open>
  \<^bold>\<open>zx\_handle\_duplicate.\<close> Дублирование дескриптора с урезанием маски:
  требуется @{text ZX_RIGHT_DUPLICATE} (иначе @{text ZX_ERR_ACCESS_DENIED}) и
  @{term "req_rights \<subseteq> h_rights h"} (иначе @{text ZX_ERR_INVALID_ARGS}) ---
  ровно как у @{text zx_handle_duplicate} в Zircon. Новый handle смотрит на
  тот же объект, права~--- @{const reduce_rights_wf}. Исходный handle
  сохраняется.
\<close>

definition zx_handle_duplicate ::
  "process_id \<Rightarrow> handle_id \<Rightarrow> rights \<Rightarrow> system_state \<Rightarrow>
   (handle_id \<times> system_state) option" where
  "zx_handle_duplicate pid hid req_rights s =
    (case (lookup_handle pid hid s, get_table pid s) of
      (Some h, Some ht) \<Rightarrow>
        if ZX_RIGHT_DUPLICATE \<notin> h_rights h then None
        else if \<not> (req_rights \<subseteq> h_rights h) then None
        else
          (let actual = reduce_rights_wf req_rights (h_rights h);
               h' = h\<lparr> h_rights := actual \<rparr>;
               (hid', s1) = alloc_hid pid s
           in Some (hid', set_table pid (ht(hid' \<mapsto> h')) s1))
    | _ \<Rightarrow> None)"

text \<open>
  \<^bold>\<open>zx\_handle\_close.\<close> Удаляет слот из таблицы. В Zircon
  @{text ZX_HANDLE_OP_MOVE} определён как @{text zx_handle_replace}
  (атомарное \<guillemotleft>новый handle с урезанной маской + закрыть старый\<guillemotright>) с
  последующим write; в модели move встроен в @{const zx_channel_write}, а
  close оставлен явным. Подсчёт ссылок и уничтожение объекта при закрытии
  последнего handle не моделируются.
\<close>

definition zx_handle_close ::
  "process_id \<Rightarrow> handle_id \<Rightarrow> system_state \<Rightarrow> system_state option" where
  "zx_handle_close pid hid s =
    (case (lookup_handle pid hid s, get_table pid s) of
      (Some _, Some ht) \<Rightarrow> Some (set_table pid (ht(hid := None)) s)
    | _ \<Rightarrow> None)"

subsection \<open>5. Учебный сценарий\<close>

text \<open>
  Процессы 0 и 1 получают по handle на два конца одного канала (пиры).
  Процесс 0 создаёт VMO с правами READ$\mid$WRITE$\mid$TRANSFER и содержимым 42,
  передаёт процессу 1 только READ (move). Ожидаем:
  \<^item> у B есть READ и нет WRITE;
  \<^item> объект тот же;
  \<^item> у A payload-handle исчез (move);
  \<^item> @{text vmo_write} у B даёт @{text None};
  \<^item> содержимое VMO остаётся 42.
\<close>

definition example_channel_rights :: rights where
  "example_channel_rights = {ZX_RIGHT_READ, ZX_RIGHT_WRITE}"

definition example_scenario :: bool where
  "example_scenario =
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
                           ZX_RIGHT_READ \<in> h_rights h_b \<and>
                           ZX_RIGHT_WRITE \<notin> h_rights h_b \<and>
                           obj_id (h_obj h_b) = oid \<and>
                           lookup_handle 0 hid_a s3 = None \<and>
                           vmo_write 1 hid_b 99 s3 = None \<and>
                           vmo_content oid s3 = Some 42))))"

subsection \<open>6. Свойства безопасности (доказанные утверждения)\<close>

subsubsection \<open>Свойства пересечения прав\<close>

lemma reduce_rights_compose:
  "reduce_rights R1 (reduce_rights R2 R) = reduce_rights (R1 \<inter> R2) R"
  by (auto simp: reduce_rights_def)

subsubsection \<open>Характеризация успешного write / read\<close>

lemma zx_channel_write_success:
  assumes "zx_channel_write pid ch_hid pay_hid req_rights s = Some s'"
  assumes "lookup_handle pid ch_hid s = Some h_ch"
  assumes "lookup_handle pid pay_hid s = Some h_pay"
  shows "ch_hid \<noteq> pay_hid"
    and "obj_type (h_obj h_ch) = Channel"
    and "ZX_RIGHT_WRITE \<in> h_rights h_ch"
    and "ZX_RIGHT_TRANSFER \<in> h_rights h_pay"
    and "req_rights \<subseteq> h_rights h_pay"
    and "\<exists>ht q peer. get_table pid s = Some ht \<and>
             channel_peer s (obj_id (h_obj h_ch)) = Some peer \<and>
             channels s peer = Some q \<and>
             s' = (set_table pid (ht(pay_hid := None)) s)
                    \<lparr> channels :=
                      (channels (set_table pid (ht(pay_hid := None)) s))
                        (peer \<mapsto>
                          q @ [\<lparr> h_obj = h_obj h_pay,
                                 h_rights = reduce_rights_wf req_rights (h_rights h_pay) \<rparr>]) \<rparr>"
  using assms
  by (auto simp: zx_channel_write_def Let_def set_table_def
           split: option.splits if_splits)

lemma zx_channel_read_success:
  assumes "zx_channel_read pid ch_hid s = Some (hid', s')"
  assumes "lookup_handle pid ch_hid s = Some h_ch"
  shows "obj_type (h_obj h_ch) = Channel"
    and "ZX_RIGHT_READ \<in> h_rights h_ch"
    and "\<exists>ht cap rest hid_alloc s_alloc.
           get_table pid s = Some ht \<and>
           channels s (obj_id (h_obj h_ch)) = Some (cap # rest) \<and>
           alloc_hid pid s = (hid_alloc, s_alloc) \<and>
           hid' = hid_alloc \<and>
           s' = (set_table pid (ht(hid_alloc \<mapsto> cap)) s_alloc)
                  \<lparr> channels :=
                    (channels (set_table pid (ht(hid_alloc \<mapsto> cap)) s_alloc))
                      (obj_id (h_obj h_ch) \<mapsto> rest) \<rparr>"
  using assms
  by (auto simp: zx_channel_read_def Let_def lookup_handle_def get_table_def
           split: option.splits list.splits prod.splits if_splits)

lemma lookup_after_set_table:
  "lookup_handle pid hid (set_table pid ht s) = ht hid"
  by (simp add: lookup_handle_def set_table_def)

lemma lookup_after_alloc_hid:
  "lookup_handle pid hid (snd (alloc_hid pid s)) = lookup_handle pid hid s"
  by (simp add: lookup_handle_def alloc_hid_def Let_def split: option.splits)

subsubsection \<open>Шлюзы WRITE (канал), TRANSFER (payload), READ (канал)\<close>

lemma channel_write_requires_transfer:
  assumes "zx_channel_write pid ch_hid pay_hid req_rights s = Some s'"
  shows "\<exists>h. lookup_handle pid pay_hid s = Some h \<and>
             ZX_RIGHT_TRANSFER \<in> h_rights h"
  using assms
  by (auto simp: zx_channel_write_def Let_def split: option.splits if_splits)

lemma channel_write_requires_channel_write_right:
  assumes "zx_channel_write pid ch_hid pay_hid req_rights s = Some s'"
  shows "\<exists>h. lookup_handle pid ch_hid s = Some h \<and>
             obj_type (h_obj h) = Channel \<and>
             ZX_RIGHT_WRITE \<in> h_rights h"
  using assms
  by (auto simp: zx_channel_write_def Let_def split: option.splits if_splits)

lemma channel_write_fails_without_transfer:
  assumes "lookup_handle pid ch_hid s = Some h_ch"
  assumes "lookup_handle pid pay_hid s = Some h_pay"
  assumes "get_table pid s = Some ht"
  assumes "ch_hid \<noteq> pay_hid"
  assumes "obj_type (h_obj h_ch) = Channel"
  assumes "ZX_RIGHT_WRITE \<in> h_rights h_ch"
  assumes "ZX_RIGHT_TRANSFER \<notin> h_rights h_pay"
  shows "zx_channel_write pid ch_hid pay_hid req_rights s = None"
  using assms
  by (simp add: zx_channel_write_def)

lemma channel_write_fails_unless_subset:
  assumes "lookup_handle pid ch_hid s = Some h_ch"
  assumes "lookup_handle pid pay_hid s = Some h_pay"
  assumes "get_table pid s = Some ht"
  assumes "ch_hid \<noteq> pay_hid"
  assumes "obj_type (h_obj h_ch) = Channel"
  assumes "ZX_RIGHT_WRITE \<in> h_rights h_ch"
  assumes "ZX_RIGHT_TRANSFER \<in> h_rights h_pay"
  assumes "\<not> (req_rights \<subseteq> h_rights h_pay)"
  shows "zx_channel_write pid ch_hid pay_hid req_rights s = None"
  using assms
  by (simp add: zx_channel_write_def)

lemma channel_write_fails_without_channel_write:
  assumes "lookup_handle pid ch_hid s = Some h_ch"
  assumes "lookup_handle pid pay_hid s = Some h_pay"
  assumes "get_table pid s = Some ht"
  assumes "ch_hid \<noteq> pay_hid"
  assumes "obj_type (h_obj h_ch) = Channel"
  assumes "ZX_RIGHT_WRITE \<notin> h_rights h_ch"
  shows "zx_channel_write pid ch_hid pay_hid req_rights s = None"
  using assms
  by (simp add: zx_channel_write_def)

subsubsection \<open>Move: удаление handle отправителя\<close>

text \<open>
  \<^bold>\<open>Лемма @{text channel_write_moves_sender_handle}.\<close>
  После успешного write payload-handle отправителя аннулирован.
\<close>

lemma channel_write_moves_sender_handle:
  assumes "zx_channel_write pid ch_hid pay_hid req_rights s = Some s'"
  shows "lookup_handle pid pay_hid s' = None"
  using assms
  by (auto simp: zx_channel_write_def lookup_handle_def set_table_def get_table_def
                 Let_def
           split: option.splits if_splits)

lemma channel_write_preserves_other_handles:
  assumes "zx_channel_write pid ch_hid pay_hid req_rights s = Some s'"
  assumes "hid \<noteq> pay_hid"
  shows "lookup_handle pid hid s' = lookup_handle pid hid s"
  using assms
  by (auto simp: zx_channel_write_def lookup_handle_def set_table_def get_table_def
                 Let_def
           split: option.splits if_splits)

lemma channel_write_preserves_channel_handle:
  assumes "zx_channel_write pid ch_hid pay_hid req_rights s = Some s'"
  assumes "ch_hid \<noteq> pay_hid"
  shows "lookup_handle pid ch_hid s' = lookup_handle pid ch_hid s"
  using assms by (rule channel_write_preserves_other_handles)


subsubsection \<open>Нет эскалации и сохранение объекта\<close>

lemma transfer_via_channel_cap:
  assumes "transfer_via_channel src dst src_ch dst_ch pay_hid req_rights s =
             Some (hid', s')"
  assumes "lookup_handle src pay_hid s = Some h_src"
  shows "lookup_handle dst hid' s' =
           Some \<lparr> h_obj = h_obj h_src,
                  h_rights = reduce_rights_wf req_rights (h_rights h_src) \<rparr>"
proof -
  let ?cap = "\<lparr> h_obj = h_obj h_src,
                h_rights = reduce_rights_wf req_rights (h_rights h_src) \<rparr>"

  from assms(1) obtain h_src_ch h_dst_ch where
    lch_src: "lookup_handle src src_ch s = Some h_src_ch" and
    lch_dst: "lookup_handle dst dst_ch s = Some h_dst_ch" and
    ty_src: "obj_type (h_obj h_src_ch) = Channel" and
    ty_dst: "obj_type (h_obj h_dst_ch) = Channel" and
    peers: "channel_peer s (obj_id (h_obj h_src_ch)) =
              Some (obj_id (h_obj h_dst_ch))"
    by (auto simp: transfer_via_channel_def split: option.splits if_splits)

  let ?dst_oid = "obj_id (h_obj h_dst_ch)"

  from assms(1) lch_src lch_dst ty_src ty_dst peers
  have empty_ch: "channels s ?dst_oid = Some []"
    by (auto simp: transfer_via_channel_def split: option.splits list.splits if_splits)

  from assms(1) lch_src lch_dst ty_src ty_dst peers empty_ch obtain s1 where
    w: "zx_channel_write src src_ch pay_hid req_rights s = Some s1" and
    r: "zx_channel_read dst dst_ch s1 = Some (hid', s')"
    by (auto simp: transfer_via_channel_def split: option.splits if_splits)

  from zx_channel_write_success[OF w lch_src assms(2)] peers
  obtain ht q where
    gt: "get_table src s = Some ht" and
    peer_q: "channels s ?dst_oid = Some q" and
    s1_def: "s1 = (set_table src (ht(pay_hid := None)) s)
               \<lparr> channels :=
                 (channels (set_table src (ht(pay_hid := None)) s))
                   (?dst_oid \<mapsto> q @ [?cap]) \<rparr>"
    by (auto simp: set_table_def)

  from s1_def empty_ch peer_q have ch1: "channels s1 ?dst_oid = Some [?cap]"
    by (simp add: set_table_def)

  have lch_dst1: "lookup_handle dst dst_ch s1 = Some h_dst_ch"
  proof (cases "src = dst")
    case True
    from channel_write_moves_sender_handle[OF w] True
    have pay_gone: "lookup_handle dst pay_hid s1 = None" by simp
    from r have "lookup_handle dst dst_ch s1 \<noteq> None"
      by (auto simp: zx_channel_read_def split: option.splits if_splits)
    with pay_gone have "dst_ch \<noteq> pay_hid" by auto
    with True w lch_dst show ?thesis
      using channel_write_preserves_other_handles[OF w, of dst_ch] by simp
  next
    case False
    from s1_def False lch_dst
    show ?thesis
      by (simp add: lookup_handle_def set_table_def)
  qed

  from zx_channel_read_success[OF r lch_dst1]
  obtain ht' cap rest hid_alloc s_alloc where
    gt': "get_table dst s1 = Some ht'" and
    queue: "channels s1 (obj_id (h_obj h_dst_ch)) = Some (cap # rest)" and
    al: "alloc_hid dst s1 = (hid_alloc, s_alloc)" and
    hid'_eq: "hid' = hid_alloc" and
    s'_def: "s' = (set_table dst (ht'(hid_alloc \<mapsto> cap)) s_alloc)
               \<lparr> channels :=
                 (channels (set_table dst (ht'(hid_alloc \<mapsto> cap)) s_alloc))
                   (obj_id (h_obj h_dst_ch) \<mapsto> rest) \<rparr>"
    by blast

  from queue ch1 have cap_eq: "cap = ?cap" and rest_empty: "rest = []"
    by auto

  from hid'_eq s'_def gt' al cap_eq
  show ?thesis
    by (simp add: lookup_handle_def set_table_def alloc_hid_def get_table_def Let_def
             split: option.splits)
qed

text \<open>
  Посылка @{term "rights_wf (h_rights h_src)"} --- не проверка внутри
  syscall, а свойство состояния: на достижимых состояниях её даёт
  @{text state_wf} (см.\ @{text reachable_transfer_no_escalation} в
  @{text Zircon_Traces}). Без неё утверждение ложно: источник
  @{text "{WRITE, TRANSFER}"} и запрос @{text "{WRITE}"} дали бы получателю
  @{text READ}.
\<close>

lemma transfer_via_channel_no_escalation:
  assumes "transfer_via_channel src dst src_ch dst_ch pay_hid req_rights s =
             Some (hid', s')"
  assumes "lookup_handle src pay_hid s = Some h_src"
  assumes "lookup_handle dst hid' s' = Some h_dst"
  assumes "rights_wf (h_rights h_src)"
  shows "h_rights h_dst \<subseteq> h_rights h_src"
  using transfer_via_channel_cap[OF assms(1,2)] assms(3)
        reduce_rights_wf_le_old[OF assms(4), of req_rights]
  by simp

lemma transfer_without_wf_source_may_escalate:
  "\<not> rights_wf {ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER} \<and>
   \<not> (reduce_rights_wf {ZX_RIGHT_WRITE} {ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}
         \<subseteq> {ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER})"
  by (simp add: rights_wf_def reduce_rights_wf_def reduce_rights_def close_rights_def)

lemma transfer_via_channel_preserves_object:
  assumes "transfer_via_channel src dst src_ch dst_ch pay_hid req_rights s =
             Some (hid', s')"
  assumes "lookup_handle src pay_hid s = Some h_src"
  assumes "lookup_handle dst hid' s' = Some h_dst"
  shows "h_obj h_dst = h_obj h_src"
  using transfer_via_channel_cap[OF assms(1,2)] assms(3)
  by simp

text \<open>
  После успешного @{text transfer_via_channel} между \<^emph>\<open>разными\<close> процессами
  payload-handle отправителя остаётся аннулированным (read получателя не
  затрагивает таблицу отправителя). Случай @{text "src = dst"} исключаем:
  свежий id при read теоретически мог бы совпасть с освобождённым слотом
  при немонотонном заполнении таблицы.
\<close>

lemma transfer_via_channel_moves_sender:
  assumes "transfer_via_channel src dst src_ch dst_ch pay_hid req_rights s =
             Some (hid', s')"
  assumes "src \<noteq> dst"
  shows "lookup_handle src pay_hid s' = None"
proof -
  from assms(1) have
    "\<exists>s1. zx_channel_write src src_ch pay_hid req_rights s = Some s1 \<and>
          zx_channel_read dst dst_ch s1 = Some (hid', s')"
    by (auto simp: transfer_via_channel_def split: option.splits if_splits list.splits)
  then obtain s1 where
    w: "zx_channel_write src src_ch pay_hid req_rights s = Some s1" and
    r: "zx_channel_read dst dst_ch s1 = Some (hid', s')"
    by blast

  from channel_write_moves_sender_handle[OF w]
  have gone: "lookup_handle src pay_hid s1 = None" .

  from assms(2) r gone show ?thesis
    by (auto simp: zx_channel_read_def lookup_handle_def set_table_def
                   alloc_hid_def get_table_def Let_def
            split: option.splits list.splits if_splits prod.splits)
qed

theorem channel_transfer_no_escalation:
  assumes "transfer_via_channel src dst src_ch dst_ch pay_hid req_rights s =
             Some (hid', s')"
  assumes "lookup_handle src pay_hid s = Some h_src"
  assumes "lookup_handle dst hid' s' = Some h_dst"
  assumes "rights_wf (h_rights h_src)"
  shows "\<not>(\<exists>r. r \<in> h_rights h_dst \<and> r \<notin> h_rights h_src)"
  using transfer_via_channel_no_escalation[OF assms] by blast




subsubsection \<open>Duplicate: тот же meet, другой вход\<close>

lemma zx_handle_duplicate_rights:
  assumes "zx_handle_duplicate pid hid req_rights s = Some (hid', s')"
  assumes "lookup_handle pid hid s = Some h"
  assumes "lookup_handle pid hid' s' = Some h'"
  shows "ZX_RIGHT_DUPLICATE \<in> h_rights h"
    and "req_rights \<subseteq> h_rights h"
    and "h_obj h' = h_obj h"
    and "h_rights h' = reduce_rights_wf req_rights (h_rights h)"
  using assms
  by (auto simp: zx_handle_duplicate_def lookup_handle_def set_table_def
                 alloc_hid_def get_table_def Let_def
          split: option.splits if_splits prod.splits)

lemma zx_handle_duplicate_no_escalation:
  assumes "zx_handle_duplicate pid hid req_rights s = Some (hid', s')"
  assumes "lookup_handle pid hid s = Some h"
  assumes "lookup_handle pid hid' s' = Some h'"
  assumes "rights_wf (h_rights h)"
  shows "h_rights h' \<le> h_rights h"
  using zx_handle_duplicate_rights(4)[OF assms(1-3)]
        reduce_rights_wf_le_old[OF assms(4), of req_rights]
  by (simp add: less_eq_set_def)

lemma zx_handle_duplicate_requires_duplicate_right:
  assumes "zx_handle_duplicate pid hid req_rights s = Some (hid', s')"
  shows "\<exists>h. lookup_handle pid hid s = Some h \<and>
             ZX_RIGHT_DUPLICATE \<in> h_rights h"
  using assms
  by (auto simp: zx_handle_duplicate_def Let_def split: option.splits if_splits)

lemma zx_handle_close_removes:
  assumes "zx_handle_close pid hid s = Some s'"
  shows "lookup_handle pid hid s' = None"
  using assms
  by (auto simp: zx_handle_close_def lookup_handle_def set_table_def
          split: option.splits)

subsubsection \<open>Целостность данных: запись требует WRITE\<close>

lemma vmo_write_denied_without_write_right:
  assumes "lookup_handle pid hid s = Some h"
  assumes "obj_type (h_obj h) = VMO"
  assumes "ZX_RIGHT_WRITE \<notin> h_rights h"
  shows "vmo_write pid hid content s = None"
  using assms by (simp add: vmo_write_def)

lemma vmo_write_denied_means_no_new_state:
  assumes "lookup_handle pid hid s = Some h"
  assumes "ZX_RIGHT_WRITE \<notin> h_rights h"
  shows "vmo_write pid hid content s = None"
  using assms by (auto simp: vmo_write_def)

lemma vmo_write_succeeds_iff_write_right:
  assumes "lookup_handle pid hid s = Some h"
  assumes "obj_type (h_obj h) = VMO"
  shows "(vmo_write pid hid content s = Some s') \<longleftrightarrow>
         (ZX_RIGHT_WRITE \<in> h_rights h \<and>
          s' = s\<lparr> vmo_store :=
            (vmo_store s)(obj_id (h_obj h) \<mapsto> content) \<rparr>)"
  using assms by (auto simp: vmo_write_def)

lemma vmo_write_updates_only_with_write_right:
  assumes "vmo_write pid hid content s = Some s'"
  shows "\<exists>h. lookup_handle pid hid s = Some h \<and>
             obj_type (h_obj h) = VMO \<and>
             ZX_RIGHT_WRITE \<in> h_rights h \<and>
             vmo_store s' = (vmo_store s)(obj_id (h_obj h) \<mapsto> content)"
  using assms by (auto simp: vmo_write_def split: option.splits if_splits)

subsubsection \<open>Сценарий истинен\<close>

lemma example_scenario_true:
  "example_scenario"
  unfolding example_scenario_def example_channel_rights_def
            empty_state_def init_process_def create_channel_pair_def
            create_vmo_def transfer_via_channel_def zx_channel_write_def
            zx_channel_read_def alloc_hid_def set_table_def get_table_def
            lookup_handle_def reduce_rights_def reduce_rights_wf_def
            close_rights_def rights_wf_def
            vmo_write_def vmo_content_def Let_def
  by simp

text \<open>
  \<^bold>\<open>Лемма @{text example_empty_rights_ok_true}.\<close>
  Передача с запросом @{term "{}"} допустима: получатель получает handle на
  тот же объект с пустой маской; @{text vmo_write} по-прежнему отказ;
  move у отправителя сохраняется. Пустая маска~--- результат сокращения
  и допустимое состояние handle; сам факт передачи по-прежнему требует
  @{text TRANSFER} у источника. Это отделяет no-escalation / integrity от
  старого правила \<guillemotleft>пустая маска $\Rightarrow$ отказ транзакции\<guillemotright>.
\<close>

definition example_empty_rights_ok :: bool where
  "example_empty_rights_ok =
    (let s0 = init_process 1 (init_process 0 empty_state);
         rights_a = {ZX_RIGHT_READ, ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER}
     in case create_channel_pair 0 1 example_channel_rights example_channel_rights s0 of
          None \<Rightarrow> False
        | Some (ch0, ch1, _, s1) \<Rightarrow>
            (case create_vmo 0 rights_a 42 s1 of
               None \<Rightarrow> False
             | Some (hid_a, oid, s2) \<Rightarrow>
                 (case transfer_via_channel 0 1 ch0 ch1 hid_a {} s2 of
                    None \<Rightarrow> False
                  | Some (hid_b, s3) \<Rightarrow>
                      (case lookup_handle 1 hid_b s3 of
                         None \<Rightarrow> False
                       | Some h_b \<Rightarrow>
                           h_rights h_b = {} \<and>
                           obj_id (h_obj h_b) = oid \<and>
                           lookup_handle 0 hid_a s3 = None \<and>
                           vmo_write 1 hid_b 99 s3 = None \<and>
                           vmo_content oid s3 = Some 42))))"

lemma example_empty_rights_ok_true:
  "example_empty_rights_ok"
  unfolding example_empty_rights_ok_def example_channel_rights_def
            empty_state_def init_process_def create_channel_pair_def
            create_vmo_def transfer_via_channel_def zx_channel_write_def
            zx_channel_read_def alloc_hid_def set_table_def get_table_def
            lookup_handle_def reduce_rights_def reduce_rights_wf_def
            close_rights_def rights_wf_def
            vmo_write_def vmo_content_def Let_def
  by simp

end
