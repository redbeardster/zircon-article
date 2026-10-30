module Zircon : sig
  type nat
  type right
  type num
  type 'a set
  type kernel_obj_type
  type 'a kernel_obj_ext
  type 'a handle_ext
  type 'a system_state_ext
  val lookup_handle :
    nat -> nat -> unit system_state_ext -> unit handle_ext option
  val vmo_write :
    nat -> nat -> nat -> unit system_state_ext -> unit system_state_ext option
  val create_vmo :
    nat ->
      right set ->
        nat ->
          unit system_state_ext -> (nat * (nat * unit system_state_ext)) option
  val empty_state : unit system_state_ext
  val vmo_content : nat -> unit system_state_ext -> nat option
  val init_process : nat -> unit system_state_ext -> unit system_state_ext
  val zx_channel_read :
    nat -> nat -> unit system_state_ext -> (nat * unit system_state_ext) option
  val zx_handle_close :
    nat -> nat -> unit system_state_ext -> unit system_state_ext option
  val example_channel_rights : right set
  val zx_channel_write :
    nat ->
      nat ->
        nat ->
          right set -> unit system_state_ext -> unit system_state_ext option
  val transfer_via_channel :
    nat ->
      nat ->
        nat ->
          nat ->
            nat ->
              right set ->
                unit system_state_ext -> (nat * unit system_state_ext) option
  val create_channel_pair :
    nat ->
      nat ->
        right set ->
          right set ->
            unit system_state_ext ->
              (nat * (nat * (nat * unit system_state_ext))) option
  val example_scenario : bool
  val example_setup : unit system_state_ext
  val zx_handle_duplicate :
    nat ->
      nat ->
        right set ->
          unit system_state_ext -> (nat * unit system_state_ext) option
  val example_rights_a : right set
  val example_exec_ok : bool
  val example_empty_rights_ok : bool
  val example_empty_exec_ok : bool
end = struct

type nat = Nat of Z.t;;

let rec integer_of_nat (Nat x) = x;;

let rec equal_nata m n = Z.equal (integer_of_nat m) (integer_of_nat n);;

type 'a equal = {equal : 'a -> 'a -> bool};;
let equal _A = _A.equal;;

let equal_nat = ({equal = equal_nata} : nat equal);;

let rec equal_bool p pa = match p, pa with p, true -> p
                     | p, false -> not p
                     | true, p -> p
                     | false, p -> not p;;

type char = Chara of bool * bool * bool * bool * bool * bool * bool * bool;;

let rec equal_chara
  (Chara (x1, x2, x3, x4, x5, x6, x7, x8))
    (Chara (y1, y2, y3, y4, y5, y6, y7, y8)) =
    equal_bool x1 y1 &&
      (equal_bool x2 y2 &&
        (equal_bool x3 y3 &&
          (equal_bool x4 y4 &&
            (equal_bool x5 y5 &&
              (equal_bool x6 y6 && (equal_bool x7 y7 && equal_bool x8 y8))))));;

let equal_char = ({equal = equal_chara} : char equal);;

type right = ZX_RIGHT_READ | ZX_RIGHT_WRITE | ZX_RIGHT_EXECUTE | ZX_RIGHT_MAP |
  ZX_RIGHT_TRANSFER | ZX_RIGHT_DUPLICATE | ZX_RIGHT_SIGNAL;;

let rec equal_righta
  x0 x1 = match x0, x1 with ZX_RIGHT_DUPLICATE, ZX_RIGHT_SIGNAL -> false
    | ZX_RIGHT_SIGNAL, ZX_RIGHT_DUPLICATE -> false
    | ZX_RIGHT_TRANSFER, ZX_RIGHT_SIGNAL -> false
    | ZX_RIGHT_SIGNAL, ZX_RIGHT_TRANSFER -> false
    | ZX_RIGHT_TRANSFER, ZX_RIGHT_DUPLICATE -> false
    | ZX_RIGHT_DUPLICATE, ZX_RIGHT_TRANSFER -> false
    | ZX_RIGHT_MAP, ZX_RIGHT_SIGNAL -> false
    | ZX_RIGHT_SIGNAL, ZX_RIGHT_MAP -> false
    | ZX_RIGHT_MAP, ZX_RIGHT_DUPLICATE -> false
    | ZX_RIGHT_DUPLICATE, ZX_RIGHT_MAP -> false
    | ZX_RIGHT_MAP, ZX_RIGHT_TRANSFER -> false
    | ZX_RIGHT_TRANSFER, ZX_RIGHT_MAP -> false
    | ZX_RIGHT_EXECUTE, ZX_RIGHT_SIGNAL -> false
    | ZX_RIGHT_SIGNAL, ZX_RIGHT_EXECUTE -> false
    | ZX_RIGHT_EXECUTE, ZX_RIGHT_DUPLICATE -> false
    | ZX_RIGHT_DUPLICATE, ZX_RIGHT_EXECUTE -> false
    | ZX_RIGHT_EXECUTE, ZX_RIGHT_TRANSFER -> false
    | ZX_RIGHT_TRANSFER, ZX_RIGHT_EXECUTE -> false
    | ZX_RIGHT_EXECUTE, ZX_RIGHT_MAP -> false
    | ZX_RIGHT_MAP, ZX_RIGHT_EXECUTE -> false
    | ZX_RIGHT_WRITE, ZX_RIGHT_SIGNAL -> false
    | ZX_RIGHT_SIGNAL, ZX_RIGHT_WRITE -> false
    | ZX_RIGHT_WRITE, ZX_RIGHT_DUPLICATE -> false
    | ZX_RIGHT_DUPLICATE, ZX_RIGHT_WRITE -> false
    | ZX_RIGHT_WRITE, ZX_RIGHT_TRANSFER -> false
    | ZX_RIGHT_TRANSFER, ZX_RIGHT_WRITE -> false
    | ZX_RIGHT_WRITE, ZX_RIGHT_MAP -> false
    | ZX_RIGHT_MAP, ZX_RIGHT_WRITE -> false
    | ZX_RIGHT_WRITE, ZX_RIGHT_EXECUTE -> false
    | ZX_RIGHT_EXECUTE, ZX_RIGHT_WRITE -> false
    | ZX_RIGHT_READ, ZX_RIGHT_SIGNAL -> false
    | ZX_RIGHT_SIGNAL, ZX_RIGHT_READ -> false
    | ZX_RIGHT_READ, ZX_RIGHT_DUPLICATE -> false
    | ZX_RIGHT_DUPLICATE, ZX_RIGHT_READ -> false
    | ZX_RIGHT_READ, ZX_RIGHT_TRANSFER -> false
    | ZX_RIGHT_TRANSFER, ZX_RIGHT_READ -> false
    | ZX_RIGHT_READ, ZX_RIGHT_MAP -> false
    | ZX_RIGHT_MAP, ZX_RIGHT_READ -> false
    | ZX_RIGHT_READ, ZX_RIGHT_EXECUTE -> false
    | ZX_RIGHT_EXECUTE, ZX_RIGHT_READ -> false
    | ZX_RIGHT_READ, ZX_RIGHT_WRITE -> false
    | ZX_RIGHT_WRITE, ZX_RIGHT_READ -> false
    | ZX_RIGHT_SIGNAL, ZX_RIGHT_SIGNAL -> true
    | ZX_RIGHT_DUPLICATE, ZX_RIGHT_DUPLICATE -> true
    | ZX_RIGHT_TRANSFER, ZX_RIGHT_TRANSFER -> true
    | ZX_RIGHT_MAP, ZX_RIGHT_MAP -> true
    | ZX_RIGHT_EXECUTE, ZX_RIGHT_EXECUTE -> true
    | ZX_RIGHT_WRITE, ZX_RIGHT_WRITE -> true
    | ZX_RIGHT_READ, ZX_RIGHT_READ -> true;;

let equal_right = ({equal = equal_righta} : right equal);;

type 'a ord = {less_eq : 'a -> 'a -> bool; less : 'a -> 'a -> bool};;
let less_eq _A = _A.less_eq;;
let less _A = _A.less;;

let ord_integer = ({less_eq = Z.leq; less = Z.lt} : Z.t ord);;

type num = One | Bit0 of num | Bit1 of num;;

type 'a set = Set of 'a list | Coset of 'a list;;

type kernel_obj_type = Process | Thread | Channel | VMO | Hardware |
  Other_Obj of char list;;

type 'a kernel_obj_ext = Kernel_obj_ext of kernel_obj_type * nat * 'a;;

type 'a handle_ext = Handle_ext of unit kernel_obj_ext * right set * 'a;;

type 'a system_state_ext =
  System_state_ext of
    (nat -> (nat -> unit handle_ext option) option) * (nat -> nat option) *
      (nat -> (unit handle_ext list) option) * (nat -> nat option) *
      (nat -> nat option) * nat * 'a;;

let rec eq _A a b = equal _A a b;;

let rec plus_nat m n = Nat (Z.add (integer_of_nat m) (integer_of_nat n));;

let one_nat : nat = Nat (Z.of_int 1);;

let rec suc n = plus_nat n one_nat;;

let rec fold f x1 s = match f, x1, s with f, x :: xs, s -> fold f xs (f x s)
               | f, [], s -> s;;

let rec removeAll _A
  x xa1 = match x, xa1 with x, [] -> []
    | x, y :: xs ->
        (if eq _A x y then removeAll _A x xs else y :: removeAll _A x xs);;

let rec membera _A x0 y = match x0, y with [], y -> false
                     | x :: xs, y -> eq _A x y || membera _A xs y;;

let rec inserta _A x xs = (if membera _A xs x then xs else x :: xs);;

let rec insert _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (removeAll _A x xs)
    | x, Set xs -> Set (inserta _A x xs);;

let rec member _A
  x xa1 = match x, xa1 with x, Coset xs -> not (membera _A xs x)
    | x, Set xs -> membera _A xs x;;

let rec remove _A
  x xa1 = match x, xa1 with x, Coset xs -> Coset (inserta _A x xs)
    | x, Set xs -> Set (removeAll _A x xs);;

let rec fun_upd _A f a b = (fun x -> (if eq _A x a then b else f x));;

let rec filter
  p x1 = match p, x1 with p, [] -> []
    | p, x :: xs -> (if p x then x :: filter p xs else filter p xs);;

let rec is_none = function Some x -> false
                  | None -> true;;

let rec next_hids_update
  next_hidsa
    (System_state_ext
      (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
        more))
    = System_state_ext
        (proc_tables, next_hidsa next_hids, channels, channel_peer, vmo_store,
          next_obj_id, more);;

let rec next_hids
  (System_state_ext
    (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
      more))
    = next_hids;;

let rec alloc_hid
  pid s =
    (let hid = (match next_hids s pid with None -> one_nat | Some n -> n) in
     let a =
       next_hids_update
         (fun _ -> fun_upd equal_nat (next_hids s) pid (Some (suc hid))) s
       in
      (hid, a));;

let rec proc_tables
  (System_state_ext
    (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
      more))
    = proc_tables;;

let rec get_table pid s = proc_tables s pid;;

let rec rights_wf
  r = (if member equal_right ZX_RIGHT_WRITE r
        then member equal_right ZX_RIGHT_READ r else true) &&
        (if member equal_right ZX_RIGHT_EXECUTE r
          then member equal_right ZX_RIGHT_READ r else true);;

let rec proc_tables_update
  proc_tablesa
    (System_state_ext
      (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
        more))
    = System_state_ext
        (proc_tablesa proc_tables, next_hids, channels, channel_peer, vmo_store,
          next_obj_id, more);;

let rec set_table
  pid ht s =
    proc_tables_update
      (fun _ -> fun_upd equal_nat (proc_tables s) pid (Some ht)) s;;

let rec equal_list _A
  x0 x1 = match x0, x1 with [], x21 :: x22 -> false
    | x21 :: x22, [] -> false
    | x21 :: x22, y21 :: y22 -> eq _A x21 y21 && equal_list _A x22 y22
    | [], [] -> true;;

let rec equal_kernel_obj_type
  x0 x1 = match x0, x1 with Hardware, Other_Obj x6 -> false
    | Other_Obj x6, Hardware -> false
    | VMO, Other_Obj x6 -> false
    | Other_Obj x6, VMO -> false
    | VMO, Hardware -> false
    | Hardware, VMO -> false
    | Channel, Other_Obj x6 -> false
    | Other_Obj x6, Channel -> false
    | Channel, Hardware -> false
    | Hardware, Channel -> false
    | Channel, VMO -> false
    | VMO, Channel -> false
    | Thread, Other_Obj x6 -> false
    | Other_Obj x6, Thread -> false
    | Thread, Hardware -> false
    | Hardware, Thread -> false
    | Thread, VMO -> false
    | VMO, Thread -> false
    | Thread, Channel -> false
    | Channel, Thread -> false
    | Process, Other_Obj x6 -> false
    | Other_Obj x6, Process -> false
    | Process, Hardware -> false
    | Hardware, Process -> false
    | Process, VMO -> false
    | VMO, Process -> false
    | Process, Channel -> false
    | Channel, Process -> false
    | Process, Thread -> false
    | Thread, Process -> false
    | Other_Obj x6, Other_Obj y6 -> equal_list equal_char x6 y6
    | Hardware, Hardware -> true
    | VMO, VMO -> true
    | Channel, Channel -> true
    | Thread, Thread -> true
    | Process, Process -> true;;

let rec vmo_store_update
  vmo_storea
    (System_state_ext
      (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
        more))
    = System_state_ext
        (proc_tables, next_hids, channels, channel_peer, vmo_storea vmo_store,
          next_obj_id, more);;

let rec vmo_store
  (System_state_ext
    (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
      more))
    = vmo_store;;

let rec obj_type (Kernel_obj_ext (obj_type, obj_id, more)) = obj_type;;

let rec obj_id (Kernel_obj_ext (obj_type, obj_id, more)) = obj_id;;

let rec h_rights (Handle_ext (h_obj, h_rights, more)) = h_rights;;

let rec lookup_handle
  pid hid s = (match proc_tables s pid with None -> None | Some ht -> ht hid);;

let rec h_obj (Handle_ext (h_obj, h_rights, more)) = h_obj;;

let rec vmo_write
  pid hid content s =
    (match lookup_handle pid hid s with None -> None
      | Some h ->
        (if not (equal_kernel_obj_type (obj_type (h_obj h)) VMO) then None
          else (if not (member equal_right ZX_RIGHT_WRITE (h_rights h))
                 then None
                 else Some (vmo_store_update
                             (fun _ ->
                               fun_upd equal_nat (vmo_store s)
                                 (obj_id (h_obj h)) (Some content))
                             s))));;

let rec next_obj_id_update
  next_obj_ida
    (System_state_ext
      (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
        more))
    = System_state_ext
        (proc_tables, next_hids, channels, channel_peer, vmo_store,
          next_obj_ida next_obj_id, more);;

let rec next_obj_id
  (System_state_ext
    (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
      more))
    = next_obj_id;;

let rec create_vmo
  pid initial_rights content s =
    (match get_table pid s with None -> None
      | Some ht ->
        (if not (rights_wf initial_rights) then None
          else (let oid = next_obj_id s in
                let obj = Kernel_obj_ext (VMO, oid, ()) in
                let h = Handle_ext (obj, initial_rights, ()) in
                let (hid, s1) = alloc_hid pid s in
                let hta = fun_upd equal_nat ht hid (Some h) in
                let s2 = set_table pid hta s1 in
                let s3 =
                  next_obj_id_update (fun _ -> suc oid)
                    (vmo_store_update
                      (fun _ ->
                        fun_upd equal_nat (vmo_store s2) oid (Some content))
                      s2)
                  in
                 Some (hid, (oid, s3)))));;

let rec list_all p x1 = match p, x1 with p, [] -> true
                   | p, x :: xs -> p x && list_all p xs;;

let zero_nat : nat = Nat Z.zero;;

let empty_state : unit system_state_ext
  = System_state_ext
      ((fun _ -> None), (fun _ -> None), (fun _ -> None), (fun _ -> None),
        (fun _ -> None), zero_nat, ());;

let rec vmo_content oid s = vmo_store s oid;;

let rec close_rights
  r = (if member equal_right ZX_RIGHT_WRITE r ||
            member equal_right ZX_RIGHT_EXECUTE r
        then insert equal_right ZX_RIGHT_READ r else r);;

let rec init_process
  pid s =
    next_hids_update
      (fun _ -> fun_upd equal_nat (next_hids s) pid (Some one_nat))
      (proc_tables_update
        (fun _ -> fun_upd equal_nat (proc_tables s) pid (Some (fun _ -> None)))
        s);;

let rec inf_set _A
  a x1 = match a, x1 with a, Coset xs -> fold (remove _A) xs a
    | a, Set xs -> Set (filter (fun x -> member _A x a) xs);;

let rec reduce_rights
  new_rights old_rights = inf_set equal_right new_rights old_rights;;

let rec channels_update
  channelsa
    (System_state_ext
      (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
        more))
    = System_state_ext
        (proc_tables, next_hids, channelsa channels, channel_peer, vmo_store,
          next_obj_id, more);;

let rec channels
  (System_state_ext
    (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
      more))
    = channels;;

let rec zx_channel_read
  pid ch_hid s =
    (match (lookup_handle pid ch_hid s, get_table pid s) with (None, _) -> None
      | (Some _, None) -> None
      | (Some h_ch, Some ht) ->
        (if not (equal_kernel_obj_type (obj_type (h_obj h_ch)) Channel)
          then None
          else (if not (member equal_right ZX_RIGHT_READ (h_rights h_ch))
                 then None
                 else (match channels s (obj_id (h_obj h_ch)) with None -> None
                        | Some [] -> None
                        | Some (cap :: rest) ->
                          (let oid = obj_id (h_obj h_ch) in
                           let (hid, s1) = alloc_hid pid s in
                           let hta = fun_upd equal_nat ht hid (Some cap) in
                           let s2 = set_table pid hta s1 in
                           let s3 =
                             channels_update
                               (fun _ ->
                                 fun_upd equal_nat (channels s2) oid
                                   (Some rest))
                               s2
                             in
                            Some (hid, s3))))));;

let rec zx_handle_close
  pid hid s =
    (match (lookup_handle pid hid s, get_table pid s) with (None, _) -> None
      | (Some _, None) -> None
      | (Some _, Some ht) ->
        Some (set_table pid (fun_upd equal_nat ht hid None) s));;

let rec max _A a b = (if less_eq _A a b then b else a);;

let rec equal_option _A x0 x1 = match x0, x1 with None, Some x2 -> false
                          | Some x2, None -> false
                          | Some x2, Some y2 -> eq _A x2 y2
                          | None, None -> true;;

let bot_set : 'a set = Set [];;

let example_channel_rights : right set
  = insert equal_right ZX_RIGHT_READ
      (insert equal_right ZX_RIGHT_WRITE bot_set);;

let rec channel_peer
  (System_state_ext
    (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
      more))
    = channel_peer;;

let rec less_eq_set _A
  a b = match a, b with Coset [], Set [] -> false
    | a, Coset ys -> list_all (fun y -> not (member _A y a)) ys
    | Set xs, b -> list_all (fun x -> member _A x b) xs;;

let rec reduce_rights_wf req src = close_rights (reduce_rights req src);;

let rec zx_channel_write
  pid ch_hid pay_hid req_rights s =
    (match
      (lookup_handle pid ch_hid s,
        (lookup_handle pid pay_hid s, get_table pid s))
      with (None, _) -> None | (Some _, (None, _)) -> None
      | (Some _, (Some _, None)) -> None
      | (Some h_ch, (Some h_pay, Some ht)) ->
        (if equal_nata ch_hid pay_hid then None
          else (if not (equal_kernel_obj_type (obj_type (h_obj h_ch)) Channel)
                 then None
                 else (if not (member equal_right ZX_RIGHT_WRITE
                                (h_rights h_ch))
                        then None
                        else (if not (member equal_right ZX_RIGHT_TRANSFER
                                       (h_rights h_pay))
                               then None
                               else (if not
  (less_eq_set equal_right req_rights (h_rights h_pay))
                                      then None
                                      else (match
     channel_peer s (obj_id (h_obj h_ch)) with None -> None
     | Some peer ->
       (match channels s peer with None -> None
         | Some q ->
           (let actual = reduce_rights_wf req_rights (h_rights h_pay) in
            let cap = Handle_ext (h_obj h_pay, actual, ()) in
            let hta = fun_upd equal_nat ht pay_hid None in
            let s1 = set_table pid hta s in
            let a =
              channels_update
                (fun _ ->
                  fun_upd equal_nat (channels s1) peer (Some (q @ [cap])))
                s1
              in
             Some a)))))))));;

let rec transfer_via_channel
  src dst src_ch dst_ch pay_hid req_rights s =
    (match (lookup_handle src src_ch s, lookup_handle dst dst_ch s)
      with (None, _) -> None | (Some _, None) -> None
      | (Some h_src_ch, Some h_dst_ch) ->
        (if not (equal_kernel_obj_type (obj_type (h_obj h_src_ch)) Channel) ||
              not (equal_kernel_obj_type (obj_type (h_obj h_dst_ch)) Channel)
          then None
          else (if not (equal_option equal_nat
                         (channel_peer s (obj_id (h_obj h_src_ch)))
                         (Some (obj_id (h_obj h_dst_ch))))
                 then None
                 else (match channels s (obj_id (h_obj h_dst_ch))
                        with None -> None
                        | Some [] ->
                          (match
                            zx_channel_write src src_ch pay_hid req_rights s
                            with None -> None
                            | Some a -> zx_channel_read dst dst_ch a)
                        | Some (_ :: _) -> None))));;

let rec nat_of_integer k = Nat (max ord_integer Z.zero k);;

let rec channel_peer_update
  channel_peera
    (System_state_ext
      (proc_tables, next_hids, channels, channel_peer, vmo_store, next_obj_id,
        more))
    = System_state_ext
        (proc_tables, next_hids, channels, channel_peera channel_peer,
          vmo_store, next_obj_id, more);;

let rec create_channel_pair
  pid0 pid1 rights0 rights1 s =
    (match get_table pid0 s with None -> None
      | Some ht0 ->
        (match get_table pid1 s with None -> None
          | Some _ ->
            (if not (rights_wf rights0) || not (rights_wf rights1) then None
              else (let oid0 = next_obj_id s in
                    let oid1 = suc oid0 in
                    let obj0 = Kernel_obj_ext (Channel, oid0, ()) in
                    let obj1 = Kernel_obj_ext (Channel, oid1, ()) in
                    let h0 = Handle_ext (obj0, rights0, ()) in
                    let h1 = Handle_ext (obj1, rights1, ()) in
                    let (hid0, s1) = alloc_hid pid0 s in
                    let s2 =
                      set_table pid0 (fun_upd equal_nat ht0 hid0 (Some h0)) s1
                      in
                    let (hid1, s3) = alloc_hid pid1 s2 in
                     (match get_table pid1 s3 with None -> None
                       | Some ht1 ->
                         (let s4 =
                            set_table pid1
                              (fun_upd equal_nat ht1 hid1 (Some h1)) s3
                            in
                          let s5 =
                            next_obj_id_update (fun _ -> suc oid1)
                              (channel_peer_update
                                (fun _ ->
                                  fun_upd equal_nat
                                    (fun_upd equal_nat (channel_peer s4) oid0
                                      (Some oid1))
                                    oid1 (Some oid0))
                                (channels_update
                                  (fun _ ->
                                    fun_upd equal_nat
                                      (fun_upd equal_nat (channels s4) oid0
(Some []))
                                      oid1 (Some []))
                                  s4))
                            in
                           Some (hid0, (hid1, (oid0, s5)))))))));;

let example_scenario : bool
  = (let s0 = init_process one_nat (init_process zero_nat empty_state) in
     let rights_a =
       insert equal_right ZX_RIGHT_READ
         (insert equal_right ZX_RIGHT_WRITE
           (insert equal_right ZX_RIGHT_TRANSFER bot_set))
       in
      (match
        create_channel_pair zero_nat one_nat example_channel_rights
          example_channel_rights s0
        with None -> false
        | Some (ch0, (ch1, (_, s1))) ->
          (match create_vmo zero_nat rights_a (nat_of_integer (Z.of_int 42)) s1
            with None -> false
            | Some (hid_a, (oid, s2)) ->
              (match
                transfer_via_channel zero_nat one_nat ch0 ch1 hid_a
                  (insert equal_right ZX_RIGHT_READ bot_set) s2
                with None -> false
                | Some (hid_b, s3) ->
                  (match lookup_handle one_nat hid_b s3 with None -> false
                    | Some h_b ->
                      member equal_right ZX_RIGHT_READ (h_rights h_b) &&
                        (not (member equal_right ZX_RIGHT_WRITE
                               (h_rights h_b)) &&
                          (equal_nata (obj_id (h_obj h_b)) oid &&
                            (is_none (lookup_handle zero_nat hid_a s3) &&
                              (is_none
                                 (vmo_write one_nat hid_b
                                   (nat_of_integer (Z.of_int 99)) s3) &&
                                equal_option equal_nat (vmo_content oid s3)
                                  (Some (nat_of_integer
  (Z.of_int 42))))))))))));;

let example_setup : unit system_state_ext
  = init_process one_nat (init_process zero_nat empty_state);;

let rec h_rights_update
  h_rightsa (Handle_ext (h_obj, h_rights, more)) =
    Handle_ext (h_obj, h_rightsa h_rights, more);;

let rec zx_handle_duplicate
  pid hid req_rights s =
    (match (lookup_handle pid hid s, get_table pid s) with (None, _) -> None
      | (Some _, None) -> None
      | (Some h, Some ht) ->
        (if not (member equal_right ZX_RIGHT_DUPLICATE (h_rights h)) then None
          else (if not (less_eq_set equal_right req_rights (h_rights h))
                 then None
                 else (let actual = reduce_rights_wf req_rights (h_rights h) in
                       let ha = h_rights_update (fun _ -> actual) h in
                       let (hida, s1) = alloc_hid pid s in
                        Some (hida,
                               set_table pid
                                 (fun_upd equal_nat ht hida (Some ha)) s1)))));;

let example_rights_a : right set
  = insert equal_right ZX_RIGHT_READ
      (insert equal_right ZX_RIGHT_WRITE
        (insert equal_right ZX_RIGHT_TRANSFER bot_set));;

let example_exec_ok : bool
  = (match
      create_channel_pair zero_nat one_nat example_channel_rights
        example_channel_rights example_setup
      with None -> false
      | Some (ch0, (ch1, (_, s1))) ->
        (match
          create_vmo zero_nat example_rights_a (nat_of_integer (Z.of_int 42)) s1
          with None -> false
          | Some (hid_a, (oid, s2)) ->
            (match
              transfer_via_channel zero_nat one_nat ch0 ch1 hid_a
                (insert equal_right ZX_RIGHT_READ bot_set) s2
              with None -> false
              | Some (hid_b, s3) ->
                is_none (lookup_handle zero_nat hid_a s3) &&
                  (is_none
                     (vmo_write one_nat hid_b (nat_of_integer (Z.of_int 99))
                       s3) &&
                    equal_option equal_nat (vmo_content oid s3)
                      (Some (nat_of_integer (Z.of_int 42)))))));;

let rec equal_set _A a b = less_eq_set _A a b && less_eq_set _A b a;;

let example_empty_rights_ok : bool
  = (let s0 = init_process one_nat (init_process zero_nat empty_state) in
     let rights_a =
       insert equal_right ZX_RIGHT_READ
         (insert equal_right ZX_RIGHT_WRITE
           (insert equal_right ZX_RIGHT_TRANSFER bot_set))
       in
      (match
        create_channel_pair zero_nat one_nat example_channel_rights
          example_channel_rights s0
        with None -> false
        | Some (ch0, (ch1, (_, s1))) ->
          (match create_vmo zero_nat rights_a (nat_of_integer (Z.of_int 42)) s1
            with None -> false
            | Some (hid_a, (oid, s2)) ->
              (match
                transfer_via_channel zero_nat one_nat ch0 ch1 hid_a bot_set s2
                with None -> false
                | Some (hid_b, s3) ->
                  (match lookup_handle one_nat hid_b s3 with None -> false
                    | Some h_b ->
                      equal_set equal_right (h_rights h_b) bot_set &&
                        (equal_nata (obj_id (h_obj h_b)) oid &&
                          (is_none (lookup_handle zero_nat hid_a s3) &&
                            (is_none
                               (vmo_write one_nat hid_b
                                 (nat_of_integer (Z.of_int 99)) s3) &&
                              equal_option equal_nat (vmo_content oid s3)
                                (Some (nat_of_integer (Z.of_int 42)))))))))));;

let example_empty_exec_ok : bool = example_empty_rights_ok;;

end;; (*struct Zircon*)
