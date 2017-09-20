
(** {1 Modular Term Structure} *)

open Solver_types

module Fields = Term_fields

type view = term_view = ..
type t = term
type tc = tc_term

let[@inline] id t = t.t_id
let[@inline] view t = t.t_view
let[@inline] equal t u = t.t_id = u.t_id
let[@inline] compare t u = CCInt.compare t.t_id u.t_id
let[@inline] hash t = CCHash.int t.t_id
let[@inline] pp out (t:t): unit = t.t_tc.tct_pp out t.t_view
let[@inline] field_get f t = Fields.get f t.t_fields
let[@inline] field_set f t = t.t_fields <- Fields.set f true t.t_fields
let[@inline] field_clear f t = t.t_fields <- Fields.set f false t.t_fields

(* store plugin id at 4 lowest bits *)
let plugin_id_width = 4

(* bitmask *)
let p_mask = (1 lsl plugin_id_width) - 1

let[@inline] plugin_id t : int = id t land p_mask
let[@inline] plugin_specific_id t : int = id t lsr plugin_id_width
let[@inline] weight t = t.t_weight
let[@inline] set_weight t f = t.t_weight <- f
let[@inline] is_deleted t = field_get field_t_is_deleted t
let[@inline] is_added t = field_get field_t_is_added t
let[@inline] var t = t.t_var
let[@inline] ty t = t.t_ty
let[@inline] iter_subterms (t:term): term Sequence.t = t.t_tc.tct_subterms t.t_view
let[@inline] is_bool t = Type.is_bool t.t_ty
let[@inline] subterms t : t list = iter_subterms t |> Sequence.to_list
let[@inline] level t = match t.t_value with
  | TA_none -> -1
  | TA_assign {level;_} -> level

let[@inline] gc_marked (t:t) : bool = field_get field_t_gc_marked t
let[@inline] gc_unmark (t:t) : unit = field_clear field_t_gc_marked t
let[@inline] gc_mark (t:t) : unit = field_set field_t_gc_marked t

let[@inline] dirty (t:t): bool = field_get field_t_dirty t
let[@inline] dirty_unmark (t:t) : unit = field_clear field_t_dirty t
let[@inline] dirty_mark (t:t) : unit = field_set field_t_dirty t

let[@inline] value (t:t): term_assignment = t.t_value
let[@inline] value_exn (t:t): value = match t.t_value with
  | TA_none -> assert false
  | TA_assign {value;_} -> value
let[@inline] has_value (t:t): bool = match t.t_value with
  | TA_none -> false
  | TA_assign _ -> true

let[@inline] max_level l1 l2 =
  if l1<0 || l2<0 then -1
  else max l1 l2

(* max level of arguments *)
let[@inline] level_sub_aux ~f (t:t) : level =
  let res = ref 0 in
  iter_subterms t
    (fun u ->
       let lev = level u in
       res := f !res lev);
  !res

let[@inline] level_semantic (t:t) : level = level_sub_aux ~f:max_level t
let[@inline] level_sub (t:t) : level = level_sub_aux ~f:max t

let[@inline] mk_eq (t:t) (u:t) : t = Type.mk_eq (ty t) t u

let[@inline] reason_exn t = match value t with
  | TA_assign{reason;_} -> reason
  | TA_none -> assert false

let[@inline] reason t = match value t with
  | TA_none -> None
  | TA_assign{reason;_} -> Some reason

let[@inline] recompute_state (lvl:level) (t:t) : unit =
  Type.refresh_state (ty t) lvl t

let[@inline] decide_state_exn (t:t) : decide_state = match var t with
  | Var_semantic {v_decide_state=s;_} -> s
  | _ -> assert false

(** {2 Assignment view} *)

let[@inline] assigned (t:term): bool = match t.t_value with
  | TA_none -> false
  | TA_assign _ -> true

let[@inline] assignment (t:term) = match value t with
  | TA_assign {value=V_true;_} -> Some (A_bool (t,true))
  | TA_assign {value=V_false;_} -> Some (A_bool (t,false))
  | TA_assign {value;_} -> Some (A_semantic (t,value))
  | TA_none -> None

(** {2 Containers} *)

module As_key = struct
  type t = term
  let compare = compare
  let equal = equal
  let hash = hash
end
module Map = CCMap.Make(As_key)
module Tbl = CCHashtbl.Make(As_key)

(** {2 Low Level constructors. Use at your own risks.} *)
module Unsafe = struct
  let max_plugin_id = (1 lsl plugin_id_width) - 1

  let[@inline] mk_plugin_id (id:int): plugin_id =
    if id > max_plugin_id then (
      failwith "add_plugin: too many plugins";
    );
    id

  (* build a fresh term *)
  let[@inline never] make_term t_id t_view t_ty t_tc : t =
    let t_fields = Fields.empty in
    let t_weight = 0. in
    let t_idx = ~-1 in
    let t_watches = lazy (Vec.make_empty dummy_term) in
    { t_id; t_view; t_ty; t_fields; t_weight; t_idx;
      t_var=Var_none; t_value=TA_none; t_watches; t_tc; }
end

(* make a fresh variable for this term *)
let mk_var_ (t:t): var =
  if Type.is_bool t.t_ty then (
    let t_id_double = t.t_id lsl 1 in
    let pa = {
      a_term=t;
      a_watched = Vec.make 10 dummy_clause;
      a_id = t_id_double; (* aid = vid*2 *)
    } and na = {
        a_term=t;
        a_watched = Vec.make 10 dummy_clause;
        a_id = t_id_double + 1; (* aid = vid*2+1 *)
      } in
    Var_bool {pa; na}
  ) else (
    Var_semantic {
      v_decide_state=Type.mk_decide_state t.t_ty;
    }
  )

let[@inline] has_var t = match t.t_var with
  | Var_none -> false
  | Var_bool _
  | Var_semantic _ -> true

let[@inline] setup_var t =
  if not (has_var t) then (
    let v = mk_var_ t in
    t.t_var <- v;
    assert (has_var t);
  )

let[@inline] add_watch (t:t) (u:t) : unit =
  let lazy vec = t.t_watches in
  Vec.push vec u

let tc_mk
    ?(init=fun _ _ -> ())
    ?(update_watches=fun _ _ ~watch:_ -> Watch_keep)
    ?(delete=fun _ -> ())
    ?(subterms=fun _ _ -> ())
    ?(eval_bool=fun _ -> Eval_unknown)
    ?(map=fun t _ -> t)
    ~pp
    () : tc =
  { tct_init=init;
    tct_update_watches=update_watches;
    tct_delete=delete;
    tct_subterms=subterms;
    tct_pp=pp;
    tct_eval_bool=eval_bool;
    tct_map=map;
  }

let marked t = Term_fields.get field_t_seen t.t_fields
let mark t = t.t_fields <- Term_fields.set field_t_seen true t.t_fields
let unmark t = t.t_fields <- Term_fields.set field_t_seen false t.t_fields

module Bool = struct
  type t = bool_term

  let both_atoms_marked (t:t): bool =
    let seen_pos = Term_fields.get field_t_mark_pos t.t_fields in
    let seen_neg = Term_fields.get field_t_mark_neg t.t_fields in
    seen_pos && seen_neg

  let[@inline] assigned_atom t : atom option = match value t, var t with
    | TA_assign {value=V_true;_}, Var_bool{pa;_} -> Some pa
    | TA_assign {value=V_false;_}, Var_bool{na;_} -> Some na
    | _ -> None

  let[@inline] assigned_atom_exn t : atom = match value t, var t with
    | TA_assign {value=V_true;_}, Var_bool{pa;_} -> pa
    | TA_assign {value=V_false;_}, Var_bool{na;_} -> na
    | _ -> assert false

  let[@inline] is_true t = match value t with
    | TA_assign {value=V_true;_} -> true
    | _ -> false

  let[@inline] is_false t = match value t with
    | TA_assign {value=V_false;_} -> true
    | _ -> false

  let[@inline] pa_unsafe (t:t) : atom = match t.t_var with
    | Var_bool {pa; _} -> pa
    | _ -> assert false

  let[@inline] na_unsafe (t:t) : atom = match t.t_var with
    | Var_bool {na; _} -> na
    | _ -> assert false

  let[@inline] pa (t:t) : atom = setup_var t; pa_unsafe t
  let[@inline] na (t:t) : atom = setup_var t; na_unsafe t
  let[@inline] mk_neq t u = mk_eq t u |> na
  let[@inline] mk_eq t u = mk_eq t u |> pa
end

let[@inline] eval_bool (t:term) : eval_bool_res =
  assert (Type.is_bool t.t_ty);
  t.t_tc.tct_eval_bool t

let debug_no_val out t : unit =
  let state = if is_deleted t then "][D" else "" in
  Format.fprintf out "%a[%d%s]" pp t (id t) state

(* verbose debug printer *)
let debug out t : unit =
  let pp_val out = function
    | TA_none -> ()
    | TA_assign {value;level;_} ->
      Format.fprintf out "[@@%d@<1>→%a]" level Value.pp value
  in
  debug_no_val out t;
  pp_val out (value t)

(* find a term in [w] that is not assigned, or otherwise,
       the one with highest level
       @return index of term to watch, and [true] if all are assigned *)
let rec find_watch_ w i highest : int * bool =
  if i=Array.length w then highest, true
  else if has_value w.(i) then (
    let highest =
      if level w.(i) > level w.(highest) then i else highest
    in
    find_watch_ w (i+1) highest
  ) else i, false

module Watch1 = struct
  type t = term array
  let dummy = [||]
  let make = Array.of_list
  let[@inline] make_a a : t = a
  let[@inline] iter w k = if Array.length w>0 then k w.(0)

  let init w t ~on_all_set : unit =
    let i, all_set = find_watch_ w 0 0 in
    (* put watch first *)
    Util.swap_arr w i 0;
    add_watch w.(0) t;
    if all_set then (
      on_all_set ();
    );
    ()

  let update w t ~watch ~on_all_set : watch_res =
    (* find another watch. If none is present, keep the
       current one and call [on_all_set]. *)
    assert (w.(0) == watch);
    let i, all_set = find_watch_ w 0 0 in
    if all_set then (
      on_all_set ();
      Watch_keep (* just keep current watch *)
    ) else (
      (* use [i] as the watch *)
      assert (i>0);
      Util.swap_arr w i 0;
      add_watch w.(0) t;
      Watch_remove
    )
end

module Watch2 = struct
  type t = term array
  let dummy = [||]
  let make = Array.of_list
  let[@inline] make_a a : t = a

  let[@inline] iter w k =
    if Array.length w>0 then (
      k w.(0);
      if Array.length w>1 then k w.(1)
    )

  let[@inline] init w t ~on_unit ~on_all_set : unit =
    let i0, all_set0 = find_watch_ w 0 0 in
    Util.swap_arr w i0 0;
    let i1, all_set1 = find_watch_ w 1 0 in
    Util.swap_arr w i1 1;
    add_watch w.(0) t;
    add_watch w.(1) t;
    assert (if all_set0 then all_set1 else true);
    if all_set0 then (
      on_all_set ()
    ) else if all_set1 then (
      assert (not (has_value w.(0)));
      on_unit w.(0);
    );
    ()

  let update w t ~watch ~on_unit ~on_all_set : watch_res =
    (* find another watch. If none is present, keep the
       current ones and call [on_unit] or [on_all_set]. *)
    if w.(0) == watch then (
      (* ensure that if there is only one watch, it's the first *)
      Util.swap_arr w 0 1;
    ) else assert (w.(1) == watch);
    let i, all_set1 = find_watch_ w 1 0 in
    if all_set1 then (
      if has_value w.(0) then (
        on_all_set ();
      ) else (
        on_unit w.(0);
      );
      Watch_keep (* just keep current watch *)
    ) else (
      (* use [i] as the second watch *)
      assert (i>1);
      Util.swap_arr w i 1;
      add_watch w.(1) t;
      Watch_remove
    )
end

(** {2 Subst} *)

module Subst = struct
  type t = term_subst

  let empty = Int_map.empty

  let is_empty = Int_map.is_empty

  let[@inline] add s t u =
    assert (not (Int_map.mem t.t_id s));
    Int_map.add t.t_id (t,u) s

  let[@inline] mem s t = Int_map.mem t.t_id s

  let[@inline] find s t : term = Int_map.find t.t_id s |> snd

  (* TODO: investigate in storing normal form in a pointer in the term
     instead;
     rw_cache would then just be a vector of terms for which to clean
     the normal form *)

  type rw_cache = term Tbl.t lazy_t (* Maps terms to their normal form *)

  let mk_cache () : rw_cache = lazy (Tbl.create 32)

  (* applying a substitution to a term.
     Since terms in the codomain of the substitution are not normalized,
     we have to apply the substitution to them, too *)
  let apply ?(cache=mk_cache()) (subst:term_subst) (t:term) : term =
    if is_empty subst then t
    else (
      (* evaluate as a DAG *)
      let lazy cache = cache in
      let rec aux (t:term) : term = match Tbl.find cache t with
        | u -> u
        | exception Not_found ->
          let u = match find subst t with
            | u -> aux u
            | exception Not_found ->
              t.t_tc.tct_map t aux (* rewrite subterms *)
          in
          Tbl.add cache t u;
          u
      in
      aux t
    )

  let pp_ pp_t out (s:t) =
    if is_empty s then ()
    else (
      let pp_bind out (t,u) = Fmt.fprintf out "@[%a@ @<1>→ %a@]" pp_t t pp_t u in
      Fmt.fprintf out "{@[<hv>%a@]}"
        (Util.pp_seq ~sep:" , " pp_bind) (Int_map.values s)
    )

  let[@inline] pp out s = pp_ pp out s
  let[@inline] debug out s = pp_ debug out s
end

(** {2 Hashconsing of a Theory Terms} *)

module type TERM_ALLOC_OPS = sig
  val p_id : plugin_id (** ID of the theory *)
  val initial_size: int (** initial size of table *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
end

module type TERM_ALLOC = sig
  val make : view -> Type.t -> tc_term -> t (** Make a term of the theory *)
  val delete : t -> unit (** Delete a term of the theory *)
  val iter_terms : term Sequence.t (** All terms *)
  val gc_all : unit -> int (** GC all unmarked tems; unmark alive terms *)
end


module[@inline] Term_allocator(Ops : TERM_ALLOC_OPS) : TERM_ALLOC = struct
  module H = CCHashtbl.Make(struct
      type t = view
      include Ops
    end)
  let () = assert (Ops.p_id <= Unsafe.max_plugin_id)

  (* view -> term *)
  let tbl = H.create Ops.initial_size

  (* delete a term: flag it for removal, then recycle its ID.
     The flag is used so that anything that might still hold it can know
     it has been deleted. *)
  let delete (t:t) : unit =
    Log.debugf 5 (fun k->k "(@[<1>term.alloc.delete@ %a@])" debug t);
    t.t_fields <- Term_fields.set field_t_is_deleted true t.t_fields;
    t.t_tc.tct_delete t;
    t.t_value <- TA_none; (* unassign *)
    assert (plugin_id t = Ops.p_id);
    H.remove tbl (view t);
    ()

  (* obtain a fresh ID, unused by any other term *)
  let get_fresh_id : unit -> int =
    let id_alloc = ref 0 in
    fun () ->
      let n = !id_alloc in
      incr id_alloc;
      n

  (* build a fresh term *)
  let make_term_ t_view t_ty t_tc : t =
    let p_specific_id = get_fresh_id () in
    let t_id = Ops.p_id lor (p_specific_id lsl plugin_id_width) in
    Unsafe.make_term t_id t_view t_ty t_tc

  (* inline make function *)
  let[@inline] make (view:view) (ty:Type.t) (tc:tc_term) : t =
    try H.find tbl view
    with Not_found ->
      let t = make_term_ view ty tc in
      H.add tbl view t;
      t

  let[@inline] iter_terms k = H.values tbl k

  let gc_all () : int =
    Log.debugf 5 (fun k->k "(@[term.alloc.gc_all@ :p_id %d@])" Ops.p_id);
    let to_gc = Vec.make_empty dummy_term in (* terms to be collected *)
    let n_alive = ref 0 in
    (* collect *)
    H.values tbl
      (fun t ->
         if gc_marked t then (
           incr n_alive;
           gc_unmark t;
         ) else (
           Vec.push to_gc t
         ));
    (* delete *)
    let n_collected = Vec.size to_gc in
    Vec.iter delete to_gc;
    Log.debugf 15
      (fun k->k "(@[term.alloc.gc.stats@ :collected %d@ :alive %d@])"
          n_collected !n_alive);
    n_collected
end

