
(** {1 Modular Term Structure} *)

open Solver_types

module Fields = Term_fields

type view = term_view = ..
type t = term

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
let[@inline] level t = t.t_level
let[@inline] is_deleted t = field_get field_t_is_deleted t
let[@inline] var t = t.t_var
let[@inline] iter_subterms (t:term): term Sequence.t = t.t_tc.tct_subterms t
let[@inline] eval_bool (t:term) : eval_bool_res =
  assert (t.t_ty == Type.prop);
  t.t_tc.tct_eval_bool t

let[@inline] gc_marked (t:t) : bool = field_get field_t_gc_marked t
let[@inline] gc_unmark (t:t) : unit = field_clear field_t_gc_marked t
let[@inline] gc_mark (t:t) : unit = field_set field_t_gc_marked t

let rec gc_mark_rec (t:t) : unit =
  if not (gc_marked t) then (
    gc_mark t;
    iter_subterms t gc_mark_rec
  )

let[@inline] reason t = match var t with
  | Var_none -> None
  | Var_bool {b_value=(B_true r|B_false r); _} -> Some r
  | Var_semantic {v_value=V_assign {reason=r; _}; _} -> Some r
  | Var_bool _ | Var_semantic _ -> None

(** {2 Assignment view} *)

let[@inline] assigned (t:term): bool = match t.t_var with
  | Var_none -> false
  | Var_bool {b_value=(B_true _|B_false _); _} -> true
  | Var_bool {b_value=B_none; _} -> false
  | Var_semantic {v_value=V_assign _; _} -> true
  | Var_semantic {v_value=V_none; _} -> false

let[@inline] assignment (t:term) = match t.t_var with
  | Var_bool {b_value=(B_true _); _} -> Some (A_bool (t,true))
  | Var_bool {b_value=(B_false _); _} -> Some (A_bool (t,false))
  | Var_semantic {v_value=V_assign {value=v;_}; _} -> Some (A_semantic (t,v))
  | Var_none
  | Var_semantic {v_value=V_none; _}
  | Var_bool {b_value=B_none; _}
    -> None

(** {2 Low Level constructors. Use at your own risks.} *)
module Unsafe = struct
  let max_plugin_id = (1 lsl plugin_id_width) - 1

  let[@inline] mk_plugin_id (id:int): plugin_id =
    if id > max_plugin_id then (
      failwith "add_plugin: too many plugins";
    );
    id
end

(* make a fresh variable for this term *)
let mk_var_ (t:t): var =
  if Type.equal Type.prop t.t_ty then (
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
    Var_bool {pa; na; b_value=B_none}
  ) else (
    Var_semantic {
      v_value=V_none;
      v_watched=Vec.make_empty dummy_term;
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

let marked t = Term_fields.get field_t_seen t.t_fields
let mark t = t.t_fields <- Term_fields.set field_t_seen true t.t_fields
let unmark t = t.t_fields <- Term_fields.set field_t_seen false t.t_fields

module Bool = struct
  type t = bool_term

  let both_atoms_marked (t:t): bool =
    let seen_pos = Term_fields.get field_t_mark_pos t.t_fields in
    let seen_neg = Term_fields.get field_t_mark_neg t.t_fields in
    seen_pos && seen_neg

  let[@inline] assigned_atom t : atom option = match t.t_var with
    | Var_bool {pa; b_value=B_true _; _} -> Some pa
    | Var_bool {na; b_value=B_false _; _} -> Some na
    | _ -> None

  let[@inline] assigned_atom_exn t : atom = match t.t_var with
    | Var_bool {pa; b_value=B_true _; _} -> pa
    | Var_bool {na; b_value=B_false _; _} -> na
    | _ -> assert false

  let pa (t:t) : atom = match t.t_var with
    | Var_bool {pa; _} -> pa
    | _ -> assert false

  let na (t:t) : atom = match t.t_var with
    | Var_bool {na; _} -> na
    | _ -> assert false
end

(** {2 Hashconsing of a Theory Terms} *)

module type TERM_ALLOC_OPS = sig
  val p_id : plugin_id (** ID of the theory *)
  val initial_size: int (** initial size of table *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
end

module[@inline] Term_allocator(Ops : TERM_ALLOC_OPS) = struct
  module H = CCHashtbl.Make(struct
      type t = view
      include Ops
    end)
  let () = assert (Ops.p_id <= Unsafe.max_plugin_id)

  (* view -> term *)
  let tbl = H.create Ops.initial_size

  (* after GC, recycle identifiers *)
  let recycle_ids : int Vec.t = Vec.make_empty 0

  (* delete a term: flag it for removal, then recycle its ID *)
  let delete (t:t) : unit =
    Log.debugf 5 (fun k->k "delete `%a`" pp t);
    t.t_fields <- Term_fields.set field_t_is_deleted true t.t_fields;
    assert (plugin_id t = Ops.p_id);
    Vec.push recycle_ids (plugin_specific_id t);
    H.remove tbl (view t);
    ()

  (* obtain a fresh ID, unused by any other term *)
  let get_fresh_id : unit -> int =
    let id_alloc = ref 0 in
    fun () ->
      if Vec.size recycle_ids = 0 then (
        let n = !id_alloc in
        incr id_alloc;
        n
      ) else (
        let n = Vec.last recycle_ids in
        Vec.pop recycle_ids;
        n
      )

  (* build a fresh term *)
  let[@inline never] make_real_ t_view t_ty t_tc : t =
    let p_specific_id = get_fresh_id () in
    let t_id = Ops.p_id lor (p_specific_id lsl plugin_id_width) in
    let t_fields = Fields.empty in
    let t_level = -1 in
    let t_weight = 0. in
    let t_idx = ~-1 in
    { t_id; t_view; t_ty; t_fields; t_level; t_weight; t_idx;
      t_var=Var_none; t_tc; }

  (* inline make function *)
  let[@inline] make (view:view) (ty:Type.t) (tc:tc_term) : t =
    try H.find tbl view
    with Not_found -> make_real_ view ty tc

  let[@inline] iter_terms k = H.values tbl k

  let gc_all () : unit =
    Log.debugf 3 (fun k->k "(gc-all@ :p_id %d)" Ops.p_id);
    let v = Vec.make_empty dummy_term in
    (* collect *)
    H.iter
      (fun _ t ->
         if gc_marked t
         then gc_unmark t
         else Vec.push v t)
      tbl;
    (* delete *)
    Vec.iter delete v
end
