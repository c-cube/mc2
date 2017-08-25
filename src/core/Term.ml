
(** {1 Modular Term Structure} *)

module Fields = BitField.Make(struct end)

(** Extensible view. Each plugin might declare its own terms. *)
type view = ..

type plugin_id = int

type t = {
  mutable id: int;
  (** unique ID, made of:
      - 4 bits plugin_id
      - the rest is for plugin-specific id *)
  view: view;
  (** view *)
  ty: Type.t;
  (** type of the term *)
  mutable fields: Fields.t;
  (** bitfield for storing various info *)
}

let[@inline] id t = t.id

let[@inline] view t = t.view

let[@inline] equal t u = t.id = u.id

let[@inline] compare t u = CCInt.compare t.id u.id

let[@inline] hash t = CCHash.int t.id

(** {2 Fields} *)

let[@inline] field_get f t = Fields.get f t.fields

let[@inline] field_set f b t = t.fields <- Fields.set f b t.fields

let field_is_value = Fields.mk_field ()
let field_is_deleted = Fields.mk_field ()

(** {2 ID Management} *)

(* store plugin id at 4 lowest bits *)
let plugin_id_width = 4

(* bitmask *)
let p_mask = (1 lsl plugin_id_width) - 1

let[@inline] plugin_id t : int = id t land p_mask

let[@inline] plugin_specific_id t : int = id t lsr plugin_id_width

(** {2 Low Level constructors. Use at your own risks.} *)
module Unsafe = struct
  let max_plugin_id = (1 lsl plugin_id_width) - 1

  let[@inline] mk_plugin_id (id:int): plugin_id =
    if id > max_plugin_id then (
      failwith "add_plugin: too many plugins";
    );
    id
end

(** {2 Hashconsing of a Theory Terms} *)

module type TERM_ALLOC_OPS = sig
  val p_id : plugin_id
  (** ID of the theory *)

  val equal : view -> view -> bool
  (** Shallow equality of two views of the plugin *)

  val hash : view -> int
  (** Shallow hash of a view of the plugin *)
end

type view += Dummy

let dummy = { id= ~-1; view=Dummy; ty=Type.prop; fields= Fields.empty; }

module[@inline] Term_allocator(Ops : TERM_ALLOC_OPS) = struct
  module H = CCHashtbl.Make(struct
      type t = view
      include Ops
    end)

  let () = assert (Ops.p_id <= Unsafe.max_plugin_id)

  (* view -> term *)
  let tbl = H.create 1024

  let id_alloc = ref 0

  (* after GC, recycle identifiers *)
  let recycle_ids : int Vec.t = Vec.make_empty 0

  (* delete a term: flag it for removal, then recycle its ID *)
  let delete (t:t) : unit =
    field_set field_is_deleted true t;
    assert (plugin_id t = Ops.p_id);
    Vec.push recycle_ids (plugin_specific_id t);
    H.remove tbl t.view;
    ()

  let[@inline] get_fresh_id () : int =
    if Vec.size recycle_ids = 0 then (
      let n = !id_alloc in
      incr id_alloc;
      n
    ) else (
      let n = Vec.last recycle_ids in
      Vec.pop recycle_ids;
      n
    )

  let[@inline never] make_real_ view ty : t =
    let p_specific_id = get_fresh_id () in
    let id = Ops.p_id lor (p_specific_id lsl plugin_id_width) in
    let fields = Fields.empty in
    { id; view; ty; fields; }

  (* inline make function *)
  let[@inline] make (view:view) (ty:Type.t) : t =
    try H.find tbl view
    with Not_found -> make_real_ view ty
end

(* TODO: update this *)

  let rec dummy_var =
    { vid = -101;
      pa = dummy_atom;
      na = dummy_atom;
      used = 0;
      v_flags = Bool_var_fields.empty;
      v_level = -1;
      v_weight = -1.;
      v_assignable = None;
      reason = None;
    }
  and dummy_atom =
    { var = dummy_var;
      lit = dummy_lit;
      watched = Obj.magic 0;
      (* should be [Vec.make_empty dummy_clause]
         but we have to break the cycle *)
      neg = dummy_atom;
      is_true = false;
      aid = -102 }
  let dummy_clause =
    { name = "";
      tag = None;
      atoms = [| |];
      activity = -1.;
      attached = false;
      visited = false;
      cpremise = History [] }

  let make_semantic_var t =
    try MT.find t_map t
    with Not_found ->
      let res = {
        lid = !cpt_mk_var;
        term = t;
        l_weight = 1.;
        l_level = -1;
        assigned = None;
      } in
      incr cpt_mk_var;
      MT.add t_map t res;
      Vec.push vars (E_lit res);
      res

  let make_boolean_var : formula -> bool_var * Expr_intf.negated =
    fun t ->
      let lit, negated = E.Formula.norm t in
      try
        MF.find f_map lit, negated
      with Not_found ->
        let cpt_fois_2 = !cpt_mk_var lsl 1 in
        let rec var  =
          { vid = !cpt_mk_var;
            pa = pa;
            na = na;
            used = 0;
            v_flags = Bool_var_fields.empty;
            v_level = -1;
            v_weight = 0.;
            v_assignable = None;
            reason = None;
          }
        and pa =
          { var = var;
            lit = lit;
            watched = Vec.make 10 dummy_clause;
            neg = na;
            is_true = false;
            aid = cpt_fois_2 (* aid = vid*2 *) }
        and na =
          { var = var;
            lit = E.Formula.neg lit;
            watched = Vec.make 10 dummy_clause;
            neg = pa;
            is_true = false;
            aid = cpt_fois_2 + 1 (* aid = vid*2+1 *) } in
        MF.add f_map lit var;
        incr cpt_mk_var;
        Vec.push vars (E_var var);
        var, negated

(* TODO: move this in theory of booleans?
   ensure that [not a] shares the same atoms as [a], but inverted
   (i.e. [(not a).pa = a.na] and conversely
   OR: share the variable but have a bool field for "negated" *)
  let add_atom lit =
    let var, negated = make_boolean_var lit in
    match negated with
      | Formula_intf.Negated -> var.na
      | Formula_intf.Same_sign -> var.pa

  (* Marking helpers *)
  let clear v = v.v_flags <- Bool_var_fields.empty

  let seen_var v = Bool_var_fields.get field_seen_var v.v_flags

  let mark_var v =
    v.v_flags <- Bool_var_fields.set field_seen_var true v.v_flags

  (* Complete debug printing *)
  let sign a = if a == a.var.pa then "+" else "-"
  let pp_value fmt a =
    if a.is_true then
      Format.fprintf fmt "T%a" pp_level a
    else if a.neg.is_true then
      Format.fprintf fmt "F%a" pp_level a
    else
      Format.fprintf fmt ""


  let pp_assign fmt v =
    match v.assigned with
      | None ->
        Format.fprintf fmt ""
      | Some t ->
        Format.fprintf fmt "@[<hov>@@%d->@ %a@]" v.l_level E.Term.print t
  let pp_lit out v =
    Format.fprintf out "%d[%a][lit:@[<hov>%a@]]"
      (v.lid+1) pp_assign v E.Term.print v.term

let pp_level fmt t =
  Reason.pp fmt (t.t_level, t.t_reason)
