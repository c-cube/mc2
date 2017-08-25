
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
