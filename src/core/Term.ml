
(** {1 Modular Term Structure} *)

module Fields = CCBitField.Make(struct end)

(** Extensible view. Each plugin might declare its own terms. *)
type view = ..

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

  let[@inline] make ~p_id ~p_specific_id view ty : t =
    assert (p_id <= max_plugin_id);
    let id = p_id lor (p_specific_id lsl plugin_id_width) in
    let fields = Fields.empty in
    { id; view; ty; fields; }
end

