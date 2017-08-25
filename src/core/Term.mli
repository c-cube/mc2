
(** {1 Modular Term Structure} *)

module Fields : CCBitField.S

(** Extensible view. Each plugin might declare its own terms. *)
type view = ..

type t = private {
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

(** {2 Fields} *)

val field_set : Fields.field -> bool -> t -> unit

val field_get : Fields.field -> t -> bool

val field_is_value : Fields.field
(** Is the field a value (i.e. usable in assignments)? *)

(** {2 Basics} *)

val id : t -> int
(** Globally unique ID of this term *)

val view : t -> view

val equal : t -> t -> bool

val compare : t -> t -> int

val hash : t -> int

(** {2 ID Management} *)

val plugin_id_width : int
(** Number of bits dedicated to plugin IDs.
    There can be at most [2 ** plugin_id_width] plugins in a solver. *)

val plugin_id : t -> int
(** Which plugin owns this term? *)

val plugin_specific_id : t -> int
(** ID of the term for the plugin itself *)

(** {2 Low Level constructors. Use at your own risks.} *)
module Unsafe : sig
  val max_plugin_id: int

  val make : p_id:int -> p_specific_id:int -> view -> Type.t -> t
  (** [make ~p_id view ty] makes a term with the given view and type.
      @param p_id the ID of the plugin that owns this term
      @param p_specific_id the unique ID of the term in this plugin
  *)
end
