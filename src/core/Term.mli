
(** {1 Modular Term Structure} *)

module Fields : CCBitField.S

(** Extensible view. Each plugin might declare its own terms. *)
type view = ..

type plugin_id = private int
(** Unique ID of a plugin *)

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

val field_is_deleted : Fields.field
(** Term that has been collected *)

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

val plugin_id : t -> plugin_id
(** Which plugin owns this term? *)

val plugin_specific_id : t -> int
(** ID of the term for the plugin itself *)

(** {2 Low Level constructors. Use at your own risks.} *)
(**/**)
module Unsafe : sig
  val max_plugin_id: int

  val mk_plugin_id : int -> plugin_id
  (** Convert an int into a plugin ID.
      Should only be used in {!Plugin_db}. *)
end

val dummy : t
(** Dummy term. Do not use it in any function, just for initializing
      vectors. *)
(**/**)

(** {2 Hashconsing of a Theory Terms} *)

module type TERM_ALLOC_OPS = sig
  val p_id : plugin_id
  (** ID of the theory *)

  val equal : view -> view -> bool
  (** Shallow equality of two views of the plugin *)

  val hash : view -> int
  (** Shallow hash of a view of the plugin *)
end

module Term_allocator(T : TERM_ALLOC_OPS) : sig
  val make : view -> Type.t -> t
  (** Make a term of the theory *)

  val delete : t -> unit
  (** Delete a term of the theory *)
end
