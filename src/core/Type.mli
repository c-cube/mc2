
(** {1 Simple Types} *)

open Solver_types

type t = ty
type view = ty_view

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val pp : t CCFormat.printer

val is_bool : t -> bool

val id : t -> int (** on non-bool *)
val view : t -> view (** on non-bool *)
val decide : t -> actions -> term -> value (** on non-bool *)
val mk_decide_state : t -> decide_state (** on non-bool *)

val bool : t

module type TY_ALLOC_OPS = sig
  val initial_size: int (** initial size of table *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
  val tc : tc_ty
end

module Alloc(T : TY_ALLOC_OPS) : sig
  val make : view -> t
  (** Main constructor *)
end

