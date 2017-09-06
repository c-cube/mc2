
(** {1 Simple Types} *)

open Solver_types

type t = ty
type view = ty_view
type tc = tc_ty

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val pp : t CCFormat.printer

val is_bool : t -> bool

val id : t -> int (** on non-bool *)
val view : t -> view (** on non-bool *)
val decide : t -> actions -> term -> value (** on non-bool *)
val mk_decide_state : t -> decide_state (** on non-bool *)
val mk_eq : t -> term -> term -> term (** on non-bool *)

(** Build a typeclass *)
val tc_mk :
  decide:(actions -> term -> value) ->
  eq:(term -> term -> term) ->
  mk_state:(unit -> decide_state) ->
  pp:view CCFormat.printer ->
  unit ->
  tc

val bool : t

module type TY_ALLOC_OPS = sig
  val initial_size: int (** initial size of table *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
end

module Alloc(T : TY_ALLOC_OPS) : sig
  val make : view -> tc -> t (** Main constructor *)
end

