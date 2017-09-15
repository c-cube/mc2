
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

val bool : t

module TC : sig
  type t = tc

  (** Build a typeclass *)
  val make :
    decide:(actions -> term -> value) ->
    eq:(term -> term -> term) ->
    mk_state:(unit -> decide_state) ->
    pp:view CCFormat.printer ->
    unit ->
    t

  type lazy_tc
  (** Future typeclass. Acts as a kind of forward declaration that
      can be used to declare types before actually defining the
      operations on it *)

  val lazy_make : unit -> lazy_tc
  val lazy_from_val : t -> lazy_tc
  val lazy_get : lazy_tc -> t (** call only after {!lazy_complete} *)

  val lazy_complete :
    decide:(actions -> term -> value) ->
    eq:(term -> term -> term) ->
    mk_state:(unit -> decide_state) ->
    pp:view CCFormat.printer ->
    lazy_tc ->
    unit
    (** Set operations of the typeclass, lazily *)
end

module type TY_ALLOC_OPS = sig
  val tc : TC.lazy_tc
  val initial_size: int (** initial size of table *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
end

module Alloc(T : TY_ALLOC_OPS) : sig
  val make : view -> t (** Main constructor *)
end

val make_static : view -> tc -> t
(** Static types, directly provided by plugins. This
    function is generative, i.e. it will yield a different type every
    time it is called. *)

