
(** {1 Values} *)

(** A value belongs in models. Every term must eventually be assigned to
    a value. *)

open Solver_types

type t = value
type view = value_view

val equal : t -> t -> bool
val hash : t -> int
val pp : t CCFormat.printer

val is_bool : t -> bool
val is_true : t -> bool
val is_false : t -> bool
val as_bool : t -> bool option
val as_bool_exn : t -> bool

val bool_neg : t -> t

val view : t -> value_view (** non-bool only *)
val tc : t -> tc_value (** non-bool only *)

val true_ : t
val false_ : t
val of_bool : bool -> t

val make : tc_value -> view -> t
(** Main construction for values *)

module Tbl : CCHashtbl.S with type key = t

module TC : sig
  type t = tc_value

  val make :
    pp:view Fmt.printer -> (** printer *)
    equal:(view -> view -> bool) -> (** equality *)
    hash:(view -> int) -> (** hash function *)
    unit ->
    t
end
