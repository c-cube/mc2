
(** {1 Linear Expressions} *)

open Mc2_core

type t
(** Linear expression with rational coefficients and rational-typed terms *)

type num = Q.t

val equal : t -> t -> bool
val hash : t -> int
val pp : t Fmt.printer
val pp_no_paren : t Fmt.printer

val empty : t (** Empty linear expression *)
val zero : t (** alias for {!empty} *)

val is_const : t -> bool
(** true if the expressions is constant *)

val is_zero : t -> bool
(** true if the expressions is constant and equal to zero *)

val add : t -> t -> t (** Sum of linear expressions *)
val diff : t -> t -> t (** Diff of linear expressions *)

val const : num -> t

val as_singleton : t -> (num * term) option (** no constant, and exactly one term? *)

val mem_term : term -> t -> bool

val add_term : num -> term -> t -> t

val remove_term : term -> t -> t

val get_term : term -> t -> num option

val find_term_exn : term -> t -> num
(** Find value for this term, or Not_found *)

val singleton : num -> term -> t

val singleton1 : term -> t

val neg : t -> t
(** Invert sign *)

val mult : num -> t -> t
(** Product by constant *)

val div : t -> num -> t
(** [div e n] is [e/n].
    @raise Division_by_zero if [n=0] *)

val flatten : f:(term -> t option) -> t -> t
(** [flatten f e] traverses all terms, and if they are themselves mapped
    into expressions by [f], replaces them by the corresponding expr *)

val terms : t -> term Sequence.t
val terms_l : t -> term list

val as_const : t -> num option

val eval : f:(term -> num option) -> t -> (num * term list) option
(** [eval e] evaluates the expression if all subterms (returned in
    a list) have a value according to [f] *)

module Infix : sig
  val (+..) : t -> t -> t
  val (-..) : t -> t -> t
  val ( *..) : num -> t -> t
end

(**/**)
val hash_q : num -> int
(**/**)
