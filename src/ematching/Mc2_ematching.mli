
(** {1 E-matching} *)

open Mc2_core
open Solver_types

type pattern_view = ..
(** Custom patterns provided by plugins *)

type var = {
  v_id : ID.t;
  v_ty : Type.t;
} (** variable of a given type *)

type pattern = private
  | P_var of var
  | P_app of {
      id: ID.t;
      ty: Type.t;
      args: pattern array;
    }
  | P_term of term (** physical equality *)
  | P_value of value (** value, e.g. booleans *)
  | P_custom of {
      view: pattern_view;
      ty: Type.t;
      tc: tc_pattern;
    } (** Plugin-specific pattern, for example a linear expression
          with variables. *)
(** Patterns for matching against ground terms modulo E (and perhaps
    modulo other theories) *)

and match_fun = subst -> pattern -> term -> subst Sequence.t
(** Matching function *)

and tc_pattern = {
  tcp_pp : pattern_view Fmt.printer; (** print custom pattern *)
  tct_match : match_fun -> subst -> pattern_view -> term -> subst Sequence.t;
  (** match pattern with term *)
} (** Methods for custom patterns *)

and subst
(** Substitutions. A substitution is an immutable value that maps
    finitely many variables to (ground) terms. *)

module Var : sig
  type t = var

  val id : t -> ID.t
  val ty : t -> Type.t
  val compare : t -> t -> int
  val equal : t -> t -> bool
  val hash : t -> int

  val make : ID.t -> Type.t -> t

  val fresh : Type.t -> t

  val pp : t Fmt.printer
end

module Subst : sig
  type t = subst

  val empty : t
  val mem : t -> var -> bool
  val add : t -> var -> term -> t
  val get : t -> var -> term option
  val to_list : t -> (var * term) list

  val pp : t Fmt.printer
end

(** {2 Patterns} *)
module Pattern : sig
  type t = pattern
  type view = pattern_view
  type tc = tc_pattern

  val ty : t -> Type.t

  val var : var -> t
  val const : ID.t -> Type.t -> t
  val app_a : ID.t -> Type.t -> t array -> t (** owns the array *)
  val app_l : ID.t -> Type.t -> t list -> t

  val of_term : term -> t
  val of_value : value -> t

  val make : view -> Type.t -> tc -> t
  (** Make custom pattern *)

  val is_top : t -> bool
  (** Is the pattern a top pattern, i.e. an application of
      some uninterpreted symbol? *)

  val pp : t Fmt.printer
end

type id_instance = {
  ii_term: term; (* [id t1…tn] *)
  ii_args: term array; (* [t1…tn], the arguments of the ID *)
}

val k_iter_value_symbol : (Value.t -> ID.t -> id_instance Sequence.t) Service.Key.t
(** Service that, given a value [v] and symbol [f], iterates on
    all terms of the shape [f t1…tn] currently mapped to [v] in the model. *)

val k_iter_symbol : (ID.t -> id_instance Sequence.t) Service.Key.t
(** Service that, given a symbol [f], iterates on
    all terms of the shape [f t1…tn] currently assigned in the model. *)

val k_e_match : (pattern -> subst Sequence.t) Service.Key.t
(** Service that E-matches this pattern with any term in the model *)

val k_e_match_with : (pattern -> term -> subst Sequence.t) Service.Key.t
(** Service that E-matches this pattern with this term *)

val plugin : Plugin.Factory.t
(** Main plugin for E-matching. It depends on some UF module
    providing [k_iter_symbol] and [k_iter_value_symbol].

    Provides [k_e_match] and [k_e_match_with] *)
