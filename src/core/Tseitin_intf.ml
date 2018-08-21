(**************************************************************************)
(*                                                                        *)
(*                          Alt-Ergo Zero                                 *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                      Universite Paris-Sud 11                           *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

(** Interfaces for Tseitin's CNF conversion *)

(** Atomic formulas. *)
module type Arg = sig
  type t
  (** Type of atomic formulas. *)

  val neg : t -> t
  (** Negation of atomic formulas. *)

  val pp : t CCFormat.printer
  (** Print the given formula. *)
end

(** CNF conversion

    This modules allows to convert arbitrary boolean formulas
    into CNF.
*)
module type S = sig
  type atom
  (** The type of atomic formulas. *)

  type combinator = And | Or | Not

  type id

  type t = private {
    id: id;
    view: view;
  }

  and view =
    | True
    | Lit of atom
    | Comb of combinator * t list
    (** The type of arbitrary boolean formulas. Arbitrary boolean formulas
        can be built using functions in this module, and then converted
        to a CNF, which is a list of clauses that only use atomic formulas. *)

  val view : t -> view

  val true_ : t
  (** The [true] formula, i.e a formula that is always satisfied. *)

  val false_ : t
  (** The [false] formula, i.e a formula that cannot be satisfied. *)

  val atom : atom -> t
  (** [atom p] builds the boolean formula equivalent to the atomic formula [p]. *)

  val not_ : t -> t
  (** Creates the negation of a boolean formula. *)

  val and_ : t list -> t
  (** Creates the conjunction of a list of formulas. An empty conjunction is always satisfied. *)

  val or_ : t list -> t
  (** Creates the disjunction of a list of formulas. An empty disjunction is never satisfied. *)

  val xor : t -> t -> t
  (** [xor p q] creates the boolean formula "[p] xor [q]". *)

  val imply : t -> t -> t
  (** [imply p q] creates the boolean formula "[p] implies [q]". *)

  val imply_l : t list -> t -> t

  val equiv : t -> t -> t
  (** [equiv p q] creates the boolena formula "[p] is equivalent to [q]". *)

  val cnf : ?simplify:bool -> fresh:(unit -> atom) -> t -> atom list list
  (** [cnf f] returns a conjunctive normal form of [f] under the form: a
      list (which is a conjunction) of lists (which are disjunctions) of
      atomic formulas.
      @param fresh used to generate fresh atoms to name formulas
      @param simplify if true (default) simplifiy formula *)

  val pp : t CCFormat.printer
  (** [pp fmt f] prints the formula on the formatter [fmt].*)
end
