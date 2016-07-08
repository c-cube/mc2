(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon and Alain Mebsout                     *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

module type S = Solver_types_intf.S

module McMake (E : Expr_intf.S)(Dummy : sig end):
    S with type term = E.Term.t and type formula = E.Formula.t and type proof = E.proof
(** Functor to instantiate the types of clauses for a solver. *)

module SatMake (E : Formula_intf.S)(Dummy : sig end):
    S with type term = E.t and type formula = E.t and type proof = E.proof
(** Functor to instantiate the types of clauses for a solver. *)
