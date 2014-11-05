(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Mohamed Iguernelala                                   *)
(*                  Universite Paris-Sud 11                               *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

module Make (F : Formula_intf.S)
    (St : Solver_types.S with type formula = F.t)
    (Ex : Explanation.S with type atom = St.atom)
    (Th : Theory_intf.S with type formula = F.t and type explanation = Ex.t)
    (L : Neperien.S) :
sig
  (** Functor to create a SMT Solver parametrised by the atomic
      formulas and a theory. *)

  exception Unsat of St.clause list

  val solve : unit -> unit
  (** Try and solves the current set of assumptions.
      @return () if the current set of clauses is satisfiable
      @raise Unsat if a toplevel conflict is found *)

  val assume : F.t list list -> cnumber:int -> unit
  (** Add the list of clauses to the current set of assumptions.
      Modifies the sat solver state in place.
      @raise Unsat if a conflict is detect when adding the clauses *)

  val eval : F.t -> bool
  (** Returns the valuation of a formula in the current state
      of the sat solver. *)

  type level
  (** Abstract notion of assumption level. *)

  val base_level : level
  (** Level with no assumption at all, corresponding to the empty solver *)

  val current_level : unit -> level
  (** The current level *)

  val push : unit -> level
  (** Create a new level that extends the previous one. *)

  val pop : level -> unit
  (** Go back to the given level, forgetting every assumption added since.
      @raise Invalid_argument if the current level is below the argument *)

  val clear : unit -> unit
  (** Return to level {!base_level} *)
end

