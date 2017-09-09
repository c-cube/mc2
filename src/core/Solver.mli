(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(** Main Interface for the Solver
*)

open Solver_types

type proof = Res.proof
type nonrec atom = atom (** The type of atoms given by the module argument for formulas *)

(** {2 Types} *)

(** {2 Main Type} *)

type t
(** The type of a solver *)

(** {2 Base operations} *)

val create : plugins:Plugin.Factory.t list -> unit -> t
(** Create a new solver with the given plugins *)

val plugins : t -> Plugin.t Sequence.t
(** Obtain the current plugins *)

val services : t -> Service.Registry.t

val get_service : t -> 'a Service.Key.t -> 'a option
(** Obtain a service by its key *)

val get_service_exn : t -> 'a Service.Key.t -> 'a
(** Obtain a service by its key, or fail *)

val assume : t -> ?tag:int -> atom list list -> unit
(** Add the list of clauses to the current set of assumptions.
    Modifies the sat solver state in place. *)

val add_term : t -> term -> unit
(** Add a new literal (i.e term) to the solver. This term will
    be decided on at some point during solving, whether it appears
    in clauses or not. *)

val unsat_core : t -> proof -> clause list
(** Returns the unsat core of a given proof. *)

val true_at_level0 : t -> atom -> bool
(** [true_at_level0 a] returns [true] if [a] was proved at level0, i.e.
    it must hold in all models *)

type 'clause clause_sets = {
  cs_hyps: 'clause Vec.t;
  cs_history: 'clause Vec.t;
  cs_local: 'clause Vec.t;
}
(** Current state of the SAT solver *)

val clause_sets : t -> clause clause_sets
(** Iterate on current sets of clauses *)

(* TODO: update…
   - in particular, MCsat implies some interfaces are different (model is
    pairs (term,value))
   - distinguish term/value
   - merge term/formula (whch are just boolean-typed terms of the
    plugin of formulas)
*)

type 'a state
(** Opaque view on the solver in a given state, with a phantom parameter to
    indicate in which state it is *)

val state_solver: _ state -> t
(** Get the solver back from a solver. *)

exception UndecidedLit
(** Exception raised by the evaluating functions when a literal
    has not yet been assigned a value. *)

module Sat_state : sig
  type t = [`SAT] state

  val eval: t -> atom -> bool
  (** Returns the valuation of a formula in the current state
      of the sat solver.
      @raise UndecidedLit if the literal is not decided *)

  val eval_level: t -> atom -> bool * int
  (** Return the current assignment of the literals, as well as its
      decision level. If the level is 0, then it is necessary for
      the atom to have this value; otherwise it is due to choices
      that can potentially be backtracked.
      @raise UndecidedLit if the literal is not decided *)

  val iter_trail : t -> term Sequence.t
  (** Iterate through the formulas and terms in order of decision/propagation
      (starting from the first propagation, to the last propagation). *)

  val model: t -> assignment_view list
  (** Returns the model found if the formula is satisfiable. *)
end

module Unsat_state : sig
  type t = [`UNSAT] state

  val unsat_conflict : t -> clause
  (** Returns the unsat clause found at the toplevel *)

  val get_proof : t -> proof
  (** returns a persistent proof of the empty clause from the Unsat result. *)
end

type res =
  | Sat of Sat_state.t (** Returned when the solver reaches SAT *)
  | Unsat of Unsat_state.t (** Returned when the solver reaches UNSAT *)
(** Result type for the solver *)

val solve :
  ?gc:bool ->
  ?restarts:bool ->
  ?assumptions:atom list ->
  t ->
  res
(** Try and solves the current set of assumptions. *)

val pp_stats : t CCFormat.printer
(** Print stats *)
