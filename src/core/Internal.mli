(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(** mSAT core

    This is the core of msat, containing the code doing the actual solving.
    This module is based on mini-sat, and as such the solver heavily uses mutation,
    which makes using it direclty kinda tricky (some exceptions can be raised
    at surprising times, mutating is dangerous for maintaining invariants, etc...).
*)


(** {2 Solving facilities} *)

open Solver_types

exception Unsat
exception UndecidedLit

type t
(** The core solver structure *)

val create : unit -> t
(** Create a solver *)

val add_plugin : t -> Plugin.Factory.t -> Plugin.t
(** [add_plugin s f] creates a new plugin, stores it into [s],
    and returns it.
    @raise Failure if all plugin IDs have been allocated
*)


val plugins : t -> Plugin.t Sequence.t

val get_plugin : t -> plugin_id -> Plugin.t
(** Get the plugin from its ID *)

val services : t -> Service.Registry.t
(** Service registry *)

val get_service : t -> 'a Service.Key.t -> 'a option
(** Obtain a service by its key *)

val get_service_exn : t -> 'a Service.Key.t -> 'a
(** Obtain a service by its key *)

val actions : t -> actions
(** Actions available to plugins *)

(* FIXME:
val gc_mark_sub : t -> (Term.t -> unit) -> Term.t -> unit
(** [gc_mark_sub f t] should call [f] on every subterm of [t]
    to retain them during GC *)
*)

val iter_terms : t -> term Sequence.t
(** Iterate on all terms known to plugins.
    Used for checking all variables to assign, and for garbage collection. *)

val solve : t -> unit
(** Try and solves the current set of assumptions.
    @return () if the current set of clauses is satisfiable
    @raise Unsat if a toplevel conflict is found *)

val assume : t -> ?tag:int -> atom list list -> unit
(** Add the list of clauses to the current set of assumptions.
    Modifies the sat solver state in place. *)

val add_term : t -> term -> unit
(** Add a new generalized variable (i.e term) to the solver. This term will
    be decided on at some point during solving, wether it appears
    in clauses or not. *)

val add_term : t -> term -> unit
(** Add term (and its subterms, recursively) to the solver.
    It means the term will have a value in the model. *)

val push : t -> unit
(** Create a decision level for local assumptions.
    @raise Unsat if a conflict is detected in the current state. *)

val pop : t -> unit
(** Pop a decision level for local assumptions. *)

val local : t -> atom list -> unit
(** Add local assumptions
    @param assumptions list of additional local assumptions to make,
      removed after the callback returns a value
    @raise Invalid_argument if no levels were {!push}ed *)

(** {2 Propositional models} *)

val eval : atom -> bool
(** Returns the valuation of a term in the current state
    of the sat solver.
    @raise UndecidedLit if the literal is not decided *)

val eval_level : atom -> bool * int
(** Return the current assignement/evaluation of the boolean term,
    as well as its decision level. If the level is 0, then it is necessary for
    the atom to have this value; otherwise it is due to choices
    that can potentially be backtracked.
    @raise UndecidedLit if the literal is not decided not calculable *)

val model : t -> assignment_view list
(** Returns the model found if the term is satisfiable. *)

val check : t -> bool
(** Check the satisfiability of the current model. Only has meaning
    if the solver finished proof search and has returned [Sat]. *)

(** {2 Proofs and Models} *)

type proof = Res.proof

val unsat_conflict : t -> clause option
(** Returns the unsat clause found at the toplevel, if it exists (i.e if
    [solve] has raised [Unsat]) *)

(** {2 Internal data}
    These functions expose some internal data stored by the solver, as such
    great care should be taken to ensure not to mess with the values returned. *)

val trail : t -> trail
(** Returns the current trail.
    {b DO NOT MUTATE} *)

val hyps : t -> clause Vec.t
(** Returns the vector of assumptions used by the solver. May be slightly different
    from the clauses assumed because of top-level simplification of clauses.
    {b DO NOT MUTATE} *)

val temp : t -> clause Vec.t
(** Returns the clauses coreesponding to the local assumptions.
    All clauses in this vec are assured to be unit clauses.
    {b DO NOT MUTATE} *)

val history : t -> clause Vec.t
(** Returns the history of learnt clauses, with no guarantees on order.
    {b DO NOT MUTATE} *)
