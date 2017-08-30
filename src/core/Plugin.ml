(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Evelyne Contejean                    *)
(*                  Francois Bobot, Mohamed Iguernelala, Alain Mebsout    *)
(*                  CNRS, Universite Paris-Sud 11                         *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)
(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

(** McSat Theory

    This module defines what a theory must implement in order to
    be used in a MCSat solver.
*)

open Solver_types

type proof = Res.proof

type eval_res =
  | Unknown (** The given formula does not have an evaluation *)
  | Valued of bool * term list
  (** The given formula can be evaluated to the given bool.
      The list of terms to give is the list of terms that were effectively used
      for the evaluation.
  *)
(** The type of evaluation results for a given formula.
    For instance, let's suppose we want to evaluate the formula [x * y = 0], the
    following result are correct:
    - [Unknown] if neither [x] nor [y] are assigned to a value
    - [Valued (true, [x])] if [x] is assigned to [0]
    - [Valued (true, [y])] if [y] is assigned to [0]
    - [Valued (false, [x; y])] if [x] and [y] are assigned to 1 (or any non-zero number)
*)

type res =
  | Sat
  (** The current set of assumptions is satisfiable. *)
  | Unsat of atom list * lemma
  (** The current set of assumptions is *NOT* satisfiable, and here is a
      theory tautology (with its proof), for which every literal is false
      under the current assumptions. *)

type actions = {
  act_push_clause : clause -> unit;
  (** push a new clause *)
  act_propagate_bool : term -> bool -> term list -> unit;
  (** [act_propagate_bool t b l] propagates the boolean literal [t]
      assigned to boolean value [b], explained by evaluation of
      (sub)terms [l] *)
  act_on_backtrack : int -> (unit -> unit) -> unit;
  (** [act_on_backtrack level f] will call [f] when the given [level]
      is backtracked *)
}
(** Actions available to plugins when doing propagation/model building,
    including adding clauses, registering actions to do upon
    backtracking, etc. *)

(** Main interface for plugins. Each plugin must abide by this
    interface. *)
module type S = sig
  val id : plugin_id

  val name : string
  (** Descriptive name *)

  val decide : actions -> term -> value
  (** Pick a value for this variable to do a decision *)

  val cb_assign : actions -> term -> res
  (** Called when a term of this plugin is assigned/propagated *)

  val cb_if_sat : actions -> unit or_conflict
  (** Last call before answering "sat". If the current trail is not
      theory-satisfiable, the plugin {b MUST} give a conflict here. *)

  val eval_bool : bool_term -> eval_res
  (** Evaluate boolean term in current trail *)

  val iter_sub : term -> term Sequence.t
  (** Iterate on immediate sub-term *)

  val iter_terms : term Sequence.t
  (** Iterate on all terms known to the plugin. Used for
      checking all variables to assign, and for
      garbage collection. *)

  val gc_mark_sub : (term -> unit) -> term_view -> unit
  (** [gc_mark_sub f t] should call [f] on every subterm of [t]
      to retain them during GC *)

  val term_of_value : value -> term
  (** Turn a value of this plugin into a term of this plugin. *)

  val pp_term : term CCFormat.printer -> term_view CCFormat.printer
  (** [pp_term pp_sub] is a term-view printer.
      It is only ever called with terms that belong to this plugin,
      and can use [pp_sub] to call sub-terms in a generic way. *)

  val pp_lemma : lemma CCFormat.printer
  (** Print lemma belonging to this plugin *)
end

type t = (module S)

type factory = plugin_id -> t
(** A plugin factory, i.e. the method to build a plugin with a given ID.
    The plugin is allowed to register actions to be taken upon backtracking.
    @param plugin_id the unique ID of the plugin
    @param on_backtrack to call to register backtrack actions
      [on_backtrack lev f] will call [f] when level [lev] is backtracked.
*)

let[@inline] owns_term (module P : S) (t:term) : bool = Term.plugin_id t = P.id
let[@inline] name (module P : S) = P.name
