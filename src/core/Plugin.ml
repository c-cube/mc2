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
  | Unsat of bool_term list * lemma
  (** The current set of assumptions is *NOT* satisfiable, and here is a
      theory tautology (with its proof), for which every literal is false
      under the current assumptions. *)

(** Main interface for plugins. Each plugin must abide by this
    interface. *)
module type S = sig
  val id : plugin_id

  val name : string
  (** Descriptive name *)

  val decide : term -> value or_conflict
  (** Pick a value for this variable to do a decision *)

  val cb_assign : term -> propagation list or_conflict
  (** Called when a term of this plugin is assigned/propagated *)

  val cb_if_sat : unit -> propagation list or_conflict
  (** Last call before answering "sat". If the current trail is not
      theory-satisfiable, the plugin {b MUST} give a conflict here. *)

  val eval_bool : bool_term -> bool option
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

  val pp_term : term CCFormat.printer -> term_view CCFormat.printer
  (** [pp_term pp_sub] is a term-view printer.
      It is only ever called with terms that belong to this plugin,
      and can use [pp_sub] to call sub-terms in a generic way. *)

  val pp_lemma : lemma CCFormat.printer
  (** Print lemma belonging to this plugin *)
end

type t = (module S)

type factory = plugin_id -> t

let[@inline] owns_term (module P : S) (t:term) : bool =
  Term.plugin_id t = P.id
