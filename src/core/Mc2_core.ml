
(** {1 Core Library} *)

(** This library contains the core structures and  algorithms of mc2.
    It defines terms, types, values, the main solver, plugins, etc.

*)

module Atom = Atom
module Term = Term
module Type = Type
module Value = Value
module Actions = Actions
module Builtins = Builtins
module Clause = Clause
module Proof = Proof
module Solver = Solver
module Service = Service
module Plugin = Plugin
module Tseitin = Tseitin
module ID = ID
module Lemma = Lemma

(**/**)
module Util = Util
module Log = Log
(**/**)

module Fmt = CCFormat
module Int_map = Util.Int_map

type level = Solver_types.level
(** Backtracking level *)

type ty_view = Solver_types.ty_view = ..
type term_view = Solver_types.term_view = ..
type value_view = Solver_types.value_view = ..
type lemma_view = Solver_types.lemma_view = ..
type decide_state = Solver_types.decide_state = ..

type tc_ty = Solver_types.tc_ty
type tc_term = Solver_types.tc_term
type tc_value = Solver_types.tc_value
type tc_lemma = Solver_types.tc_lemma

type term = Solver_types.term
type atom = Solver_types.atom
type clause = Solver_types.clause
type lemma = Solver_types.lemma
type actions = Solver_types.actions

(** Types *)
type ty = Solver_types.ty =
  | Bool
  | Ty of {
      mutable id: int;
      view: ty_view;
      tc: tc_ty;
    }

(** Semantic values in the model *)
type value = Solver_types.value =
  | V_true
  | V_false
  | V_value of {
      view : value_view;
      tc : tc_value;
    }

(** Result of evaluating a term in the current (partial) model *)
type eval_res = Solver_types.eval_res =
  | Eval_unknown
  | Eval_into of value * term list

type assignment_view = Solver_types.assignment_view =
  | A_bool of term * bool
  | A_semantic of term * value

type watch_res = Solver_types.watch_res =
  | Watch_keep
  | Watch_remove

type premise_step = Solver_types.premise_step =
  | Step_resolve of { c : clause; pivot : term; }

(** Result of checking satisfiability of a problem *)
type check_res = Solver_types.check_res =
  | Sat
  (** The current set of assumptions is satisfiable. *)
  | Unsat of atom list * lemma
  (** The current set of assumptions is *NOT* satisfiable, and here is a
      theory tautology (with its proof), for which every literal is false
      under the current assumptions. *)
