
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
module Statement = Statement
module Bound_var = Bound_var
module Error = Error

(**/**)
module Util = Util
module Log = Log
(**/**)

module Fmt = CCFormat
module Int_map = Util.Int_map

type level = Solver_types.level
(** Backtracking level *)

type ty_view = Solver_types.ty_view = ..
(** Extensible view on types *)

type term_view = Solver_types.term_view = ..
(** Extensible view on terms (generalized variables).
    Each plugin might declare its own terms. *)

type value_view = Solver_types.value_view = ..
(** Extensible view on values. *)

type lemma_view = Solver_types.lemma_view = ..
(** Extensible proof object *)

type decide_state = Solver_types.decide_state = ..
(** State carried by a given term, depending on its type, and used
    for decisions and propagations related to the term.
    Typically it contains a set of constraints on the values this
    term can have (lower/upper bounds, etc.)
*)

type tc_ty = Solver_types.tc_ty

type tc_term = Solver_types.tc_term
(** type class for terms, packing all operations on terms *)

type tc_value = Solver_types.tc_value
type tc_lemma = Solver_types.tc_lemma

type term = Solver_types.term
(** Main term representation.
    It is worth noting that terms are also (generalized) {i variables}
    and behave mostly the same as boolean variables for the main
    solver, meaning that they need to be assigned a value in the model.
*)

type atom = Solver_types.atom
(** Atoms and variables wrap theory formulas. They exist in the form of
    triplet: a variable and two atoms. For a formula [f] in normal form,
    the variable v points to the positive atom [a] which wraps [f], while
    [a.neg] wraps the theory negation of [f]. *)

type clause = Solver_types.clause
(** The type of clauses. Each clause generated should be true, i.e. enforced
    by the current problem (for more information, see the cpremise field). *)

type lemma = Solver_types.lemma =
  | Lemma_bool_tauto (** tautology [a ∨ ¬a] *)
  | Lemma_custom of {
      view: lemma_view; (** The lemma content *)
      tc: tc_lemma; (** Methods on the lemma *)
    } (** A lemma belonging to some plugin. Must be a tautology of the theory. *)

type actions = Solver_types.actions
(** Actions available to terms/plugins when doing propagation/model building,
    including adding clauses, registering actions to do upon
    backtracking, etc. *)

(** Types *)
type ty = Solver_types.ty =
  | Bool (** Builtin type of booleans *)
  | Ty of {
      mutable id: int;
      view: ty_view;
      tc: tc_ty;
    }
  (** An atomic type, with some attached data *)

(** A value, either boolean or semantic *)
type value = Solver_types.value =
  | V_true
  | V_false
  | V_value of {
      view : value_view;
      tc : tc_value;
    }
  (** A semantic value, part of the model's domain.
      For arithmetic, it would
      be a number; for arrays, a finite map + default value; etc.
      Note that terms map to values in the model but that values are
      not necessarily normal "terms" (i.e. generalized variables in
      the MCSat sense).
  *)

(** The "generalized variable" part of a term, containing the
    current assignment, watched literals/terms, etc. *)
type var = Solver_types.var

(** The type of evaluation results for a given formula.
    For instance, let's suppose we want to evaluate the formula [x * y = 0], the
    following result are correct:
    - [Unknown] if neither [x] nor [y] are assigned to a value
    - [Valued (true, [x])] if [x] is assigned to [0]
    - [Valued (true, [y])] if [y] is assigned to [0]
    - [Valued (false, [x; y])] if [x] and [y] are assigned to 1 (or any non-zero number)
*)
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

type statement = Statement.t
