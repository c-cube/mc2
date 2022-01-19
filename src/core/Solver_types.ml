
(** Internal types (implementation)

    This modules actually implements the internal types used by the solver.
    Since mutation is heavily used in the solver, it is really, really, *really*
    discouraged to direclty use the functions in this module if you don't know the
    inner working of mSAT perfectly as even the simplest
    change can have dramatic effects on the solver.
*)

(** Internal types (interface)

    This modules defines the interface of most of the internal types
    used in the core solver.
*)

module Term_fields = BitField.Make(struct end)
module Clause_fields = BitField.Make(struct end)

module Option = Util.Option
module Fmt = CCFormat
module Int_map = Util.Int_map

(** {2 Type definitions} *)

type plugin_id = int
type level = int

type term_view = ..
(** Extensible view on terms (generalized variables).
    Each plugin might declare its own terms. *)

type value_view = ..
(** Extensible view on values. *)

type decide_state = ..
(** State carried by a given term, depending on its type, and used
    for decisions and propagations related to the term.
    Typically it contains a set of constraints on the values this
    term can have (lower/upper bounds, etc.)
*)

type lemma_view = ..
(** Extensible proof object *)

type ty_view = ..
(** Extensible view on types *)

(** Types *)
type ty =
  | Bool (** Builtin type of booleans *)
  | Ty of {
      mutable id: int; (** unique ID of the type *)
      view: ty_view;
      tc: tc_ty; (** operations *)
    }
  (** An atomic type, with some attached data *)

and tc_ty = {
  tcty_decide: actions -> term -> value;
  (** How to make semantic decisions for terms of this type? *)
  tcty_eq: term -> term -> term;
  (* how to build equalities between terms of that type *)
  tcty_pp: ty_view CCFormat.printer; (** print types *)
  tcty_mk_state: unit -> decide_state; (** decide state for a new term *)
}

and term = {
  t_tc: tc_term; (** typeclass for the term *)
  mutable t_id: int;
  (** unique ID, made of:
      - [k] bits plugin_id (with k small)
      - the rest is for plugin-specific id *)
  t_view: term_view; (** view *)
  t_ty: ty; (** type of the term *)
  mutable t_idx: int; (** position in heap *)
  mutable t_weight : float; (** Weight (for the heap), tracking activity *)
  mutable t_fields: Term_fields.t;
  (** bitfield for storing various info *)
  mutable t_var: var;
  (** The "generalized variable" part, for assignments. *)
  mutable t_watches : watcher Vec.t; (** terms that watch this term *)
  mutable t_assign: term_assignment; (** current assignment *)
}
(** Main term representation. A {!term}, contains almost all information
    necessary to process it, including:

    - its unique ID
    - its plugin-specific representation (possibly with subterms)
    - its current assignment, level, weight, etc.
    - some info related to its position in the queue of terms to decide

    It is worth noting that terms are also (generalized) {i variables}
    and behave mostly the same as boolean variables for the main
    solver, meaning that they need to be assigned a value in the model.
*)

and watcher = (actions -> term -> watch_res)
(** [w acts t] means [t] was assigned, so we update some internal state
    and return whether [w] should still watch [t]. *)

and tc_term = {
  tct_pp : term_view CCFormat.printer; (** print views of this plugin *)
  tct_init: actions -> term -> unit; (** called when term is added *)
  tct_delete: term -> unit;
  (** called when term is deleted *)
  tct_subterms: term_view -> term Iter.t; (** iterate on immediate subterms *)
  tct_eval: term -> eval_res; (** Evaluate term *)
}
(** type class for terms, packing all operations on terms *)

and watch_res =
  | Watch_keep (** Keep the watch *)
  | Watch_remove (** Remove the watch *)

and eval_res =
  | Eval_unknown (** The given formula does not have an evaluation *)
  | Eval_into of value * term list
  (** The given formula can be evaluated to the given value.
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

and check_res =
  | Sat
  (** The current set of assumptions is satisfiable. *)
  | Unsat of atom list
  (** The current set of assumptions is *NOT* satisfiable, and here is a
      theory tautology (with its proof), for which every literal is false
      under the current assumptions. *)

and value =
  | V_true
  | V_false
  | V_value of {
      view: value_view; (** Actual shape of the value *)
      tc: tc_value; (** typeclass for values *)
    }
  (** A semantic value, part of the model's domain.
      For arithmetic, it would
      be a number; for arrays, a finite map + default value; etc.
      Note that terms map to values in the model but that values are
      not necessarily normal "terms" (i.e. generalized variables in
      the MCSat sense).
  *)
(** A value, either boolean or semantic *)

(** The "generalized variable" part of a term, containing the
    current assignment, watched literals/terms, etc. *)
and var =
  | Var_semantic of {
      mutable v_decide_state: decide_state; (** used for decisions/assignments *)
    } (** Semantic variable *)
  | Var_bool of {
      pa : atom; (** Link for the positive atom *)
      na : atom; (** Link for the negative atom *)
    } (** Bool variable *)
  | Var_none (** Not a variable yet (not added) *)

and atom = {
  a_id : int; (** Unique identifier *)
  a_term : term; (** Link for the parent variable *)
  mutable a_watched : clause Vec.t; (** The vector of clauses that watch this atom *)
}
(** Atoms and variables wrap theory formulas. They exist in the form of
    triplet: a variable and two atoms. For a formula [f] in normal form,
    the variable v points to the positive atom [a] which wraps [f], while
    [a.neg] wraps the theory negation of [f]. *)

(** The value(s) and reason(s) for propagation/decision
    and evaluation of the term *)
and term_assignment =
  | TA_none
  | TA_assign of {
      level : int; (** Decision level of the assignment *)
      value: value;
      reason: reason;
    }

and clause = {
  c_name : int; (** Clause name, mainly for printing, unique. *)
  c_tag : int option; (** User-provided tag for clauses. *)
  c_atoms : atom array; (** The atoms that constitute the clause.*)
  mutable c_activity : float;   (** Clause activity, used for the heap heuristics. *)
  mutable c_fields: Clause_fields.t; (** bitfield for clauses *)
}
(** The type of clauses. Each clause generated should be true, i.e. enforced
    by the current problem (for more information, see the cpremise field). *)

and tc_value = {
  tcv_pp : value_view CCFormat.printer; (** printer *)
  tcv_equal : value_view -> value_view -> bool; (** equality *)
  tcv_hash : value_view -> int; (** hash function *)
}
(** Methods for values *)

and reason =
  | Decision
  (** The atom has been decided by the sat solver *)
  | Bcp of clause
  (** The atom has been propagated by the given clause *)
  | Bcp_lazy of clause lazy_t
  (** Same as {!Bcp} but the clause is produced on demand
      (typically, useful for theory propagation) *)
  | Eval of term list
  (** The term can be evaluated using the terms in the list. Each
      term has a value. *)
(** Reasons of propagation/decision of atoms/terms. *)


and actions = {
  act_push_clause : clause -> unit;
  (** push a new clause. This clause is added to the solver and will
      not be backtracked. *)
  act_level : unit -> level;
  (** access current decision level *)
  act_propagate_bool_eval : term -> bool -> subs:term list -> unit;
  (** [act_propagate_bool_eval t b l] propagates the boolean literal [t]
      assigned to boolean value [b], explained by evaluation with
      relevant (sub)terms [l]
      @param subs subterms used for the propagation *)
  act_propagate_bool_lemma : term -> bool -> atom list -> unit;
  (** [act_propagate_bool_lemma t b c] propagates the boolean literal [t]
      assigned to boolean value [b], explained by a valid theory
      lemma [c].
      Precondition: [c] is a tautology such that [c == (c' ∨ t=b)], where [c']
      is composed of atoms false in current model.
  *)
  act_raise_conflict: 'a. atom list -> 'a;
  (** Raise a conflict with the given clause, which must be false
      in the current trail, and with a lemma to explain *)
  act_on_backtrack : (unit -> unit) -> unit;
  (** [act_on_backtrack f] will call [f] when we backtrack *)
}
(** Actions available to terms/plugins when doing propagation/model building,
    including adding clauses, registering actions to do upon
    backtracking, etc. *)

let field_t_is_deleted = Term_fields.mk_field () (** term deleted during GC? *)
let field_t_is_added = Term_fields.mk_field() (** term added to core solver? *)
let field_t_mark_pos = Term_fields.mk_field() (** positive atom marked? *)
let field_t_mark_neg = Term_fields.mk_field() (** negative atom marked? *)
let field_t_seen = Term_fields.mk_field() (** term seen during some traversal? *)
let field_t_negated = Term_fields.mk_field() (** negated term? *)
let field_t_gc_marked = Term_fields.mk_field() (** marked for GC? *)

let field_c_lemma = Clause_fields.mk_field() (** clause is deduced (a lemma) *)
let field_c_attached = Clause_fields.mk_field() (** clause added to state? *)
let field_c_visited = Clause_fields.mk_field() (** visited during some traversal? *)
let field_c_deleted = Clause_fields.mk_field() (** deleted during GC *)
let field_c_gc_marked = Clause_fields.mk_field() (** clause is alive for GC *)

type term_view += Dummy

let tct_default : tc_term = {
  tct_pp=(fun _ _ -> assert false);
  tct_init=(fun _ _ -> ());
  tct_delete=(fun _ -> ());
  tct_subterms=(fun _ _ -> ());
  tct_eval=(fun _ -> Eval_unknown);
}

type bool_term = term (** Alias for boolean terms *)

(** {2 Decisions and propagations} *)

type trail = term Vec.t
(** A trail is a vector of assignments. An assignment is simply
    a term whose value is decided. *)

type assignment_view =
  | A_bool of term * bool
  | A_semantic of term * value

type 'a or_conflict = ('a, clause) CCResult.t
(** Either an ['a], or a conflict clause *)

(* TODO: datatypes, in a plugin
type data = {
  data_id: ID.t;
  data_cstors: cstor ID.Map.t lazy_t;
  data_as_ty: ty lazy_t;
}

and cstor = {
  cstor_id: ID.t;
  cstor_is_a: ID.t;
  mutable cstor_arity: int;
  cstor_args: select list lazy_t;
  cstor_ty_as_data: data;
  cstor_ty: ty lazy_t;
}

and select = {
  select_id: ID.t;
  select_cstor: cstor;
  select_ty: ty lazy_t;
  select_i: int;
}
   *)

type bound_var = ID.t * ty

(** Function definition *)
type definition = ID.t * bound_var list * ty * term

type statement =
  | Stmt_set_logic of string
  | Stmt_set_option of string list
  | Stmt_set_info of string * string
  (* | Stmt_data of data list *)
  | Stmt_ty_decl of ID.t * int (* new atomic cstor *)
  | Stmt_decl of ID.t * ty list * ty
  | Stmt_define of definition list
  | Stmt_assert_clauses of atom list list
  | Stmt_check_sat
  | Stmt_exit

let pp_clause_name out c =
  let prefix = if Clause_fields.get field_c_lemma c.c_fields then "L" else "H" in
  Format.fprintf out "%s%d" prefix c.c_name

