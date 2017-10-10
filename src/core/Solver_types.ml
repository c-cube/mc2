
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
  tcty_refresh_state: level -> term -> unit; (** recompute internal {!decide_state} in new level *)
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
  mutable t_watches : term Vec.t lazy_t; (** terms that watch this term *)
  mutable t_assign: term_assignment; (** current assignment *)
  mutable t_nf: term option; (** used for rewriting *)
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

and tc_term = {
  tct_pp : term_view CCFormat.printer; (** print views of this plugin *)
  tct_init: actions -> term -> unit; (** called when term is added *)
  tct_update_watches: actions -> term -> watch:term -> watch_res;
  (** [watch] was assign, update term [t], and return whether [t] should
      still watch [watch] *)
  tct_delete: term -> unit;
  (** called when term is deleted *)
  tct_subterms: term_view -> (term->unit) -> unit; (** iterate on subterms *)
  tct_eval_bool : term -> eval_bool_res; (** Evaluate boolean term *)
  mutable tct_map : term -> (term -> term) -> term; (** Map function to subterms *)
}
(** type class for terms, packing all operations on terms *)

and watch_res =
  | Watch_keep (** Keep the watch *)
  | Watch_remove (** Remove the watch *)

and eval_bool_res =
  | Eval_unknown (** The given formula does not have an evaluation *)
  | Eval_bool of bool * (term * value) list
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

and check_res =
  | Sat
  (** The current set of assumptions is satisfiable. *)
  | Unsat of atom list * lemma
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
  | TA_eval of {
      mutable level : int; (** Decision level of the assignment *)
      mutable value: value;
      mutable reason: reason;
    }
  | TA_assign of {
      mutable level : int; (** Decision level of the assignment *)
      mutable value: value;
      mutable reason: reason;
    }
  | TA_both of {
      mutable level_eval: level;
      mutable value_eval: value;
      mutable reason_eval: reason;
      mutable level_assign: level;
      mutable value_assign: value;
      mutable reason_assign: reason
    } (** Two assignments *)

and clause = {
  c_name : int; (** Clause name, mainly for printing, unique. *)
  c_tag : int option; (** User-provided tag for clauses. *)
  c_atoms : atom array; (** The atoms that constitute the clause.*)
  mutable c_premise : premise;
  (** The premise of the clause, i.e. the justification of why the clause must
      be satisfied. *)
  mutable c_activity : float;   (** Clause activity, used for the heap heuristics. *)
  mutable c_fields: Clause_fields.t; (** bitfield for clauses *)
}
(** The type of clauses. Each clause generated should be true, i.e. enforced
    by the current problem (for more information, see the cpremise field). *)

and paramod_clause = {
  pc_lhs: term;
  pc_rhs: term;
  pc_guard: atom list;
  pc_premise: premise;
  pc_clause: clause lazy_t; (** view as a clause *)
}
(** A paramodulation clause, of the form [guard => (lhs = rhs)]. It is
    used to rewrite [lhs] into [rhs] assuming [guard] holds *)

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
  | Propagate_value of {
      rw_into: term; (** Term to rewrite into *)
      guard: atom list; (** Condition for rewriting to be valid *)
      lemma: lemma; (** justification *)
    }
  (** [t -> v] explained by [guard => (t = rewrite_into)] *)
  | Eval of (term * value) list
  (** The term can be evaluated using the terms in the list. Each
      term is bundled with the value it can evaluate into *)
(** Reasons of propagation/decision of atoms/terms. *)

and premise =
  | Hyp (** The clause is a hypothesis, provided by the user. *)
  | Local
  (** The clause is a 1-atom clause, where the atom is a local assumption *)
  | Lemma of lemma
  (** The clause is a theory-provided tautology, with the given proof. *)
  | Simplify of clause
  (** Deduplication/sorting of atoms in the clause *)
  | P_steps of {
      init: clause;
      steps: premise_step list; (* resolution steps *)
    }
  | P_raw_steps of raw_premise_step list
  (** The clause can be obtained by resolution or paramodulation of the clauses
      in the list, left-to-right.
      For a premise [History [a_1 :: ... :: a_n]] ([n >= 2]) the clause
      is obtained by performing resolution of [a_1] with [a_2], and then
      performing a resolution step between the result and [a_3], etc...  Of
      course, each of the clause [a_i] also has its own premise.
  *)
(** Premises for clauses. Indeed each clause generated during a run of the solver
    should be satisfied, the premise is the justification of why it should be
    satisfied by the solver.

    The premise of a clause can be updated, during proof processing,
    going from [Hyper_res l] towards explicit steps of resolution
    with [Resolve]. This update preserves the semantics of proofs
    but acts as a memoization of the proof reconstruction process. *)

(** Clause or paramodulation, raw form *)
and raw_premise_step =
  | RP_resolve of clause (** resolution with clause *)
  | RP_paramod of paramod_atom (** Paramodulation on one atom *)

(** Clause or paramodulation, refined form *)
and premise_step =
  | Step_resolve of {
      c: clause; (** clause to resolve with *)
      pivot: term; (** pivot to remove *)
    }
  | Step_paramod of paramod_atom

and paramod_trace = {
  pt_id: int; (* unique ID *)
  pt_lhs: term;
  pt_rhs: term;
  pt_steps: paramod_step list;
}
(** rewrite [lhs] into [rhs] such that:
    - [can_eval[trail] t v]
    - [step] is a transitive list of equalities that starts with [lhs]
        and ends with [rhs]
*)

and paramod_step =
  | PS_paramod of {
      pc: paramod_clause;
    } (** rewrite [lhs] into [rhs] such that:
          - [can_eval[trail] t v]
          - [pc] is a clause with head [lhs=rhs] *)
  | PS_sub of {
      subs: paramod_trace list;
    } (** given the list of sub-paramodulations [subs], lhs=rhs *)

(** Paramodulation of atoms *)
and paramod_atom = {
  pa_init: atom;
  pa_learn: atom option; (** if result not absurd (otherwise [false]) *)
  pa_trace: paramod_trace; (** rewrite [init.term -> learn.term] *)
}

and lemma =
  | Lemma_bool_tauto (** tautology [a ∨ ¬a] *)
  | Lemma_custom of {
      view: lemma_view; (** The lemma content *)
      tc: tc_lemma; (** Methods on the lemma *)
    } (** A lemma belonging to some plugin. Must be a tautology of the theory. *)

and tc_lemma = {
  tcl_pp : lemma_view CCFormat.printer;
}

and actions = {
  act_push_clause : clause -> unit;
  (** push a new clause *)
  act_level : unit -> level;
  (** access current decision level *)
  act_propagate_bool_eval : term -> bool -> subs:(term * value) list -> unit;
  (** [act_propagate_bool_eval t b l] propagates the boolean literal [t]
      assigned to boolean value [b], explained by evaluation with
      relevant (sub)terms [l]
      @param subs subterms used for the propagation *)
  act_propagate_bool_lemma : term -> bool -> atom list -> lemma -> unit;
  (** [act_propagate_bool_lemma t b c] propagates the boolean literal [t]
      assigned to boolean value [b], explained by a valid theory
      lemma [c].
      Precondition: [c] is a tautology such that [c == (c' ∨ t=b)], where [c']
      is composed of atoms false in current model.
  *)
  act_propagate_val_eval : term -> value -> subs:(term * value) list -> unit;
  (** [act_propagate_val_eval t v l] propagates the term [t]
      assigned to value [v], explained by evaluation with
      relevant (sub)terms [l]
      @param subs subterms used for the propagation *)
  act_propagate_val_lemma : term -> value -> rw_into:term -> atom list -> lemma -> unit;
  (** [act_propagate_val_lemma t v ~rw_into c l]
      propagates the term [t] assigned to value [v],
      explained by a valid theory lemma [c => (t = rw_into)].
      It is necessary that [rw_into] evaluates to [v] in the current model.
      Precondition: [c] is a list of true atoms such that [c => (t = rw_into)].
  *)
  act_mark_dirty : term -> unit;
  (** Mark the term as dirty because its set of unit constraints has changed.
      It potentially has to re-compute new information from that
      (e.g. lower/upper bounds, set of forbidden values, etc.). *)
  act_raise_conflict: 'a. atom list -> lemma -> 'a;
  (** Raise a conflict with the given clause, which must be false
      in the current trail, and with a lemma to explain *)
  act_on_backtrack : level -> (unit -> unit) -> unit;
  (** [act_on_backtrack level f] will call [f] when the given [level]
      is backtracked *)
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
let field_t_dirty = Term_fields.mk_field() (** needs to update unit constraints? *)
let field_t_inconsistent = Term_fields.mk_field() (** assignment is inconsistent (BCP/eval). At most one per conflict *)

let field_c_attached = Clause_fields.mk_field() (** clause added to state? *)
let field_c_visited = Clause_fields.mk_field() (** visited during some traversal? *)
let field_c_deleted = Clause_fields.mk_field() (** deleted during GC *)
let field_c_gc_marked = Clause_fields.mk_field() (** clause is alive for GC *)

type term_view += Dummy

let tct_default : tc_term = {
  tct_pp=(fun _ _ -> assert false);
  tct_init=(fun _ _ -> ());
  tct_update_watches=(fun _ _ ~watch:_ -> Watch_keep);
  tct_delete=(fun _ -> ());
  tct_subterms=(fun _ _ -> ());
  tct_eval_bool=(fun _ -> Eval_unknown);
  tct_map=(fun t _ -> t);
}

let dummy_tct : tc_term = tct_default

let rec dummy_term : term = {
  t_id= ~-1;
  t_tc=dummy_tct;
  t_idx= ~-1;
  t_view=Dummy;
  t_ty=Bool;
  t_fields= Term_fields.empty;
  t_weight= -1.;
  t_var=Var_none;
  t_watches=lazy (Vec.make_empty dummy_term);
  t_assign=TA_none;
  t_nf=None;
}

let dummy_clause : clause = {
  c_name = -1;
  c_tag = None;
  c_atoms = [| |];
  c_activity = -1.;
  c_fields = Clause_fields.empty;
  c_premise = Hyp;
}

let dummy_atom : atom = {
  a_id= -1;
  a_term=dummy_term;
  a_watched=Vec.make_empty dummy_clause;
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
