
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

(** {2 Type definitions} *)

type plugin_id = int

type term_view = ..
(** Extensible view. Each plugin might declare its own terms. *)

type lemma = ..
(** Extensible proof object
    FIXME: shouldn't this be simpler? or more complicated, like typeclass + variant*)

type term = {
  mutable t_id: int;
  (** unique ID, made of:
      - 4 bits plugin_id
      - the rest is for plugin-specific id *)
  t_view: term_view;
  (** view *)
  t_ty: Type.t;
  (** type of the term *)
  mutable t_fields: Term_fields.t;
  (** bitfield for storing various info *)
  mutable t_level : int; (** Decision level of the assignment *)
  mutable t_weight : float; (** Weight (for the heap) *)
  mutable t_reason : reason option;
  (** The reason for propagation/decision of the literal *)
  t_var: var;
}

and var =
  (** Semantic variable *)
  | V_semantic of {
      mutable v_value : term option; (** Assignment *)
      mutable v_watched : term Vec.t; (* watched terms *)
    }

  (** Bool variable *)
  | V_bool of {
      pa : atom; (** Link for the positive atom *)
      na : atom; (** Link for the negative atom *)
    }

and atom = {
  a_id : int; (** Unique identifier *)
  a_term : term ; (** Link for the parent variable *)
  a_neg : atom; (** Link for the negation of the atom *)
  mutable a_is_true : bool;
  (** Is the atom true ? Conversely, the atom is false iff a.neg.is_true *)
  mutable a_watched : clause Vec.t; (** The vector of clauses that watch this atom *)
}
(** Atoms and variables wrap theory formulas. They exist in the form of
    triplet: a variable and two atoms. For a formula [f] in normal form,
    the variable v points to the positive atom [a] which wraps [f], while
    [a.neg] wraps the theory negation of [f]. *)

and clause = {
  c_name : string; (** Clause name, mainly for printing, unique. *)
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

and reason =
  | Decision
  (** The atom has been decided by the sat solver *)
  | Bcp of clause
  (** The atom has been propagated by the given clause *)
  | Semantic
  (** The atom has been propagated by the theory at the given level. *)
(** Reasons of propagation/decision of atoms. *)

and premise =
  | Hyp (** The clause is a hypothesis, provided by the user. *)
  | Local
  (** The clause is a 1-atom clause, where the atom is a local assumption *)
  | Lemma of lemma
  (** The clause is a theory-provided tautology, with the given proof. *)
  | History of clause list
  (** The clause can be obtained by resolution of the clauses
      in the list. If the list has a single element [c] , then the clause can
      be obtained by simplifying [c] (i.e eliminating doublons in its atom
      list).  For a premise [History [a_1 :: ... :: a_n]] ([n > 0]) the clause
      is obtained by performing resolution of [a_1] with [a_2], and then
      performing a resolution step between the result and [a_3], etc...  Of
      course, each of the clause [a_i] also has its own premise.
  *)
(** Premises for clauses. Indeed each clause generated during a run of the solver
    should be satisfied, the premise is the justification of why it should be
    satisfied by the solver. *)

(** {2 Decisions and propagations} *)
type assignment =
  | Assign_term of term
  | Assign_atom of atom
  (** Either a lit of an atom *)

