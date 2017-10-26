(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(** Resolution proofs

    This modules defines functions to create and manipulate resolution proofs.
*)

open Solver_types

(** {3 Type declarations} *)

type t
(** Lazy type for proof trees. Proofs are persistent objects, and can be
    extended to proof nodes using functions defined later. *)

and node = {
  conclusion : clause;  (** The conclusion of the proof *)
  step : step;          (** The reasoning step used to prove the conclusion *)
}
(** A proof can be expanded into a proof node, which show the first step of the proof. *)
and step =
  | Hypothesis
  (** The conclusion is a user-provided hypothesis *)
  | Assumption
  (** The conclusion has been locally assumed by the user *)
  | Lemma of lemma
  (** The conclusion is a tautology provided by the theory, with associated proof *)
  | Simplify of {
      init: t;
      duplicates: atom list;
      absurd: atom list;
    }
  (** The conclusion is obtained by eliminating multiple occurrences of atoms in
      the conclusion of the provided proof, and removing some absurd atoms. *)
  | Hyper_res of {
      init: t;
      steps: premise_step list; (* list of steps to apply to [init] *)
    }
  (** The conclusion can be deduced by performing a series of resolution steps
      between [init] and, successively, each clause in the list on the
      corresponding pivot atom. *)
(** The type of reasoning steps allowed in a proof. *)

val conclusion : node -> clause
val step : node -> step

(** {3 Proof building functions} *)

val prove : clause -> t
(** Given a clause, return a proof of that clause.
    @raise Util.Error if it does not succeed. *)

val prove_unsat : clause -> t
(** Given a conflict clause [c], returns a proof of the empty clause.
    @raise Util.Error if it does not succeed *)

val prove_atom : atom -> t option
(** Given an atom [a], returns a proof of the clause [\[a\]] if [a] is true at level 0 *)

(** {3 Proof Nodes} *)

val is_leaf : step -> bool
(** Returns whether the proof node is a leaf, i.e. an hypothesis,
    an assumption, or a lemma.
    [true] if and only if {parents} returns the empty list. *)

val expl : step -> string
(** Returns a short string description for the proof step; for instance
    ["hypothesis"] for a [Hypothesis]
    (it currently returns the variant name in lowercase). *)

val parents : step -> t list
(** Returns the parents of a proof node. *)

(** {3 Proof Manipulation} *)

val expand : t -> node
(** Return the proof step at the root of a given proof. *)

val fold : ('a -> node -> 'a) -> 'a -> t -> 'a
(** [fold f acc p], fold [f] over the proof [p] and all its node. It is guaranteed that
    [f] is executed exactly once on each proof node in the tree, and that the execution of
    [f] on a proof node happens after the execution on the parents of the nodes. *)

val iter : (node -> unit) -> t -> unit

val unsat_core : t -> clause list
(** Returns the unsat_core of the given proof, i.e the lists of conclusions of all leafs of the proof.
    More efficient than using the [fold] function since it has access to the internal representation of proofs *)

val debug_step : step CCFormat.printer

(** {3 Misc} *)

val check : t -> unit
(** Check the contents of a proof. Mainly for internal use *)

(** {3 Unsafe} *)

module H : Hashtbl.S with type key = clause
(** Hashtable over clauses. Uses the details of the internal representation
    to achieve the best performances, however hashtables from this module
    become invalid when solving is restarted, so they should only be live
    during inspection of a single proof. *)

