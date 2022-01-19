
(** {1 Actions for Plugins} *)

(** Plugins are given a set of possible actions at certain times, such as propagation
    or first-time addition of watches to a term. *)

open Solver_types

type t = actions
(** Actions available to terms/plugins when doing propagation/model building,
    including adding clauses, registering actions to do upon
    backtracking, etc. *)

val push_clause : t -> clause -> unit
(** push a new clause. This clause is added to the solver and will
    not be backtracked. *)

val level : t -> level
(** access current decision level *)

val propagate_bool_eval : t -> term -> bool -> subs:term list -> unit
(** [propagate_bool_eval t b l] propagates the boolean literal [t]
    assigned to boolean value [b], explained by evaluation with
    relevant (sub)terms [l]
    @param subs subterms used for the propagation *)

val propagate_bool_lemma : t -> term -> bool -> atom list -> unit
(** [propagate_bool_lemma t b c] propagates the boolean literal [t]
      assigned to boolean value [b], explained by a valid theory
      lemma [c].
      Precondition: [c] is a tautology such that [c == (c' ∨ t=b)], where [c']
      is composed of atoms false in current model.
*)

val raise_conflict : t -> atom list -> 'a
(** Raise a conflict with the given clause, which must be false
    in the current trail, and with a lemma to explain *)

val on_backtrack : t -> (unit -> unit) -> unit
(** [on_backtrack f] will call [f] when the solver backtracks *)

