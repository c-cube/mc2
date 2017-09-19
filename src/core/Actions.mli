
(** {1 Actions for Plugins} *)

(** Plugins are given a set of possible actions at certain times, such as propagation
    or first-time addition of watches to a term. *)

open Solver_types

type t = actions

val push_clause : t -> clause -> unit

val level : t -> level

val propagate_bool_eval : t -> term -> bool -> subs:term list -> unit

val propagate_bool_lemma : t -> term -> bool -> atom list -> lemma -> unit

val raise_conflict : t -> atom list -> lemma -> 'a

val on_backtrack : t -> (unit -> unit) -> unit

