
(** {1 Actions for Plugins} *)

(** Plugins are given a set of possible actions at certain times, such as propagation
    or first-time addition of watches to a term. *)

open Solver_types

type t = actions

val push_clause : t -> clause -> unit

val level : t -> level

val propagate_bool : t -> term -> bool -> subs:term list -> unit

val mark_dirty : t -> term -> unit

val raise_conflict : t -> atom list -> lemma -> 'a

val on_backtrack : t -> level -> (unit -> unit) -> unit

val mark_dirty_on_backtrack : t -> term -> unit
(** [mark_dirty_on_backtrack acts t] will mark [t] as dirty once we
    backtrack below current level.
    Short for [on_backtrack acts (level acts) (fun () -> mark_dirty acts t)].

    To be called, typically, by a plugin on a term [t] when some other
    term becomes a unit constraint on [t]
*)
