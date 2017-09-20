
(** {1 Lemmas} *)

open Solver_types

type t = lemma
type view = lemma_view

val pp : t CCFormat.printer

val tauto : t
val make : view -> tc_lemma -> t
