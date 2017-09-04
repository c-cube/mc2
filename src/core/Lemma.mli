
(** {1 Lemmas} *)

open Solver_types

type t = lemma
type view = lemma_view

val view : t -> view
val pp : t CCFormat.printer

val make : view -> tc_lemma -> t
