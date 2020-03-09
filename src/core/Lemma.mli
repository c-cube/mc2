
(** {1 Lemmas} *)

open Solver_types

type t = lemma
type view = lemma_view

val pp : t CCFormat.printer

val tauto : t
val make : view -> tc_lemma -> t

module TC : sig
  type t = tc_lemma

  val make :
    pp:view Fmt.printer ->
    unit ->
    t
end
