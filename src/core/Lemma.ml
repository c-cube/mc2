
(** {1 Lemmas} *)

open Solver_types

type t = lemma
type view = lemma_view

let[@inline] view l = l.lemma_view
let[@inline] pp out (l:t) = l.lemma_tc.tcl_pp out l.lemma_view

let make lemma_view lemma_tc: t = { lemma_view; lemma_tc }
