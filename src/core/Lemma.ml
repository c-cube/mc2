
(** {1 Lemmas} *)

open Solver_types

type t = lemma
type view = lemma_view

let[@inline] pp out (l:t) = match l with
  | Lemma_bool_tauto -> Fmt.string out "bool_tauto"
  | Lemma_custom {view;tc} -> tc.tcl_pp out view

let tauto = Lemma_bool_tauto
let[@inline] make view tc: t = Lemma_custom {view;tc}

module TC = struct
  type t = tc_lemma

  let make ~pp () : t = { tcl_pp=pp }

end
