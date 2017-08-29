
open Solver_types

type t = premise

let pp out = function
  | Hyp -> Format.fprintf out "hyp"
  | Local -> Format.fprintf out "local"
  | Lemma _ -> Format.fprintf out "th_lemma"
  | History v ->
    List.iter (fun { c_name=s; _ } -> Format.fprintf out "%s,@ " s) v
