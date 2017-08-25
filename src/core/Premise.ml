
open Solver_types

type t = premise

let pp_premise out = function
  | Hyp -> Format.fprintf out "hyp"
  | Local -> Format.fprintf out "local"
  | Lemma _ -> Format.fprintf out "th_lemma"
  | History v -> List.iter (fun { name; _ } -> Format.fprintf out "%s,@ " name) v
