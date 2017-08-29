
open Solver_types

type t = premise

let prefix p = match p with
  | Hyp -> "H"
  | Lemma _ -> "T"
  | History _ -> "L"
  | _ -> "C"

let pp out = function
  | Hyp -> Format.fprintf out "hyp"
  | Local -> Format.fprintf out "local"
  | Lemma _ -> Format.fprintf out "th_lemma"
  | History v ->
    List.iter
      (fun { c_name=s; c_premise=p; _ } ->
         Format.fprintf out "%s%d,@ " (prefix p) s)
      v
