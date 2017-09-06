
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
  | Lemma l ->
    Format.fprintf out "th_lemma@ %a" Lemma.pp l
  | History v ->
    Util.pp_list ~sep:","
      (fun out { c_name=s; c_premise=p; _ } ->
         Format.fprintf out "%s%d" (prefix p) s)
      out v
