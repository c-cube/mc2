
open Solver_types

type t = premise

let prefix p = match p with
  | Hyp -> "H"
  | Lemma _ -> "T"
  | Simplify _ | Hyper_res _ -> "L"
  | _ -> "C"

let[@inline] pp_clause_name out { c_name=s; c_premise=p; _ } =
  Format.fprintf out "%s%d" (prefix p) s

let pp out = function
  | Hyp -> Format.fprintf out "hyp"
  | Local -> Format.fprintf out "local"
  | Lemma l ->
    Format.fprintf out "th_lemma@ %a" Lemma.pp l
  | Simplify c -> Format.fprintf out "simpl %a" pp_clause_name c
  | Hyper_res v ->
    Util.pp_list ~sep:"," pp_clause_name out v

let[@inline] hyper_res = function
  | [] | [_] -> assert false
  | l -> Hyper_res l
