
open Solver_types

type t = premise

let prefix p = match p with
  | Hyp -> "H"
  | Lemma _ -> "T"
  | Simplify _ | Hyper_res _ | Resolve _ -> "L"
  | _ -> "C"

let[@inline] pp_clause_name out { c_name=s; c_premise=p; _ } =
  Format.fprintf out "%s%d" (prefix p) s

let[@inline] hyper_res l : t =
  assert (match l with []|[_] -> false | _ -> true);
  Hyper_res l

let[@inline] hyper_res_or_simplify = function
  | [] -> assert false
  | [c] -> Simplify c
  | l -> Hyper_res l

let[@inline] resolve pivot c1 c2 : t = Resolve{c1;c2;pivot}

let pp out = function
  | Hyp -> Format.fprintf out "hyp"
  | Local -> Format.fprintf out "local"
  | Lemma l ->
    Format.fprintf out "th_lemma@ %a" Lemma.pp l
  | Simplify c -> Format.fprintf out "simpl %a" pp_clause_name c
  | Resolve{c1;c2;_} ->
    Format.fprintf out "res{%a;%a}" pp_clause_name c1 pp_clause_name c2
  | Hyper_res v ->
    Fmt.fprintf out "hres{@[<hv>%a@]}" (Util.pp_list ~sep:"," pp_clause_name) v
