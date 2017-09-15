
open Solver_types

type t = premise

let prefix p = match p with
  | Hyp -> "H"
  | Lemma _ -> "T"
  | Simplify _ | P_hyper_res _ | P_steps _ -> "L"
  | _ -> "C"

let[@inline] pp_clause_name out { c_name=s; c_premise=p; _ } =
  Format.fprintf out "%s%d" (prefix p) s

let[@inline] hres l : t =
  assert (match l with []|[_] -> false | _ -> true);
  P_steps l

let[@inline] hres_or_simplify = function
  | [] -> assert false
  | [c] -> Simplify c
  | l -> P_steps l

let[@inline] hyper_res init steps =
  assert (steps<>[]);
  P_hyper_res {init;steps}

let pp out = function
  | Hyp -> Format.fprintf out "hyp"
  | Local -> Format.fprintf out "local"
  | Lemma l ->
    Format.fprintf out "th_lemma@ %a" Lemma.pp l
  | Simplify c -> Format.fprintf out "simpl %a" pp_clause_name c
  | P_steps v ->
    Fmt.fprintf out "steps{@[%a@]}" (Util.pp_list ~sep:"," pp_clause_name) v
  | P_hyper_res {init;steps} ->
    let pp_step out (_,c) = pp_clause_name out c in
    Format.fprintf out "hyper_res{@[%a;@,%a@]}"
      pp_clause_name init (Util.pp_list ~sep:";" pp_step) steps
