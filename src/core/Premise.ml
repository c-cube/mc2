
open Solver_types

type t = premise

let prefix p = match p with
  | Hyp -> "H"
  | Lemma _ -> "T"
  | Simplify _ | P_hyper_res _ | P_steps _ -> "L"
  | _ -> "C"

let[@inline] pp_clause_name out { c_name=s; c_premise=p; _ } =
  Format.fprintf out "%s%d" (prefix p) s

let[@inline] pp_atom_id out {a_id;_} = Fmt.int out a_id

let empty_paramod = Paramod_none

let[@inline] hres ?(paramod=empty_paramod) l : t =
  assert (match l with []|[_] -> false | _ -> true);
  P_steps {cs=l; paramod}

let[@inline] hres_or_simplify ?(paramod=empty_paramod) l = match paramod, l with
  | _, [] -> assert false
  | Paramod_none, [c] -> Simplify c
  | _ -> P_steps {cs=l;paramod}

let[@inline] hyper_res ?(paramod=empty_paramod) init steps =
  assert (steps<>[]);
  P_hyper_res {init;steps;paramod}

let pp_paramod out = function
  | Paramod_none -> ()
  | Paramod_some {pivots;_} ->
    Fmt.fprintf out "@ :paramod (@[%a@])" (Util.pp_list pp_atom_id) pivots

let pp out = function
  | Hyp -> Format.fprintf out "hyp"
  | Local -> Format.fprintf out "local"
  | Lemma l ->
    Format.fprintf out "th_lemma@ %a" Lemma.pp l
  | Simplify c -> Format.fprintf out "simpl %a" pp_clause_name c
  | P_steps {cs;paramod} ->
    Fmt.fprintf out "steps{@[%a%a@]}"
      (Util.pp_list ~sep:"," pp_clause_name) cs pp_paramod paramod
  | P_hyper_res {init;steps;paramod} ->
    let pp_step out (_,c) = pp_clause_name out c in
    Format.fprintf out "hyper_res{@[%a;@,%a%a@]}"
      pp_clause_name init (Util.pp_list ~sep:";" pp_step) steps
      pp_paramod paramod
