
open Solver_types

type t = premise

let prefix p = match p with
  | Hyp -> "H"
  | Lemma _ -> "T"
  | Simplify _ | P_raw_steps _ | P_steps _ -> "L"
  | _ -> "C"

let[@inline] pp_clause_name out { c_name=s; c_premise=p; _ } =
  Format.fprintf out "%s%d" (prefix p) s

let[@inline] pp_term_id out {t_id;_} = Fmt.int out t_id

(* negation of the atom *)
let[@inline] atom_is_pos (a:atom) : bool = match a.a_term.t_var with
  | Var_bool { pa; _ } -> a==pa
  | Var_none | Var_semantic _ -> assert false

let[@inline] pp_atom_id out a =
  Fmt.fprintf out "%s%d" (if atom_is_pos a then "+" else "-") a.a_term.t_id

let[@inline] raw_steps l : t =
  assert (match l with []|[_] -> false | _ -> true);
  P_raw_steps l

let[@inline] raw_steps_or_simplify l = match l with
  | [RP_resolve c] -> Simplify c
  | [] | [_] -> assert false
  | _ -> P_raw_steps l

let[@inline] steps init steps =
  assert (steps<>[]);
  P_steps {init;steps}

let[@inline] res_is_absurd (pa:paramod_atom): bool = CCOpt.is_none pa.pa_learn

let[@inline] pp_raw_premise_step out = function
  | RP_resolve c -> pp_clause_name out c
  | RP_paramod pa ->
    begin match pa.pa_learn with
      | None ->
        Fmt.fprintf out "rw(%a→⊥)" pp_atom_id pa.pa_init
      | Some learn ->
        Fmt.fprintf out "(%a=%a)" pp_atom_id pa.pa_init pp_atom_id learn
    end

let[@inline] pp_premise_step out = function
  | Step_resolve {c;_} -> pp_clause_name out c
  | Step_paramod pa ->
    begin match pa.pa_learn with
      | None ->
        Fmt.fprintf out "rw(%a→⊥)" pp_atom_id pa.pa_init
      | Some learn ->
        Fmt.fprintf out "(%a=%a)" pp_atom_id pa.pa_init pp_atom_id learn
    end

let pp out = function
  | Hyp -> Format.fprintf out "hyp"
  | Local -> Format.fprintf out "local"
  | Lemma l ->
    Format.fprintf out "@[th_lemma@ %a@]" Lemma.pp l
  | Simplify c -> Format.fprintf out "simpl %a" pp_clause_name c
  | P_raw_steps l ->
    Fmt.fprintf out "steps{@[%a@]}"
      (Util.pp_list ~sep:"," pp_raw_premise_step) l
  | P_steps {init;steps} ->
    Format.fprintf out "hyper_res{@[%a;@,%a@]}"
      pp_clause_name init (Util.pp_list ~sep:";" pp_premise_step) steps
