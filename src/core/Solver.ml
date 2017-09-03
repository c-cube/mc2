(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

open Solver_types

module S = Internal

type proof = Res.proof
type nonrec atom = atom (** The type of atoms given by the module argument for formulas *)

type 'clause clause_sets = {
  cs_hyps: 'clause Vec.t;
  cs_history: 'clause Vec.t;
  cs_local: 'clause Vec.t;
}
(** Current state of the SAT solver *)

exception UndecidedLit

(** Main type *)
type t = Internal.t

type 'a state =
  | St_sat : t -> [`SAT] state
  | St_unsat : t -> [`UNSAT] state (* unsat conflict *)

let[@inline] state_solver (type a) (st: a state) : t = match st with
  | St_sat s -> s
  | St_unsat s -> s

let[@inline] plugins t = S.plugins t
let[@inline] get_service t k = S.get_service t k
let[@inline] get_service_exn t k = S.get_service_exn t k

let pp_all t lvl status =
  Log.debugf lvl
    (fun k -> k
        "@[<v>%s - Full resume:@,@[<hov 2>Trail:@\n%a@]@,@[<hov 2>Temp:@\n%a@]@,\
         @[<hov 2>Hyps:@\n%a@]@,@[<hov 2>Lemmas:@\n%a@]@,@]@."
        status
        (Vec.print ~sep:"" Term.pp) (S.trail t)
        (Vec.print ~sep:"" Clause.pp) (S.temp t)
        (Vec.print ~sep:"" Clause.pp) (S.hyps t)
        (Vec.print ~sep:"" Clause.pp) (S.history t))

(* Wrappers around internal functions*)
let assume = S.assume

let unsat_core _ p = Res.unsat_core p

let true_at_level0 _s a =
  try
    let b, lev = S.eval_level a in
    b && lev = 0
  with S.UndecidedLit -> false

let add_term = S.add_term

let clause_sets (s:t) = {
  cs_hyps = S.hyps s;
  cs_history = S.history s;
  cs_local = S.temp s;
}

module Sat_state = struct
  type t = [`SAT] state

  let iter_trail (St_sat s) f = Vec.iter f (S.trail s)

  let eval (St_sat _s) t = S.eval t
  let eval_level (St_sat _s) t = S.eval_level t
  let model (St_sat s) = S.model s
end

module Unsat_state = struct
  type t = [`UNSAT] state

  let unsat_conflict (St_unsat s) : clause =
    begin match S.unsat_conflict s with
      | None -> assert false
      | Some c -> c
    end

  let get_proof (s:t) =
    let c = unsat_conflict s in
    Res.prove_unsat c
end

type res =
  | Sat of Sat_state.t (** Returned when the solver reaches SAT *)
  | Unsat of Unsat_state.t (** Returned when the solver reaches UNSAT *)
(** Result type for the solver *)

let solve ?(assumptions=[]) (s:t): res =
  try
    S.pop s;
    S.push s;
    S.local s assumptions;
    S.solve s;
    pp_all s 99 "SAT";
    Sat (St_sat s)
  with S.Unsat ->
    pp_all s 99 "UNSAT";
    Unsat (St_unsat s)

let create ~plugins () =
  let solver = S.create() in
  (* sort by increasing priority *)
  let plugins = List.sort Plugin.Factory.compare plugins in
  List.iter (fun p -> ignore (S.add_plugin solver p)) plugins;
  solver

