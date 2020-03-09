(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

open Solver_types

module S = Internal

type proof = Proof.t
type nonrec atom = atom (** The type of atoms given by the module argument for formulas *)

type 'clause clause_sets = {
  cs_hyps: 'clause Vec.t;
  cs_history: 'clause Vec.t;
  cs_local: 'clause Vec.t;
}
(** Current state of the SAT solver *)

exception UndecidedLit = Internal.UndecidedLit
exception Out_of_space = Internal.Out_of_space
exception Out_of_time = Internal.Out_of_time

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
let[@inline] services t = S.services t

let pp_all t lvl status =
  Log.debugf lvl
    (fun k -> k
        "@[<v>%s - Full summary:@,@[<hov 2>Trail:@\n%a@]@,@[<hov 2>Temp:@\n%a@]@,\
         @[<hov 2>Hyps:@\n%a@]@,@[<hov 2>Lemmas:@\n%a@]@,@]@."
        status
        (Vec.pp ~sep:"" Term.pp) (S.trail t)
        (Vec.pp ~sep:"" Clause.debug) (S.temp t)
        (Vec.pp ~sep:"" Clause.debug) (S.hyps t)
        (Vec.pp ~sep:"" Clause.debug) (S.history t))

(* Wrappers around internal functions*)
let assume = S.assume

let unsat_core _ p = Proof.unsat_core p

let true_at_level0 _s a =
  try
    let b, lev = S.eval_level a in
    b && lev = 0
  with S.UndecidedLit _ -> false

let add_term = S.add_term

let clause_sets (s:t) = {
  cs_hyps = S.hyps s;
  cs_history = S.history s;
  cs_local = S.temp s;
}

module Sat_state = struct
  type t = [`SAT] state

  let iter_trail (St_sat s) f = Vec.iter f (S.trail s)

  let[@inline] eval (St_sat _s) a = S.eval a
  let[@inline] eval_opt (St_sat _s) a = try Some (S.eval a) with UndecidedLit _ -> None
  let[@inline] eval_level (St_sat _s) a = S.eval_level a
  let model (St_sat s) = S.model s

  let check_model (s:t) : bool =
    let St_sat s = s in
    begin match S.check s with
      | Ok _ -> true
      | Error msg ->
        Log.debugf 0
          (fun k->k "(@[solver.check_model.fail:@ %a@])" Format.pp_print_text msg);
        false
    end
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
    Proof.prove_unsat c
end

type res =
  | Sat of Sat_state.t (** Returned when the solver reaches SAT *)
  | Unsat of Unsat_state.t (** Returned when the solver reaches UNSAT *)
(** Result type for the solver *)

let solve ?gc ?restarts ?time ?memory ?(progress=false) ?(assumptions=[]) (s:t): res =
  try
    S.pop s;
    S.push s;
    S.local s assumptions;
    S.solve ?gc ?restarts ?time ?memory ~progress s;
    if progress then S.clear_progress();
    pp_all s 99 "SAT";
    Sat (St_sat s)
  with S.Unsat ->
    if progress then S.clear_progress();
    pp_all s 99 "UNSAT";
    Unsat (St_unsat s)

let create ~plugins () =
  let solver = S.create() in
  (* sort by increasing priority *)
  let plugins = List.sort Plugin.Factory.compare plugins in
  List.iter (fun p -> ignore (S.add_plugin solver p)) plugins;
  solver

let pp_stats = S.pp_stats
