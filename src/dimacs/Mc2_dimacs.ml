
(** {1 Main for dimacs} *)

open Mc2_core

module Dot = Mc2_backend.Dot.Make(Mc2_backend.Dot.Default)

module Plugin_sat = Plugin_sat

type 'a or_error = ('a, string) CCResult.t

include Plugin_sat

let parse reg file : atom list list or_error =
  try
    let mk_atom = Service.Registry.find_exn reg Plugin_sat.k_atom in
    CCIO.with_in file
      (fun ic ->
         let lexbuf = Lexing.from_channel ic in
         Parser.file Lexer.token lexbuf)
    |> CCList.map (CCList.map mk_atom)
    |> CCResult.return
  with e ->
    CCResult.of_exn_trace e

let solve s =
  try Solver.solve s |> CCResult.return
  with e -> CCResult.of_exn_trace e

let check_model cs state : bool =
  Log.debug 4 "checking model";
  let check_clause c =
    Log.debugf 15
      (fun k -> k "(@[check.clause@ %a@])" Clause.debug_atoms c);
    let ok =
      List.exists
        (fun a ->
           Log.debugf 15
             (fun k -> k "(@[check.atom@ %a@])" Term.debug (Atom.term a));
           let b = Solver.Sat_state.eval_opt state a in
           (* check consistency with eval_bool *)
           begin match Atom.eval a, b with
             | _, None
             | Eval_unknown, _ -> ()
             | Eval_into (b', _), Some v_a -> assert (v_a = Value.as_bool_exn b')
           end;
           b = Some true)
        c
    in
    if not ok then (
      Log.debugf 0
        (fun k->k "(@[check.fail:@ clause %a@ not satisfied in model@])" Clause.debug_atoms c);
    );
    ok
  in
  List.for_all check_clause cs

let process ?gc ?restarts ?dot_proof
    ?(pp_model=false) ?(check=false) ?time ?memory ?progress ?switch
    s pb =
  try
    let t1 = Sys.time() in
    Solver.assume s pb;
    let res =
      Solver.solve
        ?switch ?gc ?restarts ?time ?memory ?progress
        s ~assumptions:[] in
    let t2 = Sys.time () in
    begin match res with
      | Solver.Sat st ->
        if pp_model then (
          let pp_t out t =
            Fmt.fprintf out "(@[%a %B@])" Term.pp t (Term.Bool.is_true t)
          in
          Format.printf "(@[<hv1>model@ %a@])@."
            (Util.pp_iter pp_t) (Solver.Sat_state.iter_trail st)
        );
        if check then (
          if not (check_model pb st) then (
            Error.errorf "invalid model"
          )
        );
        let t3 = Sys.time () -. t2 in
        Format.printf "Sat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
      | Solver.Unsat state ->
        if check then (
          let p = Solver.Unsat_state.get_proof state in
          Proof.check p;
          begin match dot_proof with
            | None ->  ()
            | Some file ->
              CCIO.with_out file
                (fun oc ->
                   Log.debugf 1 (fun k->k "write proof into `%s`" file);
                   let fmt = Format.formatter_of_out_channel oc in
                   Dot.print fmt p;
                   Format.pp_print_flush fmt (); flush oc)
          end
        );
        let t3 = Sys.time () -. t2 in
        Format.printf "Unsat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
    end;
    CCResult.return()
  with e ->
    CCResult.of_exn_trace e
