
(** {1 Main for dimacs} *)

open Mc2_core
open Solver_types

type 'a or_error = ('a, string) CCResult.t

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

let process ?gc ?restarts ?(pp_model=false) s pb =
  try
    let t1 = Sys.time() in
    Solver.assume s pb;
    let res = Solver.solve ?gc ?restarts s ~assumptions:[] in
    let t2 = Sys.time () in
    begin match res with
      | Solver.Sat st ->
        if pp_model then (
          let pp_t out t =
            Fmt.fprintf out "(@[%a %B@])" Term.pp t (Term.Bool.is_true t)
          in
          Format.printf "(@[<hv1>model@ %a@])@."
            (Util.pp_seq pp_t) (Solver.Sat_state.iter_trail st)
        );
        let t3 = Sys.time () -. t2 in
        Format.printf "Sat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
      | Solver.Unsat _state ->
        let t3 = Sys.time () -. t2 in
        Format.printf "Unsat (%.3f/%.3f/%.3f)@." t1 (t2-.t1) t3;
    end;
    CCResult.return()
  with e ->
    CCResult.of_exn_trace e
