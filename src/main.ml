(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

open Mc2_core
open CCResult.Infix

module E = CCResult
module Fmt = CCFormat
module Ast = Mc2_smtlib.Ast
module Process = Mc2_smtlib.Process

type 'a or_error = ('a, string) E.t

let file = ref ""
let p_cnf = ref false
let p_dot_proof = ref ""
let p_proof_print = ref false
let time_limit = ref 300.
let size_limit = ref 1000_000_000.

(* TODO: remove the functor, there will be only one input *)
(* TODO: uniform typing interface for dimacs/smtlib *)
(* TODO: tseitin theory *)

module Dot = Mc2_backend.Dot.Make(Mc2_backend.Dot.Default)

let hyps = ref []

let check_model state =
  let check_clause c =
    let l =
      List.map
        (fun a ->
           Log.debugf 99
             (fun k -> k "Checking value of %a" Term.pp (Atom.term a));
           Solver.Sat_state.eval state a)
        c
    in
    List.exists (fun x -> x) l
  in
  let l = List.map check_clause !hyps in
  List.for_all (fun x -> x) l

(* Arguments parsing *)
let int_arg r arg =
  let l = String.length arg in
  let multiplier m =
    let arg1 = String.sub arg 0 (l-1) in
    r := m *. (float_of_string arg1)
  in
  if l = 0 then raise (Arg.Bad "bad numeric argument")
  else
    try
      match arg.[l-1] with
        | 'k' -> multiplier 1e3
        | 'M' -> multiplier 1e6
        | 'G' -> multiplier 1e9
        | 'T' -> multiplier 1e12
        | 's' -> multiplier 1.
        | 'm' -> multiplier 60.
        | 'h' -> multiplier 3600.
        | 'd' -> multiplier 86400.
        | '0'..'9' -> r := float_of_string arg
        | _ -> raise (Arg.Bad "bad numeric argument")
    with Failure _ -> raise (Arg.Bad "bad numeric argument")

let setup_gc_stat () =
  at_exit (fun () ->
    Gc.print_stat stdout;
  )

let input_file = fun s -> file := s

let usage = "Usage : main [options] <file>"
let argspec = Arg.align [
    "-bt", Arg.Unit (fun () -> Printexc.record_backtrace true), " Enable stack traces";
    "-cnf", Arg.Set p_cnf, " Prints the cnf used.";
    "-check", Arg.Set Process.p_check,
    " Build, check and print the proof (if output is set), if unsat";
    "-dot", Arg.Set_string p_dot_proof,
    " If provided, print the dot proof in the given file";
    "-gc", Arg.Unit setup_gc_stat,
    " Outputs statistics about the GC";
    "-size", Arg.String (int_arg size_limit),
    "<s>[kMGT] Sets the size limit for the sat solver";
    "-time", Arg.String (int_arg time_limit),
    "<t>[smhd] Sets the time limit for the sat solver";
    "-v", Arg.Int Log.set_debug,
    "<lvl> Sets the debug verbose level";
  ]

let main () =
  CCFormat.set_color_default true;
  (* Administrative duties *)
  Arg.parse argspec input_file usage;
  if !file = "" then (
    Arg.usage argspec usage;
    exit 2
  );

  Process.with_limits
    ~time:!time_limit
    ~memory:!size_limit
    (fun () ->
       (* parse pb *)
       Mc2_smtlib.Ast.parse !file >>= fun input ->
       (* TODO: parse list of plugins on CLI *)
       let solver =
         Solver.create
           ~plugins:[
             Mc2_propositional.plugin;
             Mc2_unin_sort.plugin;
             Mc2_uf.plugin;
           ] ()
       in
       (* process statements *)
       try
         let dot_proof = if !p_dot_proof = "" then None else Some !p_dot_proof in
         E.fold_l
           (fun () -> Process.process_stmt ~pp_cnf:!p_cnf ?dot_proof solver)
           () input
       with Exit ->
         E.return())

let () = match main() with
  | E.Ok () -> ()
  | E.Error msg ->
    print_endline msg;
    exit 1
  | exception Process.Out_of_time ->
    Format.printf "Timeout@.";
    exit 2
  | exception Process.Out_of_space ->
    Format.printf "Spaceout@.";
    exit 3
  | exception Process.Incorrect_model ->
    Format.printf "Internal error : incorrect *sat* model@.";
    exit 4
  | exception Ast.Ill_typed msg ->
    let b = Printexc.get_backtrace () in
    Format.fprintf Format.std_formatter "typing error\n%s@." msg;
    if Printexc.backtrace_status () then
      Format.fprintf Format.std_formatter "%s@." b

