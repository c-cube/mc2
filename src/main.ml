(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

open Mc2_core
open CCResult.Infix

module E = CCResult
module Ast = Mc2_smtlib.Ast

exception Incorrect_model
exception Out_of_time
exception Out_of_space

let file = ref ""
let p_cnf = ref false
let p_check = ref false
let p_dot_proof = ref ""
let p_proof_print = ref false
let time_limit = ref 300.
let size_limit = ref 1000_000_000.

module P =
  Dolmen.Logic.Make(Dolmen.ParseLocation)
    (Dolmen.Id)(Dolmen.Term)(Dolmen.Statement)

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

let prove ~assumptions s =
  let res = Solver.solve s ~assumptions in
  let t = Sys.time () in
  begin match res with
    | Solver.Sat state ->
      if !p_check then
        if not (check_model state) then
          raise Incorrect_model;
      let t' = Sys.time () -. t in
      Format.printf "Sat (%f/%f)@." t t'
    | Solver.Unsat state ->
      if !p_check then (
        let p = Solver.Unsat_state.get_proof state in
        Res.check p;
        if !p_dot_proof <> "" then (
          CCIO.with_out !p_dot_proof
            (fun oc ->
               Log.debugf 1 (fun k->k "write proof into `%s`" !p_dot_proof);
               let fmt = Format.formatter_of_out_channel oc in
               Dot.print fmt p;
               Format.pp_print_flush fmt (); flush oc)
        )
      );
      let t' = Sys.time () -. t in
      Format.printf "Unsat (%f/%f)@." t t'
  end

(* dump CNF *)
let pp_cnf (cnf:Atom.t list list) =
  if !p_cnf then (
    let pp_c =
      CCFormat.(within "[" "]" @@ hvbox ~i:2 @@ list
          ~sep:(return " @<1>∨@ ") Atom.pp)
    in
    Format.printf "CNF: @[<v>%a@]@." CCFormat.(list pp_c) cnf;
  )

let do_task (solver:Solver.t) (s:Ast.statement) : (unit,string) E.t =
  begin match s with
    | Dolmen.Statement.Def (id, t) -> T.def id t
    | Dolmen.Statement.Decl (id, t) -> T.decl id t
    | Dolmen.Statement.Consequent t ->
      let cnf = T.consequent t in
      pp_cnf solver cnf;
      hyps := cnf @ !hyps;
      S.assume s cnf
    | Dolmen.Statement.Antecedent t ->
      let cnf = T.antecedent t in
      pp_cnf cnf;
      hyps := cnf @ !hyps;
      S.assume cnf
    | Dolmen.Statement.Pack [
        { Dolmen.Statement.descr = Dolmen.Statement.Push 1; _ };
        { Dolmen.Statement.descr = Dolmen.Statement.Antecedent f; _ };
        { Dolmen.Statement.descr = Dolmen.Statement.Prove; _ };
        { Dolmen.Statement.descr = Dolmen.Statement.Pop 1; _ };
      ] ->
      let assumptions = T.assumptions f in
      prove solver ~assumptions
    | Dolmen.Statement.Prove ->
      prove solver ~assumptions:[]
    | Dolmen.Statement.Set_info _
    | Dolmen.Statement.Set_logic _ -> ()
    | Dolmen.Statement.Exit -> exit 0
    | _ ->
      Format.printf "Command not supported:@\n%a@."
        Dolmen.Statement.print s
  end

let error_msg opt arg l =
  Format.fprintf Format.str_formatter "'%s' is not a valid argument for '%s', valid arguments are : %a"
    arg opt (fun fmt -> List.iter (fun (s, _) -> Format.fprintf fmt "%s, " s)) l;
  Format.flush_str_formatter ()

let set_flag opt arg flag l =
  try
    flag := List.assoc arg l
  with Not_found ->
    invalid_arg (error_msg opt arg l)

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
    "-check", Arg.Set p_check,
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

(* Limits alarm *)
let check () =
  let t = Sys.time () in
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let s = float heap_size *. float Sys.word_size /. 8. in
  if t > !time_limit then
    raise Out_of_time
  else if s > !size_limit then
    raise Out_of_space


let main () =
  CCFormat.set_color_default true;
  (* Administrative duties *)
  Arg.parse argspec input_file usage;
  if !file = "" then (
    Arg.usage argspec usage;
    exit 2
  );
  let al = Gc.create_alarm check in

  (* Interesting stuff happening *)
  Mc2_smtlib.Ast.parse !file >>= fun input ->
  (* TODO: parse list of plugins on CLI *)
  let solver = Solver.create() in
  List.iter (do_task solver) input;
  (* Small hack for dimacs, which do not output a "Prove" statement *)
  begin match lang with
    | P.Dimacs -> do_task solver @@ Dolmen.Statement.check_sat ()
    | _ -> ()
  end;
  Gc.delete_alarm al;
  ()

let () =
  try
    main ()
  with
    | Out_of_time ->
      Format.printf "Timeout@.";
      exit 2
    | Out_of_space ->
      Format.printf "Spaceout@.";
      exit 3
    | Incorrect_model ->
      Format.printf "Internal error : incorrect *sat* model@.";
      exit 4
    | Ast.Ill_typed msg ->
      let b = Printexc.get_backtrace () in
      Format.fprintf Format.std_formatter "typing error\n%s@." msg;
      if Printexc.backtrace_status () then
        Format.fprintf Format.std_formatter "%s@." b

