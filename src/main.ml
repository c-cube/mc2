(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

open Minismt_core
open Minismt_sat

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

module type S = sig
  val do_task : Dolmen.Statement.t -> unit
end

module Make
    (S : External.S)
    (T : Type.S with type atom := S.atom)
  : sig
    val do_task : Dolmen.Statement.t -> unit
  end = struct

  module Dot = Minismt_backend.Dot.Make(S.Proof)(Minismt_backend.Dot.Default(S.Proof))

  let hyps = ref []

  let check_model state =
    let check_clause c =
      let l = List.map (function a ->
          Log.debugf 99
            (fun k -> k "Checking value of %a" S.St.pp_atom (S.St.add_atom a));
          state.Solver_intf.eval a) c in
      List.exists (fun x -> x) l
    in
    let l = List.map check_clause !hyps in
    List.for_all (fun x -> x) l

  let prove ~assumptions =
    let res = S.solve ~assumptions () in
    let t = Sys.time () in
    begin match res with
      | S.Sat state ->
        if !p_check then
          if not (check_model state) then
            raise Incorrect_model;
        let t' = Sys.time () -. t in
        Format.printf "Sat (%f/%f)@." t t'
      | S.Unsat state ->
        if !p_check then begin
          let p = state.Solver_intf.get_proof () in
          S.Proof.check p;
          if !p_dot_proof <> "" then begin
            CCIO.with_out !p_dot_proof
              (fun oc ->
                 Log.debugf 1 (fun k->k "write proof into `%s`" !p_dot_proof);
                 let fmt = Format.formatter_of_out_channel oc in
                 Dot.print fmt p;
                 Format.pp_print_flush fmt (); flush oc)
          end
        end;
        let t' = Sys.time () -. t in
        Format.printf "Unsat (%f/%f)@." t t'
    end

  (* dump CNF *)
  let pp_cnf (cnf:S.atom list list) =
    if !p_cnf then (
      let pp_c =
        CCFormat.(within "[" "]" @@ hvbox ~i:2 @@ list
            ~sep:(return " @<1>∨@ ") T.pp_atom)
      in
      Format.printf "CNF: @[<v>%a@]@." CCFormat.(list pp_c) cnf;
    )

  let do_task s =
    match s.Dolmen.Statement.descr with
      | Dolmen.Statement.Def (id, t) -> T.def id t
      | Dolmen.Statement.Decl (id, t) -> T.decl id t
      | Dolmen.Statement.Consequent t ->
        let cnf = T.consequent t in
        pp_cnf cnf;
        hyps := cnf @ !hyps;
        S.assume cnf
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
        prove ~assumptions
      | Dolmen.Statement.Prove ->
        prove ~assumptions:[]
      | _ ->
        Format.printf "Command not supported:@\n%a@."
          Dolmen.Statement.print s
end

module Sat = Make(Sat.Make(struct end))(Type_sat)
module Mcsat = Make(Mcsat.Make(struct end))(Type_smt)

let solver = ref (module Mcsat : S)
let solver_list = [
  "sat", (module Sat : S);
  "mcsat", (module Mcsat : S);
]

let error_msg opt arg l =
  Format.fprintf Format.str_formatter "'%s' is not a valid argument for '%s', valid arguments are : %a"
    arg opt (fun fmt -> List.iter (fun (s, _) -> Format.fprintf fmt "%s, " s)) l;
  Format.flush_str_formatter ()

let set_flag opt arg flag l =
  try
    flag := List.assoc arg l
  with Not_found ->
    invalid_arg (error_msg opt arg l)

let set_solver s = set_flag "Solver" s solver solver_list

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
    "-s", Arg.Symbol (List.map fst solver_list, set_solver),
    "Sets the solver to use (default mcsat)";
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
  if !file = "" then begin
    Arg.usage argspec usage;
    exit 2
  end;
  let al = Gc.create_alarm check in

  (* Interesting stuff happening *)
  let lang, input = P.parse_file !file in
  let module S = (val !solver : S) in
  List.iter S.do_task input;
  (* Small hack for dimacs, which do not output a "Prove" statement *)
  begin match lang with
    | P.Dimacs -> S.do_task @@ Dolmen.Statement.check_sat ()
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
    | Type_sat.Typing_error (msg, t)
    | Type_smt.Typing_error (msg, t) ->
      let b = Printexc.get_backtrace () in
      let loc = match t.Dolmen.Term.loc with
        | Some l -> l | None -> Dolmen.ParseLocation.mk "<>" 0 0 0 0
      in
      Format.fprintf Format.std_formatter "While typing:@\n%a@\n%a: typing error\n%s@."
        Dolmen.Term.print t Dolmen.ParseLocation.fmt loc msg;
      if Printexc.backtrace_status () then
        Format.fprintf Format.std_formatter "%s@." b

