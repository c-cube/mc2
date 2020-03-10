
(** {1 Process Statements} *)

open Mc2_core

module PA = Smtlib_utils.V_2_6.Ast
module Typecheck = Typecheck
module E = CCResult

type 'a or_error = ('a, string) CCResult.t

module Make(ARG : sig
    val solver : Solver.t
  end)
= struct
  let solver = ARG.solver
  let parse = Smtlib_utils.V_2_6.parse_file
  let parse_stdin () = Smtlib_utils.V_2_6.parse_chan ~filename:"<stdin>" stdin

  module TC = Typecheck.Make(ARG)
  module Dot = Mc2_backend.Dot.Make(Mc2_backend.Dot.Default)

  (** {2 Processing Statements} *)

  let typecheck stmts =
    try
      let l = CCList.flat_map TC.conv_statement stmts in
      Ok l
    with e -> E.of_exn_trace e

  (* list of (local) hypothesis *)
  let hyps = ref []

  let check_model state : bool =
    Log.debug 4 "checking model";
    let check_clause c =
      Log.debugf 15
        (fun k -> k "(@[check.clause@ %a@])" Clause.debug_atoms c);
      let ok =
        List.exists (fun t -> Solver.Sat_state.eval_opt state t = Some true) c
      in
      if not ok then (
        Log.debugf 0
          (fun k->k "(@[check.fail:@ clause %a@ not satisfied in model@])" Clause.debug_atoms c);
      );
      ok
    in
    Solver.Sat_state.check_model state &&
    List.for_all check_clause !hyps

  (* call the solver to check-sat *)
  let solve
      ?gc ?restarts ?dot_proof
      ?(pp_model=false) ?(check=false) ?time ?memory ?progress ?switch
      ~assumptions s : unit =
    let t1 = Sys.time() in
    let res =
      Solver.solve ?gc ?restarts ?time ?memory ?progress ?switch
        s ~assumptions in
    let t2 = Sys.time () in
    begin match res with
      | Solver.Sat state ->
        if pp_model then (
          let pp_t out = function
            | A_bool (t,b) -> Fmt.fprintf out "(@[%a@ %B@])" Term.pp t b
            | A_semantic (t,v) -> Fmt.fprintf out "(@[%a@ %a@])" Term.pp t Value.pp v
          in
          Format.printf "(@[<hv1>model@ %a@])@."
            (Util.pp_list pp_t) (Solver.Sat_state.model state)
        );
        if check then (
          if not (check_model state) then (
            Error.error "invalid model"
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
    end

  (* process a single statement *)
  let process_stmt
      ?gc ?restarts ?(pp_cnf=false) ?dot_proof ?pp_model ?check
      ?time ?memory ?progress ?switch
      (stmt:Statement.t) : unit or_error =
    Log.debugf 5
      (fun k->k "(@[<2>process statement@ %a@])" Statement.pp stmt);
    begin match stmt with
      | Stmt_set_logic ("QF_UF"|"QF_LRA"|"QF_UFLRA") -> E.return ()
      | Stmt_set_logic s ->
        Log.debugf 0 (fun k->k "warning: unknown logic `%s`" s);
        E.return ()
      | Stmt_set_option l ->
        Log.debugf 0 (fun k->k "warning: unknown option `%a`" (Util.pp_list Fmt.string) l);
        E.return ()
      | Stmt_set_info _ -> E.return ()
      | Stmt_exit ->
        Log.debug 1 "exit";
        raise Exit
      | Stmt_check_sat ->
        solve ?gc ?restarts ?dot_proof ?check ?pp_model ?time
          ?memory ?progress ?switch
          solver ~assumptions:[];
        E.return()
      | Stmt_ty_decl _ -> E.return ()
      | Stmt_decl _ -> E.return ()
      | Stmt_assert_clauses clauses ->
        if pp_cnf then (
          Format.printf "(@[<hv1>assert@ %a@])@."
            (Util.pp_list Clause.pp_atoms) clauses;
        );
        hyps := clauses @ !hyps;
        Solver.assume solver clauses;
        E.return()
      | Stmt_define _ ->
        E.return ()
    end

end
