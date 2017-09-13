
(** {1 Process Statements} *)

open Mc2_core
open Solver_types

module Fmt = CCFormat
module A = Ast
module E = CCResult
module Reg = Service.Registry
module F = Mc2_propositional.F

type 'a or_error = ('a, string) CCResult.t

(** {2 Conversion into {!Term.t}} *)

module Subst = struct
  type 'a t = 'a ID.Map.t
  let empty = ID.Map.empty
  let mem subst v = ID.Map.mem (A.Var.id v) subst
  let pp pp_x out = ID.Map.pp ~arrow:"→" ID.pp pp_x out
  let add subst v t =
    if mem subst v then (
      Util.errorf "%a already bound" A.Var.pp v;
    );
    ID.Map.add (A.Var.id v) t subst
  let find subst v = ID.Map.get (A.Var.id v) subst
  let find_exn subst v = ID.Map.find (A.Var.id v) subst
end

let mk_ite_id =
  let n = ref 0 in
  fun () -> ID.makef "ite_%d" (CCRef.incr_then_get n)

let mk_sub_form =
  let n = ref 0 in
  fun () -> ID.makef "sub_form_%d" (CCRef.incr_then_get n)

type term_or_form =
  | T of term
  | F of F.t

let[@inline] ret_t t = T t
let[@inline] ret_f f = F f
let[@inline] ret_any t = if Term.is_bool t then F (F.atom (Term.Bool.pa t)) else T t

let conv_ty (reg:Reg.t) (ty:A.Ty.t) : Type.t =
  let mk_ty = Reg.find_exn reg Mc2_unin_sort.k_make in
  (* convert a type *)
  let rec aux_ty (ty:A.Ty.t) : Type.t = match ty with
    | A.Ty.Prop -> Type.bool
    | A.Ty.Atomic (id, args) -> mk_ty id (List.map aux_ty args)
    | A.Ty.Arrow _ ->
      Util.errorf "cannot convert arrow type `%a`" A.Ty.pp ty
  in
  aux_ty ty

let conv_bool_term (reg:Reg.t) (t:A.term): atom list list =
  let decl = Reg.find_exn reg Mc2_uf.k_decl in
  let mk_eq_ = Reg.find_exn reg Mc2_unin_sort.k_eq in
  let mk_app = Reg.find_exn reg Mc2_uf.k_app in
  let mk_const = Reg.find_exn reg Mc2_uf.k_const in
  let fresh = Reg.find_exn reg Mc2_propositional.k_fresh in
  let mk_eq t u = Term.Bool.pa (mk_eq_ t u) in
  let mk_neq t u = Term.Bool.na (mk_eq_ t u) in
  let side_clauses : atom list list ref = ref [] in
  (* adaptative equality *)
  let mk_eq_t_tf (t:term) (u:term_or_form) : F.t = match u with
    | F u -> F.equiv (F.atom (Term.Bool.pa t)) u
    | T u -> mk_eq t u |> F.atom
  and mk_eq_tf_tf (t:term_or_form) (u:term_or_form) = match t, u with
    | T t, T u -> mk_eq t u |> F.atom
    | F t, F u -> F.equiv t u
    | _ -> assert false
  in
  (* convert term *)
  let rec aux (subst:term_or_form Subst.t) (t:A.term) : term_or_form =
    begin match A.term_view t with
      | A.Var v ->
        begin match Subst.find subst v with
          | None -> Util.errorf "variable %a not bound" A.Var.pp v
          | Some t -> t
        end
      | A.Const id -> mk_const id |> ret_any
      | A.App (f, l) ->
        let l = List.map (aux_t subst) l in
        begin match A.term_view f with
          | A.Const id -> mk_app id l |> ret_any
          | _ -> Util.errorf "cannot process HO application %a" A.pp_term t
        end
      | A.If (a,b,c) ->
        let a = aux_form subst a in
        let b = aux subst b in
        let c = aux subst c in
        let ty_b = match b with
          | F _ -> Type.bool
          | T t -> Term.ty t
        in
        let placeholder_id = mk_ite_id () in
        decl placeholder_id [] ty_b;
        let placeholder = mk_const placeholder_id in
        (* add [f_a => placeholder=b] and [¬f_a => placeholder=c] *)
        let form =
          F.and_
            [ F.imply a (mk_eq_t_tf placeholder b);
              F.imply (F.not_ a) (mk_eq_t_tf placeholder c);
            ]
        in
        side_clauses := List.rev_append (mk_cnf form) !side_clauses;
        ret_t placeholder
      | A.Let (v,t,u) ->
        let subst = Subst.add subst v (aux subst t) in
        aux subst u
      | A.Op (A.And, l) -> F.and_ (List.map (aux_form subst) l) |> ret_f
      | A.Op (A.Or, l) -> F.or_ (List.map (aux_form subst) l) |> ret_f
      | A.Op (A.Imply, l) ->
        let rec curry_imply_ = function
          | [] -> assert false
          | [a] -> aux_form subst a
          | a :: b -> F.imply (aux_form subst a) (curry_imply_ b)
        in
        curry_imply_ l |> ret_f
      | A.Op (A.Eq, l) ->
        let l = List.map (aux subst) l in
        let rec curry_eq = function
          | [] | [_] -> assert false
          | [a;b] -> [mk_eq_tf_tf a b]
          | a :: b :: tail ->
            mk_eq_tf_tf a b :: curry_eq (b::tail)
        in
        F.and_ (curry_eq l) |> ret_f
      | A.Op (A.Distinct, l) ->
        (* TODO: more efficient "distinct"? *)
        List.map (aux_t subst) l
        |> CCList.diagonal
        |> List.map (fun (t,u) -> mk_neq t u |> F.atom)
        |> F.and_ |> ret_f
      | A.Not f -> F.not_ (aux_form subst f) |> ret_f
      | A.Bool true -> ret_f F.true_
      | A.Bool false -> ret_f F.false_
      | A.Select _ -> assert false (* TODO *)
      | A.Match _ -> assert false (* TODO *)
      | A.Bind _ -> assert false (* TODO *)
    end

  (* expect a term *)
  and aux_t subst (t:A.term) : term = match aux subst t with
    | T t -> t
    | F (F.Lit a) when Atom.is_pos a -> a.a_term
    | F f ->
      (* name the sub-formula and add CNF *)
      let placeholder_id = mk_sub_form() in
      decl placeholder_id [] Type.bool;
      let placeholder = mk_const placeholder_id in
      (* add [f_a => placeholder=b] and [¬f_a => placeholder=c] *)
      let form = F.equiv (F.atom (Term.Bool.pa placeholder)) f in
      side_clauses := List.rev_append (mk_cnf form) !side_clauses;
      placeholder

  (* convert formula *)
  and aux_form subst (t:A.term): F.t = match aux subst t with
    | T t -> F.atom (Term.Bool.pa t)
    | F f -> f

  and mk_cnf (f:F.t) : atom list list =
    F.cnf ~fresh f
  in
  let cs = aux_form Subst.empty t |> mk_cnf in
  List.rev_append !side_clauses cs

(** {2 Processing Statements} *)

(* list of (local) hypothesis *)
let hyps = ref []

let check_model state : bool =
  let check_clause c =
    Log.debugf 15
      (fun k -> k "(@[check.clause@ %a@])" Clause.debug_atoms c);
    let ok =
      List.exists
        (fun a ->
           Log.debugf 15
             (fun k -> k "(@[check.atom@ %a@])" Term.debug (Atom.term a));
         let b = Solver.Sat_state.eval state a in
         (* check consistency with eval_bool *)
         begin match Term.eval_bool (Atom.term a) with
           | Eval_unknown -> ()
           | Eval_bool (b', _) ->
             assert (b = (if Atom.is_pos a then b' else not b'));
         end;
         b)
        c
    in
    if not ok then (
      Log.debugf 0
        (fun k->k "(@[check.fail:@ clause %a@ not satisfied in model@])" Clause.debug_atoms c);
    );
    ok
  in
  List.for_all check_clause !hyps

module Dot = Mc2_backend.Dot.Make(Mc2_backend.Dot.Default)

(* call the solver to check-sat *)
let solve ?gc ?restarts ?dot_proof ?(pp_model=false) ?(check=false) ~assumptions s : unit =
  let t1 = Sys.time() in
  let res = Solver.solve ?gc ?restarts s ~assumptions in
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
          Util.error "invalid model"
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
    ?gc ?restarts
    ?(pp_cnf=false)
    ?dot_proof
    ?pp_model
    ?check
    (solver:Solver.t)
    (stmt:Ast.statement) : unit or_error =
  Log.debugf 5
    (fun k->k "(@[<2>process statement@ %a@])" A.pp_statement stmt);
  let decl_sort = Solver.get_service_exn solver Mc2_unin_sort.k_decl_sort in
  let decl = Solver.get_service_exn solver Mc2_uf.k_decl in
  let conv_ty = conv_ty (Solver.services solver) in
  begin match stmt with
    | A.SetLogic "QF_UF" -> E.return ()
    | A.SetLogic s ->
      Log.debugf 0 (fun k->k "warning: unknown logic `%s`" s);
      E.return ()
    | A.SetOption l ->
      Log.debugf 0 (fun k->k "warning: unknown option `%a`" (Util.pp_list Fmt.string) l);
      E.return ()
    | A.SetInfo _ -> E.return ()
    | A.Exit ->
      Log.debug 1 "exit";
      raise Exit
    | A.CheckSat ->
      solve ?gc ?restarts ?dot_proof ?check ?pp_model solver ~assumptions:[];
      E.return()
    | A.TyDecl (id,n) ->
      decl_sort id n;
      E.return ()
    | A.Decl (f,ty) ->
      let ty_args, ty_ret = A.Ty.unfold ty in
      let ty_args = List.map conv_ty ty_args in
      let ty_ret = conv_ty ty_ret in
      decl f ty_args ty_ret;
      E.return ()
    | A.Assert t ->
      let clauses =
        conv_bool_term (Solver.services solver) t
      in
      if pp_cnf then (
        Format.printf "(@[<hv1>assert@ %a@])@."
          (Util.pp_list Clause.pp_atoms) clauses;
      );
      hyps := clauses @ !hyps;
      Solver.assume solver clauses;
      E.return()
    | A.Goal (_, _) ->
      Util.errorf "cannot deal with goals yet"

      (*
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
         *)
  end

