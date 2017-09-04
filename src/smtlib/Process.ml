
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

let conv_bool_term (reg:Reg.t) (t:A.term): atom list list =
  let mk_ty = Reg.find_exn reg Mc2_unin_sort.k_make in
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
      | A.Const id -> mk_const id (A.ty t |> aux_ty) |> ret_any
      | A.App (f, l) ->
        let l = List.map (aux_t subst) l in
        begin match A.term_view f with
          | A.Const id -> mk_app id (A.ty f |> aux_ty) l |> ret_any
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
        let placeholder = mk_const (mk_ite_id ()) ty_b in
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
      let placeholder = mk_const (mk_sub_form ()) Type.bool in
      (* add [f_a => placeholder=b] and [¬f_a => placeholder=c] *)
      let form = F.equiv (F.atom (Term.Bool.pa placeholder)) f in
      side_clauses := List.rev_append (mk_cnf form) !side_clauses;
      placeholder

  (* convert formula *)
  and aux_form subst (t:A.term): F.t = match aux subst t with
    | T t -> F.atom (Term.Bool.pa t)
    | F f -> f

  (* convert a type *)
  and aux_ty (ty:A.Ty.t) : Type.t = match ty with
    | A.Ty.Prop -> Type.bool
    | A.Ty.Atomic (id, args) -> mk_ty id (List.map aux_ty args)
    | A.Ty.Arrow _ ->
      Util.errorf "cannot convert arrow type `%a`" A.Ty.pp ty
  and mk_cnf (f:F.t) : atom list list =
    F.cnf ~fresh f
  in
  let cs = aux_form Subst.empty t |> mk_cnf in
  List.rev_append !side_clauses cs

(** {2 Processing Statements} *)

exception Incorrect_model
exception Out_of_time
exception Out_of_space

(* list of (local) hypothesis *)
let hyps = ref []

let with_limits ~time ~memory f =
  (* Limits alarm *)
  let check () =
    let t = Sys.time () in
    let heap_size = (Gc.quick_stat ()).Gc.heap_words in
    let s = float heap_size *. float Sys.word_size /. 8. in
    if t > time then (
      raise Out_of_time
    ) else if s > memory then (
      raise Out_of_space
    )
  in
  let al = Gc.create_alarm check in
  CCFun.finally ~h:(fun () -> Gc.delete_alarm al) ~f

let check_model state : bool =
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

let p_check = ref true

module Dot = Mc2_backend.Dot.Make(Mc2_backend.Dot.Default)

let prove ?dot_proof ~assumptions s : unit =
  let res = Solver.solve s ~assumptions in
  let t = Sys.time () in
  begin match res with
    | Solver.Sat state ->
      if !p_check then (
        if not (check_model state) then (
          raise Incorrect_model;
        )
      );
      let t' = Sys.time () -. t in
      Format.printf "Sat (%f/%f)@." t t';
    | Solver.Unsat state ->
      if !p_check then (
        let p = Solver.Unsat_state.get_proof state in
        Res.check p;
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
      let t' = Sys.time () -. t in
      Format.printf "Unsat (%f/%f)@." t t';
  end

let process_stmt
    ?dot_proof
    (solver:Solver.t)
    (stmt:Ast.statement) : unit or_error =
  Log.debugf 5
    (fun k->k "(@[<2>process statement@ %a@])" A.pp_statement stmt);
  let decl_sort = Solver.get_service_exn solver Mc2_unin_sort.k_decl_sort in
  begin match stmt with
    | A.SetLogic "QF_UF" -> E.return ()
    | A.SetLogic s ->
      Log.debugf 0 (fun k->k "warning: unknown logic `%s`" s);
      E.return ()
    | A.SetOption l ->
      Log.debugf 0 (fun k->k "warning: unknown option `%a`" (Util.pp_list Fmt.string) l);
      E.return ()
    | A.SetInfo _ -> E.return ()
    | A.Exit -> raise Exit
    | A.CheckSat ->
      prove ?dot_proof solver ~assumptions:[];
      E.return()
    | A.TyDecl (id,n) ->
      decl_sort id n;
      E.return ()
    | A.Decl _ ->
      (* TODO: notify plugins *)
      E.return ()
    | A.Assert _t ->
      assert false
      (* FIXME: convert term, turn into CNF
      let mk_cnf = Solver.get_service_exn solver Mc2_propositional.Literal.k_cnf in
      let cnf = cnf t in
      pp_cnf cnf;
      hyps := cnf @ !hyps;
      S.assume cnf
        *)
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
