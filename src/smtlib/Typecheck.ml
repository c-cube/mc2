(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

open Mc2_core

module Loc = Smtlib_utils.V_2_6.Loc
module PA = Smtlib_utils.V_2_6.Ast
module SReg = Service.Registry
module Ty = Mc2_core.Type
module T = Mc2_core.Term
module F = Mc2_propositional.F
module RLE = Mc2_lra.LE
module Stmt = Mc2_core.Statement

type 'a or_error = ('a, string) CCResult.t

let pp_loc_opt = Loc.pp_opt

module StrTbl = CCHashtbl.Make(CCString)

module Make(ARG : sig
    val solver : Mc2_core.Solver.t
  end)
= struct
  let solver = ARG.solver
  let reg = Solver.services solver
  let decl = Solver.get_service_exn solver Mc2_uf.k_decl

  module Ctx = struct
    type t = {
      tys: (ID.t * Type.t) StrTbl.t;
      terms: ID.t StrTbl.t;
      (* TODO: definitions *)
      mutable loc: Loc.t option; (* current loc *)
    }

    let t : t = {
      terms=StrTbl.create 64;
      tys=StrTbl.create 64;
      loc=None;
    }

    let loc t = t.loc
    let set_loc ?loc () = t.loc <- loc

    let add_term_fun_ (s:string) (id:ID.t) : unit =
      StrTbl.replace t.terms s id;
      ()

    let add_ty_ (s:string) (id:ID.t) (ty:Ty.t) : unit =
      StrTbl.replace t.tys s (id,ty);
      ()

    let find_ty (s:string) : ty =
      match StrTbl.get t.tys s with
      | Some (_, ty) -> ty
      | _ -> Error.errorf "expected %s to be an atomic type" s

    let find_term_fun (s:string) : ID.t =
      match StrTbl.get t.terms s with
      | Some f -> f
      | _ -> Error.errorf "expected %s to be a function symbol" s
  end

  let error_loc () : string = Fmt.sprintf "at %a: " pp_loc_opt (Ctx.loc Ctx.t)
  let errorf_ctx msg =
    Error.errorf ("at %a:@ " ^^ msg) pp_loc_opt (Ctx.loc Ctx.t)

  let ill_typed fmt =
    errorf_ctx ("ill-typed: " ^^ fmt)

  let check_bool_ t : unit =
    if not (Ty.equal (T.ty t) Ty.bool) then (
      ill_typed "expected bool, got `@[%a : %a@]`" T.pp t Ty.pp (T.ty t)
    )

  (* parse a type *)
  let conv_ty (t:PA.ty) : Ty.t = match t with
    | PA.Ty_bool -> Ty.bool
    | PA.Ty_real ->
      SReg.find_exn reg Mc2_lra.k_rat
    | PA.Ty_app ("Rat",[]) ->
      ill_typed "cannot handle reals for now"
    | PA.Ty_app ("Int",[]) ->
      ill_typed "cannot handle ints for now"
      (* TODO: A.Ty.int , Ctx.K_ty Ctx.K_other *)
    | PA.Ty_app (f, []) -> Ctx.find_ty f
    | PA.Ty_app (_f, _l) ->
      ill_typed "cannot handle parametric types"
    | PA.Ty_arrow _ ->
      ill_typed "cannot handle arrow types"

  module Subst = struct
    module M = Util.Str_map
    type 'a t = 'a M.t
    let empty = M.empty
    let mem subst v = M.mem v subst
    let pp pp_x out = M.pp ~arrow:"→" Fmt.string pp_x out
    let add subst v t =
      if mem subst v then (
        Error.errorf "%a already bound" Fmt.string v;
      );
      M.add v t subst
    let find subst v = M.get v subst
    let find_exn subst v = M.find v subst
  end

  let is_num s =
    let is_digit_or_dot = function '0' .. '9' | '.' -> true | _ -> false in
    if s.[0] = '-'
    then CCString.for_all is_digit_or_dot (String.sub s 1 (String.length s-1))
    else CCString.for_all is_digit_or_dot s

  let mk_ite_id =
    let n = ref 0 in
    fun () -> ID.makef "ite_%d" (CCRef.incr_then_get n)

  let mk_sub_form =
    let n = ref 0 in
    fun () -> ID.makef "sub_form_%d" (CCRef.incr_then_get n)

  let mk_lra_id =
    let n = ref 0 in
    fun () -> ID.makef "lra_%d" (CCRef.incr_then_get n)

  type term_or_form =
    | T of term
    | F of F.t
    | Rat of RLE.t (* rational linear expression *)

  let[@inline] ret_t t = T t
  let[@inline] ret_f f = F f
  let[@inline] ret_rat t = Rat t
  let ret_any t =
    if Term.is_bool t then F (F.atom (Term.Bool.pa t)) else T t

  let pp_tof out = function
    | T t -> Fmt.fprintf out "(@[T %a@])" Term.pp t
    | F f -> Fmt.fprintf out "(@[F %a@])" F.pp f
    | Rat lre -> Fmt.fprintf out "(@[RLE %a@])" RLE.pp_no_paren lre

  let parse_num ~where (s:string) : [`Q of Q.t | `Z of Z.t] =
    let fail() =
      Error.errorf "%sexpected number, got `%s`" (Lazy.force where) s
    in
    begin match Z.of_string s with
      | n -> `Z n
      | exception _ ->
        begin match Q.of_string s with
          | n -> `Q n
          | exception _ ->
            if String.contains s '.' then (
              let p1, p2 = CCString.Split.left_exn ~by:"." s in
              let n1, n2 =
                try Z.of_string p1, Z.of_string p2
                with _ -> fail()
              in
              let factor_10 = Z.pow (Z.of_int 10) (String.length p2) in
              (* [(p1·10^{length p2}+p2) / 10^{length p2}] *)
              let n =
                Q.div
                  (Q.of_bigint (Z.add n2 (Z.mul n1 factor_10)))
                  (Q.of_bigint factor_10)
              in
              `Q n
            ) else fail()
        end
    end

  let side_clauses = ref []

  let mk_const = SReg.find_exn reg Mc2_uf.k_const
  let mk_lra_pred = SReg.find_exn reg Mc2_lra.k_make_pred
  let mk_lra_relu = SReg.find_exn reg Mc2_lra.k_make_relu [@@warning "-26"]
  let mk_lra_eq t u = mk_lra_pred Mc2_lra.Eq0 (RLE.diff t u) |> Term.Bool.pa
  let[@inline] mk_eq_ t u = Term.mk_eq t u
  let mk_eq t u = Term.Bool.pa (mk_eq_ t u)
  let mk_neq t u = Term.Bool.na (mk_eq_ t u)

  module LRA_tbl = CCHashtbl.Make(RLE)
  let _lra_names = LRA_tbl.create 16

  (* introduce intermediate variable for LRA sub-expression *)
  let mk_lra_expr (e:RLE.t): term =
    match RLE.as_const e, RLE.as_singleton e with
    | Some n, _ -> SReg.find_exn reg Mc2_lra.k_make_const n
    | None, Some (n,t) when Q.equal n Q.one -> t
    | _ ->
      begin match LRA_tbl.find _lra_names e with
      | t -> t
      | exception Not_found ->
        let id = mk_lra_id() in
        Log.debugf 30
          (fun k->k"(@[smtlib.name_lra@ %a@ :as %a@])" RLE.pp e ID.pp id);
        decl id [] (SReg.find_exn reg Mc2_lra.k_rat);
        let t = mk_const id in
        side_clauses := [mk_lra_eq (RLE.singleton1 t) e] :: !side_clauses;
        LRA_tbl.add _lra_names e t; (* cache *)
        t
      end

  (* adaptative equality *)
  let mk_eq_t_tf (t:term) (u:term_or_form) : F.t = match u with
    | F u -> F.equiv (F.atom (Term.Bool.pa t)) u
    | T u when Term.is_bool u ->
      F.equiv (F.atom (Term.Bool.pa t)) (F.atom (Term.Bool.pa u))
    | T u -> mk_eq t u |> F.atom
    | Rat u -> mk_lra_eq (RLE.singleton1 t) u |> F.atom
  let mk_eq_tf_tf (t:term_or_form) (u:term_or_form) = match t, u with
    | T t, T u when Term.is_bool t ->
      F.equiv (F.atom (Term.Bool.pa t)) (F.atom (Term.Bool.pa u))
    | T t, T u -> mk_eq t u |> F.atom
    | T t, Rat u | Rat u, T t -> mk_lra_eq (RLE.singleton1 t) u |> F.atom
    | Rat t, Rat u -> mk_lra_eq t u |> F.atom
    | F t, F u -> F.equiv t u
    | F t, T u -> F.equiv t (F.atom @@ Term.Bool.pa u)
    | T t, F u -> F.equiv (F.atom @@ Term.Bool.pa t) u
    | _ ->
      Log.debugf 1 (fun k->k "eq %a %a" pp_tof t pp_tof u);
      assert false

  (* convert term *)
  let rec conv_term_or_form (subst:term_or_form Subst.t) (t:PA.term) : term_or_form =
    (* polymorphic equality *)
    let mk_app = SReg.find_exn reg Mc2_uf.k_app in
    let mk_const = SReg.find_exn reg Mc2_uf.k_const in
    let side_clauses : atom list list ref = ref [] in
    let conv_const v =
      begin match Subst.find subst v with
        | Some t -> t
        | None when is_num v ->
          (* numeral *)
          begin match parse_num ~where:(lazy (error_loc ())) v with
            | `Q n -> Mc2_lra.LE.const n |> ret_rat
            | `Z n -> Mc2_lra.LE.const (Q.of_bigint n) |> ret_rat
          end
        | _ ->
          match Ctx.find_term_fun v with
          | f -> mk_app f [] |> ret_any
          | exception Not_found ->
            Error.errorf "variable %S not bound" v
        end
    in
    begin match t with
      | PA.Const v -> conv_const v
      | PA.App (f, []) -> conv_const f
      | PA.App (f, l) ->
        let l = List.map (conv_term_ subst) l in
        let id = Ctx.find_term_fun f in
        mk_app id l |> ret_any
      | PA.If (a,b,c) ->
        let a = conv_form subst a in
        let b = conv_term_or_form subst b in
        let c = conv_term_or_form subst c in
        let ty_b = match b with
          | F _ -> Type.bool
          | T t -> Term.ty t
          | Rat _ -> SReg.find_exn reg Mc2_lra.k_rat
        in
        let placeholder_id = mk_ite_id () in
        Log.debugf 30
          (fun k->k"(@[smtlib.name_term@ %a@ :as %a@])" PA.pp_term t ID.pp placeholder_id);
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
        ret_any placeholder
      | PA.Let (bs,body) ->
        (* convert all bindings in the same surrounding [subst],
           then convert [body] with all bindings active *)
        let subst =
          List.fold_left
            (fun subst' (v,t) -> Subst.add subst' v (conv_term_or_form subst t))
            subst bs
        in
        conv_term_or_form subst body
      | PA.And l -> F.and_ (List.map (conv_form subst) l) |> ret_f
      | PA.Or l -> F.or_ (List.map (conv_form subst) l) |> ret_f
      | PA.Imply (a,b) ->
        ret_f @@ F.imply (conv_form subst a) (conv_form subst b)
      | PA.Eq (a,b) ->
        let a = conv_term_or_form subst a in
        let b = conv_term_or_form subst b in
        mk_eq_tf_tf a b |> ret_f
      | PA.Distinct l ->
        (* TODO: more efficient "distinct"? *)
        List.map (conv_term_ subst) l
        |> CCList.diagonal
        |> List.map (fun (t,u) -> mk_neq t u |> F.atom)
        |> F.and_ |> ret_f
      | PA.Not f -> F.not_ (conv_form subst f) |> ret_f
      | PA.True -> ret_f F.true_
      | PA.False -> ret_f F.false_
      | PA.Arith (op, l) ->
        let l = List.map (conv_rat subst) l in
        begin match op, l with
          | PA.Minus, [a] -> RLE.neg a |> ret_rat
          | PA.Leq, [a;b] ->
            let e = RLE.diff a b in
            mk_lra_pred Mc2_lra.Leq0 e |> ret_any
          | PA.Geq, [a;b] ->
            let e = RLE.diff b a in
            mk_lra_pred Mc2_lra.Leq0 e |> ret_any
          | PA.Lt, [a;b] ->
            let e = RLE.diff a b in
            mk_lra_pred Mc2_lra.Lt0 e |> ret_any
          | PA.Gt, [a;b] ->
            let e = RLE.diff b a in
            mk_lra_pred Mc2_lra.Lt0 e |> ret_any
          | (PA.Leq | PA.Lt | PA.Geq | PA.Gt), _ ->
            Error.errorf "ill-formed arith expr:@ %a@ (binary operator)" PA.pp_term t
          | PA.Add, _ ->
            let e = List.fold_left (fun n t -> RLE.add t n) RLE.empty l in
            mk_lra_expr e |> ret_t
          | PA.Minus, a::tail ->
            let e =
              List.fold_left
                (fun n t -> RLE.diff n t)
                a tail
            in
            mk_lra_expr e |> ret_t
          | PA.Mult, _::_::_ ->
            let coeffs, terms =
              CCList.partition_map
                (fun t -> match RLE.as_const t with
                   | None -> `Right t
                   | Some c -> `Left c)
                l
            in
            begin match coeffs, terms with
              | c::c_tail, [] ->
                List.fold_right RLE.mult c_tail (RLE.const c) |> ret_rat
              | _, [t] ->
                List.fold_right RLE.mult coeffs t |> ret_rat
              | _ ->
                Error.errorf "non-linear expr:@ `%a`" PA.pp_term t
            end
          | PA.Div, (first::l) ->
            (* support t/a/b/c where only [t] is a rational *)
            let coeffs =
              List.map
                (fun c -> match RLE.as_const c with
                   | None ->
                     Error.errorf "non-linear expr:@ `%a`" PA.pp_term t
                   | Some c -> Q.inv c)
                l
            in
            List.fold_right RLE.mult coeffs first |> ret_rat
          | (PA.Minus | PA.Div | PA.Mult), ([] | [_]) ->
            Error.errorf "ill-formed arith expr:@ %a@ (binary operator)" PA.pp_term t
        end
      | PA.Attr (t,_) -> conv_term_or_form subst t
      | PA.Cast (t, ty_expect) ->
        let t = conv_term_ subst t in
        let ty_expect = conv_ty ty_expect in
        if not (Ty.equal (Term.ty t) ty_expect) then (
          ill_typed "term `%a`@ should have type `%a`" Term.pp t Ty.pp ty_expect
        );
        ret_any t
      | PA.HO_app _ ->
        errorf_ctx "cannot handle HO application"
      | PA.Fun _ -> errorf_ctx "cannot handle lambdas"
      | PA.Match (_lhs, _l) ->
        errorf_ctx "cannot handle match"
      | PA.Is_a _ ->
        errorf_ctx "cannot handle is-a" (* TODO *)
      | PA.Forall _ | PA.Exists _ ->
        errorf_ctx "cannot handle quantifiers" (* TODO *)
    end

  (* expect a term *)
  and conv_term_ subst (t:PA.term) : term =
    match conv_term_or_form subst t with
    | T t -> t
    | Rat e -> mk_lra_expr e
    | F {F.view=F.Lit a;_} when Atom.is_pos a -> Atom.term a
    | F ({F.view=F.Lit _;_} as f) ->
      (* name [¬a] *)
      let placeholder_id = mk_sub_form() in
      decl placeholder_id [] Type.bool;
      let placeholder = mk_const placeholder_id in
      Log.debugf 30
        (fun k->k"(@[smtlib.name_atom@ %a@ :as %a@])" F.pp f ID.pp placeholder_id);
      (* add [placeholder <=> ¬a] *)
      let form = F.equiv (F.atom (Term.Bool.na placeholder)) f in
      side_clauses := List.rev_append (mk_cnf form) !side_clauses;
      placeholder
    | F f ->
      (* name the sub-formula and add CNF *)
      let placeholder_id = mk_sub_form() in
      decl placeholder_id [] Type.bool;
      Log.debugf 30
        (fun k->k"(@[smtlib.name_subform@ %a@ :as %a@])" F.pp f ID.pp placeholder_id);
      let placeholder = mk_const placeholder_id in
      (* add [placeholder <=> f] *)
      let form = F.equiv (F.atom (Term.Bool.pa placeholder)) f in
      side_clauses := List.rev_append (mk_cnf form) !side_clauses;
      placeholder

  and mk_cnf (f:F.t) : atom list list =
    let fresh = SReg.find_exn reg Mc2_propositional.k_fresh in
    F.cnf ~fresh f

  (* convert formula *)
  and conv_form subst (t:PA.term): F.t = match conv_term_or_form subst t with
    | T t -> F.atom (Term.Bool.pa t)
    | F f -> f
    | Rat _ -> Error.errorf "expected proposition,@ got %a" PA.pp_term t

  (* expect a rational expr *)
  and conv_rat subst (t:PA.term) : RLE.t =
    match conv_term_or_form subst t with
    | Rat e -> e
    | T t -> RLE.singleton1 t
    | F _ -> assert false

  let conv_bool_term (t:PA.term): atom list list =
    assert (!side_clauses = []);
    let cs = conv_form Subst.empty t |> mk_cnf in
    let side = !side_clauses in
    side_clauses := [];
    List.rev_append side cs

  let conv_fun_decl f : string * Ty.t list * Ty.t =
    if f.PA.fun_ty_vars <> [] then (
      errorf_ctx "cannot convert polymorphic function@ %a"
        (PA.pp_fun_decl PA.pp_ty) f
    );
    let args = List.map conv_ty f.PA.fun_args in
    let ret = conv_ty f.PA.fun_ret in
    f.PA.fun_name, args, ret

  (* FIXME: fun defs
  let conv_fun_def ctx f_decl body : string * Ty.t * (unit -> T.t) =
    if f_decl.PA.fun_ty_vars <> [] then (
      errorf_ctx ctx "cannot convert polymorphic function@ %a"
        (PA.pp_fun_decl PA.pp_typed_var) f_decl;
    );
    let args = conv_vars ctx f_decl.PA.fun_args in
    let ty =
        (List.map snd args)
        (conv_ty_fst ctx f_decl.PA.fun_ret)
    in
    (* delayed body, for we need to declare the functions in the recursive block first *)
    let conv_body() =
      Ctx.with_vars ctx args
        (fun args ->
           A.fun_l args (conv_term ctx body))
    in
    f_decl.PA.fun_name, ty, conv_body

  let conv_fun_defs ctx decls bodies : A.definition list =
    let l = List.map2 (conv_fun_def ctx) decls bodies in
    let ids = List.map (fun (f,ty,_) -> Ctx.add_id ctx f (Ctx.K_fun ty)) l in
    let defs = List.map2 (fun id (_,ty,body) -> id, ty, body()) ids l in
    (* parse id,ty and declare them before parsing the function bodies *)
    defs
     *)

  let conv_term t = conv_term_ Subst.empty t

  let rec conv_statement (s:PA.statement): Stmt.t list =
    Log.debugf 4 (fun k->k "(@[<1>statement_of_ast@ %a@])" PA.pp_stmt s);
    Ctx.set_loc ?loc:(PA.loc s) ();
    conv_statement_aux s

  and conv_statement_aux (stmt:PA.statement) : Stmt.t list =
    match PA.view stmt with
    | PA.Stmt_set_logic s -> [Stmt.Stmt_set_logic s]
    | PA.Stmt_set_option l -> [Stmt.Stmt_set_option l]
    | PA.Stmt_set_info (a,b) -> [Stmt.Stmt_set_info (a,b)]
    | PA.Stmt_exit -> [Stmt.Stmt_exit]
    | PA.Stmt_decl_sort (s,n) ->
      if n > 0 then (
        errorf_ctx "cannot handle polymorphic type %s" s (* TODO *)
      );
      let id = ID.make s in
      (* declare type, and save it *)
      (* TODO: when handling polymorphic types, will have to kill ctx.types
         and use the function Mc2_unin_sort.k_make directly *)
      SReg.find_exn reg Mc2_unin_sort.k_decl_sort id n;
      let ty = SReg.find_exn reg Mc2_unin_sort.k_make id [] in
      Ctx.add_ty_ s id ty;
      [Stmt.Stmt_ty_decl (id, n)]
    | PA.Stmt_decl fr ->
      let f, args, ret = conv_fun_decl fr in
      let id = ID.make f in
      decl id args ret;
      Ctx.add_term_fun_ f id;
      [Stmt.Stmt_decl (id, args,ret)]
    | PA.Stmt_data _l ->
      errorf_ctx "cannot handle datatype in %a" PA.pp_stmt stmt
      (* FIXME
      [Stmt.Stmt_data l]
         *)
    | PA.Stmt_funs_rec _defs ->
      errorf_ctx "not implemented: definitions in %a" PA.pp_stmt stmt
        (* TODO
      let {PA.fsr_decls=decls; fsr_bodies=bodies} = defs in
      if List.length decls <> List.length bodies then (
        errorf_ctx ctx "declarations and bodies should have same length";
      );
      let defs = conv_fun_defs ctx decls bodies in
      [A.Define defs]
           *)
    | PA.Stmt_fun_def
        {PA.fr_decl={PA.fun_ty_vars=[]; fun_args=[]; fun_name; fun_ret}; fr_body} ->
      (* turn [def f : ret := body] into [decl f : ret; assert f=body] *)
      let ret = conv_ty fun_ret in
      let id = ID.make fun_name in
      decl id [] ret;
      Ctx.add_term_fun_ fun_name id;
      let eq_def = conv_bool_term @@ PA.eq (PA.const fun_name) fr_body in
      [ Stmt.Stmt_decl (id,[],ret);
        Stmt.Stmt_assert_clauses eq_def;
      ]
    | PA.Stmt_fun_rec _
    | PA.Stmt_fun_def _ ->
      (* TODO: handle non recursive definitions *)
      errorf_ctx "unsupported definition: %a" PA.pp_stmt stmt
    | PA.Stmt_assert t ->
      let cs = conv_bool_term t in
      [Stmt.Stmt_assert_clauses cs]
    | PA.Stmt_check_sat -> [Stmt.Stmt_check_sat]
    | PA.Stmt_check_sat_assuming _
    | PA.Stmt_get_assertions
    | PA.Stmt_get_option _
    | PA.Stmt_get_info _
    | PA.Stmt_get_model
    | PA.Stmt_get_proof
    | PA.Stmt_get_unsat_core
    | PA.Stmt_get_unsat_assumptions
    | PA.Stmt_get_assignment
    | PA.Stmt_reset
    | PA.Stmt_reset_assertions
    | PA.Stmt_push _
    | PA.Stmt_pop _
    | PA.Stmt_get_value _
      ->
      (* TODO: handle more of these *)
      errorf_ctx "cannot handle statement %a" PA.pp_stmt stmt

end
