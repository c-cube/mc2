
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

open Mc2_core

module Loc = Locations
module Fmt = CCFormat

type 'a or_error = ('a, string) CCResult.t

exception Error of string
exception Ill_typed of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some ("ast error: " ^ msg)
      | Ill_typed msg -> Some ("ill-typed: " ^ msg)
      | _ -> None)

let errorf msg =
  CCFormat.ksprintf ~f:(fun e -> raise (Error e)) msg

(** {2 Types} *)

module Var = struct
  type 'ty t = {
    id: ID.t;
    ty: 'ty;
  }

  let make id ty = {id;ty}
  let makef ~ty fmt =
    CCFormat.ksprintf fmt ~f:(fun s -> make (ID.make s) ty)
  let copy {id;ty} = {ty; id=ID.copy id}
  let id v = v.id
  let ty v = v.ty

  let equal a b = ID.equal a.id b.id
  let compare a b = ID.compare a.id b.id
  let pp out v = ID.pp out v.id
end

module Ty = struct
  type t =
    | Bool
    | Rat
    | Atomic of ID.t * t list
    | Arrow of t * t

  let bool = Bool
  let rat = Rat
  let app id l = Atomic (id,l)
  let const id = app id []
  let arrow a b = Arrow (a,b)
  let arrow_l = List.fold_right arrow

  let to_int_ = function
    | Bool -> 0
    | Atomic _ -> 1
    | Arrow _ -> 2
    | Rat -> 3

  let (<?>) = CCOrd.(<?>)

  let rec compare a b = match a, b with
    | Bool, Bool
    | Rat, Rat -> 0
    | Atomic (f1,l1), Atomic (f2,l2) ->
      CCOrd.Infix.( ID.compare f1 f2 <?> (CCOrd.list compare, l1, l2))
    | Arrow (a1,a2), Arrow (b1,b2) ->
      compare a1 b1 <?> (compare, a2,b2)
    | Bool, _
    | Atomic _, _
    | Arrow _, _
    | Rat, _
      -> CCInt.compare (to_int_ a) (to_int_ b)

  let equal a b = compare a b = 0

  let hash _ = 0 (* TODO *)

  let unfold ty =
    let rec aux acc ty = match ty with
      | Arrow (a,b) -> aux (a::acc) b
      | _ -> List.rev acc, ty
    in
    aux [] ty

  let rec pp out t = match t with
    | Bool -> Fmt.string out "Bool"
    | Rat -> Fmt.string out "Real"
    | Atomic (id,[]) -> ID.pp out id
    | Atomic (id,l) -> Fmt.fprintf out "(@[%a@ %a@])" ID.pp id (Util.pp_list pp) l
    | Arrow _ ->
      let args, ret = unfold t in
      Fmt.fprintf out "(@[-> %a@ %a@])" (Util.pp_list pp) args pp ret

  (** {2 Datatypes} *)

  type data = {
    data_id: ID.t;
    data_cstors: t ID.Map.t;
  }

  module Map = CCMap.Make(struct
      type _t = t
      type t = _t
      let compare = compare
    end)

  let ill_typed fmt =
    CCFormat.ksprintf
      ~f:(fun s -> raise (Ill_typed s))
      fmt
end

type var = Ty.t Var.t

type op =
  | And
  | Or
  | Imply
  | Eq
  | Distinct

type arith_op =
  | Leq
  | Lt
  | Geq
  | Gt
  | Add
  | Minus
  | Mult
  | Div

type binder =
  | Fun
  | Forall
  | Exists
  | Mu

type term = {
  term: term_cell;
  ty: Ty.t;
}
and term_cell =
  | Var of var
  | Const of ID.t
  | Num_z of Z.t
  | Num_q of Q.t
  | App of term * term list
  | If of term * term * term
  | Select of select * term
  | Match of term * (var list * term) ID.Map.t
  | Bind of binder * var * term
  | Arith of arith_op * term list
  | Let of var * term * term
  | Not of term
  | Op of op * term list
  | Bool of bool

and select = {
  select_name: ID.t lazy_t;
  select_cstor: ID.t;
  select_i: int;
}

type definition = ID.t * Ty.t * term

type statement =
  | SetLogic of string
  | SetOption of string list
  | SetInfo of string list
  | TyDecl of ID.t * int (* new atomic cstor *)
  | Decl of ID.t * Ty.t
  | Assert of term
  | CheckSat
  | Goal of var list * term
  | Exit
        (*
  | Data of Ty.data list
  | Define of definition list
           *)

(** {2 Helper} *)

let unfold_binder b t =
  let rec aux acc t = match t.term with
    | Bind (b', v, t') when b=b' -> aux (v::acc) t'
    | _ -> List.rev acc, t
  in
  aux [] t

let unfold_fun = unfold_binder Fun

let pp_binder out = function
  | Forall -> Fmt.string out "forall"
  | Exists -> Fmt.string out "exists"
  | Fun -> Fmt.string out "lambda"
  | Mu -> Fmt.string out "mu"

let pp_op out = function
  | And -> Fmt.string out "and"
  | Or -> Fmt.string out "or"
  | Imply -> Fmt.string out "=>"
  | Eq -> Fmt.string out "="
  | Distinct -> Fmt.string out "distinct"

let pp_arith out = function
  | Leq -> Fmt.string out "<="
  | Lt -> Fmt.string out "<"
  | Geq -> Fmt.string out ">="
  | Gt -> Fmt.string out ">"
  | Add -> Fmt.string out "+"
  | Minus -> Fmt.string out "-"
  | Mult -> Fmt.string out "*"
  | Div -> Fmt.string out "/"

let pp_term =
  let rec pp out t = match t.term with
    | Var v -> Var.pp out v
    | Const id -> ID.pp out id
    | App (f, l) -> Fmt.fprintf out "(@[<hv1>%a@ %a@])" pp f (Util.pp_list pp) l
    | If (a,b,c) -> Fmt.fprintf out "(@[<hv>ite@ %a@ %a@ %a@])" pp a pp b pp c
    | Select (s, t) ->
      Fmt.fprintf out "(@[select-%a-%d@ %a@])"
        ID.pp (Lazy.force s.select_name) s.select_i pp t
    | Match (u, m) ->
      let pp_case out (id,(vars,rhs)) =
        if vars=[] then Fmt.fprintf out "(@[<2>case %a@ %a@])" ID.pp id pp rhs
        else Fmt.fprintf out "(@[<2>case (@[%a@ %a@])@ %a@])"
            ID.pp id (Util.pp_list Var.pp) vars pp rhs
      in
      Fmt.fprintf out "(@[<hv2>match %a@ %a@])"
        pp u (Util.pp_list pp_case) (ID.Map.to_list m)
    | Bool b -> Fmt.fprintf out "%B" b
    | Not t -> Fmt.fprintf out "(@[<1>not@ %a@])" pp t
    | Op (o,l) -> Fmt.fprintf out "(@[<hv1>%a@ %a@])" pp_op o (Util.pp_list pp) l
    | Bind (b,v,u) ->
      Fmt.fprintf out "(@[<1>%a ((@[%a@ %a@]))@ %a@])"
        pp_binder b Var.pp v Ty.pp (Var.ty v) pp u
    | Let (v,t,u) ->
      Fmt.fprintf out "(@[<1>let ((@[%a@ %a@]))@ %a@])" Var.pp v pp t pp u
    | Num_z z -> Z.pp_print out z
    | Num_q z -> Q.pp_print out z
    | Arith (op, l) ->
      Fmt.fprintf out "(@[<hv>%a@ %a@])" pp_arith op (Util.pp_list pp) l
  in pp

(* FIXME
   let pp_data out d =
   let cstors =
    ID.Map.fold
      (fun c ty acc ->
         let ty_args, _ = unfold ty in
         let c_sexp = match ty_args with
           | [] -> ID.to_sexp c
           | _::_ -> S.of_list (ID.to_sexp c :: List.map to_sexp ty_args)
         in
         c_sexp :: acc)
      d.data_cstors []
   in
   S.of_list (ID.to_sexp d.data_id :: cstors)
*)

(** {2 Constructors} *)

let[@inline] term_view t = t.term

let rec app_ty_ ty l : Ty.t = match ty, l with
  | _, [] -> ty
  | Ty.Arrow (ty_a,ty_rest), a::tail ->
    if Ty.equal ty_a a.ty
    then app_ty_ ty_rest tail
    else (
      Ty.ill_typed "expected `@[%a@]`,@ got `@[%a : %a@]`"
        Ty.pp ty_a pp_term a Ty.pp a.ty
    )
  | (Ty.Bool | Ty.Rat | Ty.Atomic _), a::_ ->
    Ty.ill_typed "cannot apply ty `@[%a@]`@ to `@[%a@]`" Ty.pp ty pp_term a

let[@inline] mk_ term ty = {term; ty}
let[@inline] ty t = t.ty

let true_ = mk_ (Bool true) Ty.bool
let false_ = mk_ (Bool false) Ty.bool

let var v = mk_ (Var v) (Var.ty v)

let const id ty = mk_ (Const id) ty

let select (s:select) (t:term) ty = mk_ (Select (s,t)) ty

let app f l = match f.term, l with
  | _, [] -> f
  | App (f1, l1), _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f1, l1 @ l)) ty
  | _ ->
    let ty = app_ty_ f.ty l in
    mk_ (App (f, l)) ty

let app_a f a = app f (Array.to_list a)

let if_ a b c =
  if a.ty <> Ty.Bool
  then Ty.ill_typed "if: test  must have type bool, not `@[%a@]`" Ty.pp a.ty;
  if not (Ty.equal b.ty c.ty)
  then Ty.ill_typed
      "if: both branches must have same type,@ not `@[%a@]` and `@[%a@]`"
      Ty.pp b.ty Ty.pp c.ty;
  mk_ (If (a,b,c)) b.ty

let match_ t m =
  let c1, (_, rhs1) = ID.Map.choose m in
  ID.Map.iter
    (fun c (_, rhs) ->
       if not (Ty.equal rhs1.ty rhs.ty)
       then Ty.ill_typed
           "match: cases %a and %a disagree on return type,@ \
            between %a and %a"
           ID.pp c1 ID.pp c Ty.pp rhs1.ty Ty.pp rhs.ty)
    m;
  mk_ (Match (t,m)) rhs1.ty

let let_ v t u =
  if not (Ty.equal (Var.ty v) t.ty)
  then Ty.ill_typed
      "let: variable %a : @[%a@]@ and bounded term : %a@ should have same type"
      Var.pp v Ty.pp (Var.ty v) Ty.pp t.ty;
  mk_ (Let (v,t,u)) u.ty

let let_l l u =
  List.fold_right (fun (v,t) u -> let_ v t u) l u

let bind ~ty b v t = mk_ (Bind(b,v,t)) ty

let arith ty op l = mk_ (Arith (op,l)) ty

let num_q ty z = mk_ (Num_q z) ty
let num_z ty z = mk_ (Num_z z) ty

let parse_num ~where (s:string) : [`Q of Q.t | `Z of Z.t] =
  let fail() =
    errorf "%sexpected number, got `%s`" (Lazy.force where) s
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

let num_str ty s =
  begin match parse_num ~where:(Lazy.from_val "") s with
    | `Q x -> num_q ty x
    | `Z x -> num_z ty x
  end

let fun_ v t =
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Bind (Fun,v,t)) ty

let quant_ q v t =
  if not (Ty.equal t.ty Ty.bool) then (
    Ty.ill_typed
      "quantifier: bounded term : %a@ should have type bool"
      Ty.pp t.ty;
  );
  let ty = Ty.bool in
  mk_ (q v t) ty

let forall = quant_ (fun v t -> Bind (Forall,v,t))
let exists = quant_ (fun v t -> Bind (Exists,v,t))

let mu v t =
  if not (Ty.equal (Var.ty v) t.ty)
  then Ty.ill_typed "mu-term: var has type %a,@ body %a"
      Ty.pp (Var.ty v) Ty.pp t.ty;
  let ty = Ty.arrow (Var.ty v) t.ty in
  mk_ (Bind (Fun,v,t)) ty

let fun_l = List.fold_right fun_
let fun_a = Array.fold_right fun_
let forall_l = List.fold_right forall
let exists_l = List.fold_right exists
let mu_l = List.fold_right mu

let eq_neq_ op l = match l with
  | [] -> Ty.ill_typed "empty `distinct` is forbidden"
  | a :: tail ->
    begin match CCList.find_pred (fun b -> not @@ Ty.equal a.ty b.ty) tail with
      | Some b ->
        Ty.ill_typed "%a: `@[%a@]` and `@[%a@]` do not have the same type"
          pp_op op pp_term a pp_term b;
      | None ->
        mk_ (Op (op, l)) Ty.bool
    end

let eq_l = eq_neq_ Eq
let eq a b = eq_l [a;b]
let distinct = eq_neq_ Distinct

let check_bool_ t =
  if not (Ty.equal t.ty Ty.bool)
  then Ty.ill_typed "expected bool, got `@[%a : %a@]`" pp_term t Ty.pp t.ty

let mk_bool_op op l =
  List.iter check_bool_ l;
  mk_ (Op (op,l)) Ty.bool

let and_l = mk_bool_op And
let or_l = mk_bool_op Or
let imply_l = mk_bool_op Imply

let and_ a b = and_l [a;b]
let or_ a b = or_l [a;b]
let imply a b = imply_l [a;b]

let not_ t =
  check_bool_ t;
  mk_ (Not t) Ty.bool

(** {2 Printing} *)

let pp_statement out = function
  | SetLogic s -> Fmt.fprintf out "(set-logic %s)" s
  | SetOption l -> Fmt.fprintf out "(@[set-logic@ %a@])" (Util.pp_list Fmt.string) l
  | SetInfo l -> Fmt.fprintf out "(@[set-info@ %a@])" (Util.pp_list Fmt.string) l
  | CheckSat -> Fmt.string out "(check-sat)"
  | TyDecl (s,n) -> Fmt.fprintf out "(@[declare-sort@ %a %d@])" ID.pp s n
  | Decl (id,ty) ->
    let args, ret = Ty.unfold ty in
    Fmt.fprintf out "(@[<1>declare-fun@ %a (@[%a@])@ %a@])"
      ID.pp id (Util.pp_list Ty.pp) args Ty.pp ret
  | Assert t -> Fmt.fprintf out "(@[assert@ %a@])" pp_term t
  | Goal (vars,g) ->
    Fmt.fprintf out "(@[assert-not@ %a@])" pp_term (forall_l vars (not_ g))
  | Exit -> Fmt.string out "(exit)"
    (*
  | Data _
  | TyDecl _
  | Define _
     *)

(** {2 Parsing} *)

module StrTbl = CCHashtbl.Make(struct
    type t = string
    let equal = CCString.equal
    let hash = CCString.hash
  end)

module Ctx = struct
  type kind =
    | K_ty of ty_kind
    | K_fun of Ty.t
    | K_var of var (* local *)
  (* FIXME
     | K_cstor of Ty.t
     | K_select of Ty.t * select
  *)

  and ty_kind =
    | K_uninterpreted (* uninterpreted type *)
    | K_other
    | K_bool
    (* FIXME
       | K_data (* data type *)
    *)

  type t = {
    names: ID.t StrTbl.t;
    kinds: kind ID.Tbl.t;
    data: (ID.t * Ty.t) list ID.Tbl.t; (* data -> cstors *)
    mutable loc: Locations.t option; (* current loc *)
  }

  let create () : t = {
    names=StrTbl.create 64;
    kinds=ID.Tbl.create 64;
    data=ID.Tbl.create 64;
    loc=None;
  }

  let loc t = t.loc
  let set_loc ?loc t = t.loc <- loc

  let add_id t (s:string) (k:kind): ID.t =
    let id = ID.make s in
    StrTbl.add t.names s id;
    ID.Tbl.add t.kinds id k;
    id

  let add_data t (id:ID.t) cstors: unit =
    ID.Tbl.add t.data id cstors

  let with_var t (s:string) (ty:Ty.t) (f:Ty.t Var.t -> 'a): 'a =
    let id = ID.make s in
    StrTbl.add t.names s id;
    let v = Var.make id ty in
    ID.Tbl.add t.kinds id (K_var v);
    CCFun.finally1 f v
      ~h:(fun () -> StrTbl.remove t.names s)

  let with_vars t (l:(string*Ty.t) list) (f:Ty.t Var.t list -> 'a): 'a =
    let rec aux ids l f = match l with
      | [] -> f (List.rev ids)
      | (s,ty) :: l' -> with_var t s ty (fun id -> aux (id::ids) l' f)
    in
    aux [] l f

  let find_kind t (id:ID.t) : kind =
    try ID.Tbl.find t.kinds id
    with Not_found -> errorf "did not find kind of ID `%a`" ID.pp id

  let as_data t (ty:Ty.t) : (ID.t * Ty.t) list = match ty with
    | Ty.Atomic (id,_) ->
      begin match ID.Tbl.get t.data id with
        | Some l -> l
        | None -> errorf "expected %a to be a datatype" Ty.pp ty
      end
    | _ -> errorf "expected %a to be a constant type" Ty.pp ty

  let pp_kind out = function
    | K_ty _ -> Format.fprintf out "type"
        (*
    | K_cstor ty ->
      Format.fprintf out "(@[cstor : %a@])" Ty.pp ty
    | K_select (ty,s) ->
      Format.fprintf out "(@[select-%a-%d : %a@])"
        ID.pp s.select_cstor s.select_i Ty.pp ty
           *)
    | K_fun ty ->
      Format.fprintf out "(@[fun : %a@])" Ty.pp ty
    | K_var v ->
      Format.fprintf out "(@[var : %a@])" Ty.pp (Var.ty v)

  let pp out t =
    Format.fprintf out "ctx {@[%a@]}"
      (ID.Tbl.print ID.pp pp_kind) t.kinds
end

let error_loc ctx : string = Fmt.sprintf "at %a: " Locations.pp_opt (Ctx.loc ctx)
let errorf_ctx ctx msg =
  errorf ("at %a:@ " ^^ msg) Locations.pp_opt (Ctx.loc ctx)

let find_id_ ctx (s:string): ID.t =
  try StrTbl.find ctx.Ctx.names s
  with Not_found -> errorf_ctx ctx "name `%s` not in scope" s

module A = Parse_ast

let rec conv_ty ctx (t:A.ty) =
  try conv_ty_aux ctx t
  with Ill_typed msg ->
    Ty.ill_typed "at %a:@ %s" Locations.pp_opt (Ctx.loc ctx) msg

and conv_ty_aux ctx t = match t with
  | A.Ty_bool -> Ty.bool, Ctx.K_ty Ctx.K_bool
  | A.Ty_real -> Ty.rat, Ctx.K_ty Ctx.K_other
  | A.Ty_app (s,l) ->
    let id = find_id_ ctx s in
    let l = List.map (conv_ty_fst ctx) l in
    Ty.app id l, Ctx.find_kind ctx id
  | A.Ty_arrow (args, ret) ->
    let args = List.map (conv_ty_fst ctx) args in
    let ret, _ = conv_ty ctx ret in
    Ty.arrow_l args ret, Ctx.K_ty Ctx.K_other

and conv_ty_fst ctx t = fst (conv_ty ctx t)

let conv_vars ctx l = List.map (fun (v,ty) -> v, conv_ty_fst ctx ty) l

let is_num s =
  let is_digit_or_dot = function '0' .. '9' | '.' -> true | _ -> false in
  if s.[0] = '-'
  then CCString.for_all is_digit_or_dot (String.sub s 1 (String.length s-1))
  else CCString.for_all is_digit_or_dot s

let rec conv_term ctx (t:A.term) : term =
  try conv_term_aux ctx t
  with Ill_typed msg ->
    Ty.ill_typed "at %a:@ %s" Locations.pp_opt (Ctx.loc ctx) msg

and conv_term_aux ctx t : term = match t with
  | A.True -> true_
  | A.False -> false_
  | A.Const s when is_num s ->
    (* numeral *)
    begin match parse_num ~where:(lazy (error_loc ctx)) s with
      | `Q n -> num_q Ty.rat n
      | `Z n -> num_z Ty.rat n
    end
  | A.Const s ->
    let id = find_id_ ctx s in
    begin match Ctx.find_kind ctx id with
      | Ctx.K_var v -> var v
      | Ctx.K_fun ty -> const id ty
      | Ctx.K_ty _ ->
        errorf_ctx ctx "expected term, not type; got `%a`" ID.pp id
          (*
      | Ctx.K_cstor ty -> const id ty
      | Ctx.K_select _ -> errorf_ctx ctx "unapplied `select` not supported"
             *)
    end
  | A.If (a,b,c) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    let c = conv_term ctx c in
    if_ a b c
  | A.Fun ((v,ty), body) ->
    let ty, _ = conv_ty ctx ty in
    Ctx.with_var ctx v ty
      (fun var ->
         let body = conv_term ctx body in
         fun_ var body)
  | A.Forall (vars, body) ->
    let vars = conv_vars ctx vars in
    Ctx.with_vars ctx vars
      (fun vars ->
         let body = conv_term ctx body in
         forall_l vars body)
  | A.Exists (vars, body) ->
    let vars = conv_vars ctx vars in
    Ctx.with_vars ctx vars
      (fun vars ->
         let body = conv_term ctx body in
         exists_l vars body)
  | A.Let (l,u) ->
    let l =
      List.map (fun (v,t) ->
        let t = conv_term ctx t in
        (v, ty t), t)
        l
    in
    Ctx.with_vars ctx (List.map fst l)
      (fun vars ->
         let l = List.map2 (fun v (_,t) -> v,t) vars l in
         let u = conv_term ctx u in
         let_l l u)
  | A.Distinct l ->
    let l = List.map (conv_term ctx) l in
    distinct l
  | A.And l ->
    let l = List.map (conv_term ctx) l in
    and_l l
  | A.Or l ->
    let l = List.map (conv_term ctx) l in
    or_l l
  | A.Not a ->
    let a = conv_term ctx a in
    not_ a
  | A.Eq (a,b) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    eq a b
  | A.Imply (a,b) ->
    let a = conv_term ctx a in
    let b = conv_term ctx b in
    imply a b
  | A.Match (_lhs, _l) ->
    assert false
  (* FIXME
     (* convert a regular case *)
     let conv_case c vars rhs =
     let c_id = find_id_ ctx c in
     (* obtain the type *)
     let ty_args, _ty_ret = match Ctx.find_kind ctx c_id with
      | Ctx.K_cstor ty -> Ty.unfold ty
      | _ ->
        errorf_ctx ctx "expected `@[%a@]`@ to be a constructor" ID.pp c_id
     in
     (* pair variables with their type *)
     if List.length vars <> List.length ty_args
     then
      errorf_ctx ctx
        "in @[%a@] for case %a,@ wrong number of arguments (expected %d)"
        A.pp_term t ID.pp c_id (List.length ty_args);
     let vars = List.combine vars ty_args in
     Ctx.with_vars ctx vars
      (fun vars ->
         let rhs = conv_term ctx rhs in
         c_id, vars, rhs)
     in
     (* convert default case, where [m] contains the partial map. We have
     to complete this map *)
     let lhs = conv_term ctx lhs in
     let default, cases =
     List.fold_left
      (fun (def,cases) branch -> match branch with
         | A.Match_case (c,vars,rhs) ->
           let c, vars, rhs = conv_case c vars rhs in
           (* no duplicate *)
           if ID.Map.mem c cases
           then errorf_ctx ctx "constructor %a occurs twice" ID.pp c;
           def, ID.Map.add c (vars,rhs) cases
        | A.Match_default rhs ->
          (* check there is only one "default" case *)
          match def with
            | Some _ -> errorf_ctx ctx "cannot have two `default` cases"
            | None ->
              let rhs = conv_term ctx rhs in
              Some rhs, cases)
      (None,ID.Map.empty) l
     in
     (* now fill the blanks, check exhaustiveness *)
     let all_cstors = Ctx.as_data ctx lhs.ty in
     let cases = match default with
     | None ->
      (* check exhaustiveness *)
      let missing =
        all_cstors
        |> List.filter (fun (cstor,_) -> not (ID.Map.mem cstor cases))
        |> List.map fst
      in
      if missing<>[]
      then errorf_ctx ctx
          "missing cases in `@[%a@]`: @[%a@]"
          A.pp_term t (Util.pp_list ID.pp) missing;
      cases
     | Some def_rhs ->
      List.fold_left
        (fun cases (cstor,ty_cstor) ->
           if ID.Map.mem cstor cases then cases
           else (
             let args, _ = Ty.unfold ty_cstor in
             let vars = List.mapi (fun i ty -> Var.makef ~ty "_%d" i) args in
             ID.Map.add cstor (vars, def_rhs) cases
           ))
        cases all_cstors
     in
     match_ lhs cases
  *)
  | A.App (s, args) ->
    let id = find_id_ ctx s in
    let args = List.map (conv_term ctx) args in
    begin match Ctx.find_kind ctx id, args with
      | Ctx.K_var v, _ -> app (var v) args
      | Ctx.K_fun ty, _ -> app (const id ty) args
      | Ctx.K_ty _, _ ->
        errorf_ctx ctx "expected term, not type; got `%a`" ID.pp id
        (*
      | Ctx.K_cstor ty, _ -> app (const id ty) args
      | Ctx.K_select (ty, sel), [arg] -> select sel arg ty
      | Ctx.K_select _, _ ->
        errorf_ctx ctx "select `%a`@ should be applied to exactly one arg"
          A.pp_term t
           *)
    end
  | A.HO_app (f, arg) ->
    let f = conv_term ctx f in
    let arg = conv_term ctx arg in
    app f [arg]
  | A.Arith (op, l) ->
    let l = List.map (conv_term ctx) l in
    List.iter
      (fun t ->
         if not (Ty.equal Ty.rat (ty t)) then (
           errorf_ctx ctx "expected rational term,@ got `%a`" pp_term t
         ))
      l;
    let ty, op = match op with
      | A.Leq -> Ty.bool, Leq
      | A.Lt -> Ty.bool, Lt
      | A.Geq -> Ty.bool, Geq
      | A.Gt -> Ty.bool, Gt
      | A.Add -> Ty.rat, Add
      | A.Minus -> Ty.rat, Minus
      | A.Mult -> Ty.rat, Mult
      | A.Div -> Ty.rat, Div
    in
    arith ty op l
  | A.Cast (t, ty_expect) ->
    let t = conv_term ctx t in
    let ty_expect = conv_ty_fst ctx ty_expect in
    if not (Ty.equal (ty t) ty_expect) then (
      Ty.ill_typed "term `%a`@ should have type `%a`" pp_term t Ty.pp ty_expect
    );
    t

let find_file_ name ~dir : string option =
  Log.debugf 2 (fun k->k "search A.%sA. in A.%sA." name dir);
  let abs_path = Filename.concat dir name in
  if Sys.file_exists abs_path
  then Some abs_path
  else None

let conv_fun_decl ctx f =
  if f.A.fun_ty_vars <> [] then (
    errorf_ctx ctx "cannot convert polymorphic function@ %a"
      (A.pp_fun_decl A.pp_ty) f
  );
  let args = List.map (conv_ty_fst ctx) f.A.fun_args in
  let ty = Ty.arrow_l args (conv_ty_fst ctx f.A.fun_ret) in
  f.A.fun_name, ty

let conv_fun_def ctx f body =
  if f.A.fun_ty_vars <> [] then (
    errorf_ctx ctx "cannot convert polymorphic function@ %a"
      (A.pp_fun_decl A.pp_typed_var) f;
  );
  let args = conv_vars ctx f.A.fun_args in
  Ctx.with_vars ctx args
    (fun args ->
       let ty =
         Ty.arrow_l
           (List.map Var.ty args)
           (conv_ty_fst ctx f.A.fun_ret)
       in
       f.A.fun_name, ty, fun_l args (conv_term ctx body))

let rec conv_statement ctx (s:A.statement): statement list =
  Log.debugf 4 (fun k->k "(@[<1>statement_of_ast@ %a@])" A.pp_stmt s);
  Ctx.set_loc ctx ?loc:s.A.loc;
  conv_statement_aux ctx s

and conv_statement_aux ctx (stmt:A.statement) : statement list = match A.view stmt with
  | A.Stmt_set_logic s -> [SetLogic s]
  | A.Stmt_set_option l -> [SetOption l]
  | A.Stmt_set_info l -> [SetInfo l]
  | A.Stmt_exit -> [Exit]
  | A.Stmt_decl_sort (s,n) ->
    let id = Ctx.add_id ctx s (Ctx.K_ty Ctx.K_uninterpreted) in
    [TyDecl (id,n)]
  | A.Stmt_decl fr ->
    let f, ty = conv_fun_decl ctx fr in
    let id = Ctx.add_id ctx f (Ctx.K_fun ty) in
    [Decl (id, ty)]
  | A.Stmt_data ([],_l) ->
    assert false
  (* FIXME
     (* first, read and declare each datatype (it can occur in the other
     datatypes' construtors) *)
     let pre_parse (data_name,cases) =
     let data_id = Ctx.add_id ctx data_name (Ctx.K_ty Ctx.K_data) in
     data_id, cases
     in
     let l = List.map pre_parse l in
     (* now parse constructors *)
     let l =
     List.map
      (fun (data_id, cstors) ->
         let data_ty = Ty.const data_id in
         let parse_case (c, ty_args) =
           let selectors =
             List.map (fun (n,ty) -> n, conv_ty_fst ctx ty) ty_args
           in
           let ty_args = List.map snd selectors in
           (* declare cstor *)
           let ty_c = Ty.arrow_l ty_args data_ty in
           let id_c = Ctx.add_id ctx c (Ctx.K_cstor ty_c) in
           (* now declare selectors *)
           List.iteri
             (fun i (name_opt,ty) -> match name_opt with
                | None -> ()
                | Some select_str ->
                  (* declare this selector *)
                  let rec select_name = lazy
                    (Ctx.add_id ctx select_str
                       (Ctx.K_select (ty,
                          {select_name; select_cstor=id_c; select_i=i})))
                  in
                  ignore (Lazy.force select_name))
             selectors;
           (* return cstor *)
           id_c, ty_c
         in
         let cstors = List.map parse_case cstors in
         (* update info on [data] *)
         Ctx.add_data ctx data_id cstors;
         {Ty.data_id; data_cstors=ID.Map.of_list cstors})
      l
     in
     [Data l]
  *)
  | A.Stmt_data _ ->
    errorf_ctx ctx "not implemented: parametric datatypes" A.pp_stmt stmt
  | A.Stmt_funs_rec _defs ->
    errorf_ctx ctx "not implemented: definitions" A.pp_stmt stmt
  (* FIXME
     let {A.fsr_decls=decls; fsr_bodies=bodies} = defs in
     if List.length decls <> List.length bodies then (
     errorf_ctx ctx "declarations and bodies should have same length";
     );
     let l = List.map2 (conv_fun_def ctx) decls bodies in
     [def ?loc l |> CCOpt.return
     (* parse id,ty and declare them before parsing the function bodies *)
     let preparse fd =
     let name, ty, rhs = conv_fun_def ctx
     let ty, _ = conv_ty ctx ty in
     let id = Ctx.add_id ctx name (Ctx.K_fun ty) in
     id, ty, rhs
     in
     let defs = List.map preparse defs in
     let defs =
     List.map
      (fun (id,ty,rhs) ->
         let rhs = conv_term ctx rhs in
         id,ty,rhs)
      defs
     in
     [Define defs]
  *)
  | A.Stmt_fun_rec _def ->
    errorf_ctx ctx "not implemented: definitions" A.pp_stmt stmt
  | A.Stmt_fun_def _def ->
    errorf_ctx ctx "not implemented: definitions" A.pp_stmt stmt
  | A.Stmt_assert t ->
    let t = conv_term ctx t in
    check_bool_ t;
    [Assert t]
  | A.Stmt_assert_not ([], t) ->
    let vars, t = unfold_binder Forall (conv_term ctx t) in
    let g = not_ t in (* negate *)
    [Goal (vars, g)]
  | A.Stmt_assert_not (_::_, _) ->
    errorf_ctx ctx "cannot convert polymorphic goal@ `@[%a@]`"
      A.pp_stmt stmt
  | A.Stmt_lemma _ ->
    errorf_ctx ctx "smbc does not know how to handle `lemma` statements"
  | A.Stmt_check_sat -> [CheckSat]

let parse_chan_exn ?(filename="<no name>") ic =
  let lexbuf = Lexing.from_channel ic in
  Loc.set_file lexbuf filename;
  Parser.parse_list Lexer.token lexbuf

let parse_chan ?filename ic =
  try Result.Ok (parse_chan_exn ?filename ic)
  with e -> Result.Error (Printexc.to_string e)

let parse_file_exn file : A.statement list =
  CCIO.with_in file (parse_chan_exn ~filename:file)

let parse_file file =
  try Result.Ok (parse_file_exn file)
  with e -> Result.Error (Printexc.to_string e)

let parse_file_exn ctx file : statement list =
  (* delegate parsing to [Tip_parser] *)
  parse_file_exn file
  |> CCList.flat_map (conv_statement ctx)

let parse file =
  let ctx = Ctx.create () in
  try Result.Ok (parse_file_exn ctx file)
  with e -> Result.Error (Printexc.to_string e)

let parse_stdin () =
  let ctx = Ctx.create () in
  try
    parse_chan_exn ~filename:"<stdin>" stdin
    |> CCList.flat_map (conv_statement ctx)
    |> CCResult.return
  with e -> Result.Error (Printexc.to_string e)
