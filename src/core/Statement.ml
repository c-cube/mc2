open Solver_types

type t = statement =
  | Stmt_set_logic of string
  | Stmt_set_option of string list
  | Stmt_set_info of string * string
  (* | Stmt_data of data list *)
  | Stmt_ty_decl of ID.t * int (* new atomic cstor *)
  | Stmt_decl of ID.t * ty list * ty
  | Stmt_define of definition list
  | Stmt_assert_clauses of atom list list
  | Stmt_check_sat
  | Stmt_exit

let pp_def out (d:definition) : unit =
  let id, vars, ret, body = d in
  Fmt.fprintf out "@[%a (@[%a@]) %a@ %a@]"
    ID.pp id (Util.pp_list Bound_var.pp_with_ty) vars Type.pp ret Term.pp body

let pp out = function
  | Stmt_set_logic s -> Fmt.fprintf out "(set-logic %s)" s
  | Stmt_set_option l -> Fmt.fprintf out "(@[set-logic@ %a@])" (Util.pp_list Fmt.string) l
  | Stmt_set_info (a,b) -> Fmt.fprintf out "(@[set-info@ %s@ %s@])" a b
  | Stmt_check_sat -> Fmt.string out "(check-sat)"
  | Stmt_ty_decl (s,n) -> Fmt.fprintf out "(@[declare-sort@ %a %d@])" ID.pp s n
  | Stmt_decl (id,args,ret) ->
    Fmt.fprintf out "(@[<1>declare-fun@ %a (@[%a@])@ %a@])"
      ID.pp id (Util.pp_list Type.pp) args Type.pp ret
  | Stmt_assert_clauses cs ->
    let pp_c out c =
      Fmt.fprintf out "(@[assert-clause@ %a@])" (Util.pp_list Atom.pp) c
    in
    Fmt.fprintf out "@[<v>%a@]" (Util.pp_list pp_c) cs
  | Stmt_exit -> Fmt.string out "(exit)"
  | Stmt_define [def] ->
    Fmt.fprintf out "(@[define-fun %a@])" pp_def def
  | Stmt_define defs ->
    Fmt.fprintf out "(@[define-funs (@[%a@])@])" (Util.pp_list pp_def) defs
