
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

val pp : t Fmt.printer


