(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

module Loc = Smtlib_utils.V_2_6.Loc
module PA = Smtlib_utils.V_2_6.Ast
module T = Mc2_core.Term
module Stmt = Mc2_core.Statement

type 'a or_error = ('a, string) CCResult.t

(** {2 Typing} *)

module Make(ARG : sig
    val solver : Mc2_core.Solver.t
  end) : sig

  val conv_term : PA.term -> T.t

  val conv_bool_term : PA.term -> Mc2_core.Atom.t list list

  val conv_statement : PA.statement -> Stmt.t list
end

