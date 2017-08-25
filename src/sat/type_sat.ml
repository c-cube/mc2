(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(* Log&Module Init *)
(* ************************************************************************ *)
open Minismt_core

module Id = Dolmen.Id
module Ast = Dolmen.Term
module H = Hashtbl.Make(Id)
module Formula = Tseitin.Make(Sat.Expr)

(* Exceptions *)
(* ************************************************************************ *)

exception Typing_error of string * Dolmen.Term.t

(* Identifiers *)
(* ************************************************************************ *)

let symbols = H.create 42

let find_id id =
  try
    H.find symbols id
  with Not_found ->
    let res = Sat.Expr.fresh () in
    H.add symbols id res;
    res

(* Actual parsing *)
(* ************************************************************************ *)

let rec parse = function
  | { Ast.term = Ast.Builtin Ast.True ;_} ->
    Formula.f_true
  | { Ast.term = Ast.Builtin Ast.False ;_} ->
    Formula.f_false
  | { Ast.term = Ast.Symbol id ;_} ->
    let s = find_id id in
    Formula.make_atom s
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Not ;_}, [p]) ;_}
  | { Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "not" ;_} ;_}, [p]) ;_} ->
    Formula.make_not (parse p)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.And ;_}, l) ;_}
  | { Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "and" ;_} ;_}, l) ;_} ->
    Formula.make_and (List.map parse l)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Or ;_}, l) ;_}
  | { Ast.term = Ast.App ({Ast.term = Ast.Symbol { Id.name = "or" ;_} ;_}, l) ;_} ->
    Formula.make_or (List.map parse l)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Imply ;_}, [p; q]) ;_} ->
    Formula.make_imply (parse p) (parse q)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Equiv ;_}, [p; q]) ;_} ->
    Formula.make_equiv (parse p) (parse q)
  | { Ast.term = Ast.App ({Ast.term = Ast.Builtin Ast.Xor ;_}, [p; q]) ;_} ->
    Formula.make_xor (parse p) (parse q)
  | t ->
    raise (Typing_error ("Term is not a pure proposition", t))

(* Exported functions *)
(* ************************************************************************ *)

let decl _ t =
  raise (Typing_error ("Declarations are not allowed in pure sat", t))

let def _ t =
  raise (Typing_error ("Definitions are not allowed in pure sat", t))

let assumptions t =
  let f = parse t in
  let cnf = Formula.make_cnf f in
  List.map (function
    | [ x ] -> x
    | _ -> assert false
  ) cnf

let antecedent t =
  let f = parse t in
  Formula.make_cnf f

let consequent t =
  let f = parse t in
  Formula.make_cnf @@ Formula.make_not f

