
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

open Mc2_core

type 'a or_error = ('a, string) CCResult.t

(** {2 Types} *)

exception Error of string
exception Ill_typed of string

module Var : sig
  type 'ty t = private {
    id: ID.t;
    ty: 'ty;
  }

  val make : ID.t -> 'ty -> 'ty t
  val copy : 'a t -> 'a t
  val id : _ t -> ID.t
  val ty : 'a t -> 'a

  val equal : 'a t -> 'a t -> bool
  val compare : 'a t -> 'a t -> int
  val pp : _ t CCFormat.printer
end

module Ty : sig
  type t =
    | Bool
    | Rat
    | Atomic of ID.t * t list
    | Arrow of t * t

  val bool : t
  val rat : t
  val const : ID.t -> t
  val arrow : t -> t -> t
  val arrow_l : t list -> t -> t

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int
  val pp : t CCFormat.printer

  val unfold : t -> t list * t
  (** [unfold ty] will get the list of arguments, and the return type
      of any function. An atomic type is just a function with no arguments *)

  (** {2 Datatypes} *)

  (** Mutually recursive datatypes *)
  type data = {
    data_id: ID.t;
    data_cstors: t ID.Map.t;
  }

  module Map : CCMap.S with type key = t

  (** {2 Error Handling} *)

  val ill_typed : ('a, Format.formatter, unit, 'b) format4 -> 'a
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

type term = private {
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

(* TODO: push/pop *)

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

(** {2 Constructors} *)

val term_view : term -> term_cell
val ty : term -> Ty.t

val var : var -> term
val const : ID.t -> Ty.t -> term
val app : term -> term list -> term
val app_a : term -> term array -> term
val select : select -> term -> Ty.t -> term
val if_ : term -> term -> term -> term
val match_ : term -> (var list * term) ID.Map.t -> term
val let_ : var -> term -> term -> term
val let_l : (var * term) list -> term -> term
val bind : ty:Ty.t -> binder -> var -> term -> term
val fun_ : var -> term -> term
val fun_l : var list -> term -> term
val fun_a : var array -> term -> term
val forall : var -> term -> term
val forall_l : var list -> term -> term
val exists : var -> term -> term
val exists_l : var list -> term -> term
val mu : var -> term -> term
val eq : term -> term -> term
val eq_l : term list -> term
val distinct : term list -> term
val not_ : term -> term
val and_ : term -> term -> term
val and_l : term list -> term
val or_ : term -> term -> term
val or_l : term list -> term
val imply : term -> term -> term
val imply_l : term list -> term
val true_ : term
val false_ : term
val num_z : Ty.t -> Z.t -> term
val num_q : Ty.t -> Q.t -> term
val num_str : Ty.t -> string -> term (** parses int + {!num} *)
val arith : Ty.t -> arith_op -> term list -> term

val unfold_fun : term -> var list * term

(** {2 Printing} *)

val pp_term : term CCFormat.printer
val pp_statement : statement CCFormat.printer

(** {2 Parsing and Typing} *)

module Ctx : sig
  type t
  val create: unit -> t
  val pp : t CCFormat.printer
end

val parse : string -> statement list or_error
(** Parse the given file, type-check, etc.
    @raise Error in case the input is ill formed
    @raise Ill_typed if the input is ill typed *)

val parse_stdin : unit -> statement list or_error
(** Parse stdin, type-check, etc.
    @raise Error in case the input is ill formed
    @raise Ill_typed if the input is ill typed *)
