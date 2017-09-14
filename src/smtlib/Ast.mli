
(* This file is free software. See file "license" for more details. *)

(** {1 Preprocessing AST} *)

open Mc2_core

type loc = Locations.t

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
    | Prop
    | Atomic of ID.t * t list
    | Arrow of t * t

  val prop : t
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

type ty = Ty.t
type var = Ty.t Var.t

type op =
  | And
  | Or
  | Imply
  | Eq
  | Distinct

type binder =
  | Fun
  | Forall
  | Exists
  | Mu

type term = private {
  term: term_cell;
  ty: Ty.t;
  loc: loc option;
}
and term_cell =
  | Var of var
  | Const of ID.t
  | App of term * term list
  | If of term * term * term
  | Select of select * term
  | Match of term * (var list * term) ID.Map.t
  | Bind of binder * var * term
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

type statement = {
  stmt_view: statement_view;
  stmt_loc: loc option;
}
and statement_view =
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

val term_view : term -> term_cell
val ty : term -> Ty.t
val loc : term -> loc option

val stmt_view : statement -> statement_view
val stmt_loc : statement -> loc option

(** {2 Context for Parsing and Typing} *)

module Ctx : sig
  type t
  val create: unit -> t
  val pp : t CCFormat.printer
end

(** {2 Constructors} *)

val var : ?loc:loc -> var -> term
val const : ?loc:loc -> ID.t -> Ty.t -> term
val app : ?loc:loc -> term -> term list -> term
val app_a : ?loc:loc -> term -> term array -> term
val select : ?loc:loc -> select -> term -> Ty.t -> term
val if_ : ?loc:loc -> term -> term -> term -> term
val match_ : ?loc:loc -> term -> (var list * term) ID.Map.t -> term
val let_ : ?loc:loc -> var -> term -> term -> term
val let_l : ?loc:loc -> (var * term) list -> term -> term
val bind : ?loc:loc -> ty:Ty.t -> binder -> var -> term -> term
val fun_ : ?loc:loc -> var -> term -> term
val fun_l : ?loc:loc -> var list -> term -> term
val fun_a : ?loc:loc -> var array -> term -> term
val forall : ?loc:loc -> var -> term -> term
val forall_l : ?loc:loc -> var list -> term -> term
val exists : ?loc:loc -> var -> term -> term
val exists_l : ?loc:loc -> var list -> term -> term
val mu : ?loc:loc -> var -> term -> term
val eq : ?loc:loc -> term -> term -> term
val eq_l : ?loc:loc -> term list -> term
val distinct : ?loc:loc -> term list -> term
val not_ : ?loc:loc -> term -> term
val and_ : ?loc:loc -> term -> term -> term
val and_l : ?loc:loc -> term list -> term
val or_ : ?loc:loc -> term -> term -> term
val or_l : ?loc:loc -> term list -> term
val imply : ?loc:loc -> term -> term -> term
val imply_l : ?loc:loc -> term list -> term
val true_ : term
val false_ : term

val unfold_fun : term -> var list * term

(** {2 Printing} *)

val pp_term : term CCFormat.printer
val pp_statement : statement CCFormat.printer
