
(** {1 A Few useful Keys for Services} *)

open Solver_types

let k_uf_const : (ID.t -> term) Service.Key.t = Service.Key.make "uf.const"
(** Service for turning a constant into a term *)

let k_uf_app : (ID.t -> term list -> term) Service.Key.t
  = Service.Key.make "uf.app"
(** Service for applying a constant to some arguments.
    Arguments are:
    - The head function symbol
    - the list of arguments
*)


let k_uf_decl : (ID.t -> Type.t list -> Type.t -> unit) Service.Key.t
  = Service.Key.make "uf.decl"
(** Service for declaring an uninterpreted symbol *)

