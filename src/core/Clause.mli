
(** {1 Boolean Clauses} *)

open Solver_types

type t = clause

val dummy : t
(** Dummy values for use in vector dummys *)

val empty : t
(** The empty clause *)

val make : ?tag:int -> string -> atom list -> premise -> t
(** [make_clause name atoms size premise] creates a clause with the given attributes. *)

val make_arr : ?tag:int -> string -> atom array -> premise -> t
(** [make_clause name atoms size premise] creates a clause with the
    given attributes.
    Consumes the array. *)

val visited : t -> bool
val mark_visited : t -> unit
val clear_visited : t -> unit

val fresh_name : unit -> string
val fresh_lname : unit -> string
val fresh_tname : unit -> string
val fresh_hname : unit -> string
(** Fresh names for clauses *)

val pp : Format.formatter -> clause -> unit
(** Pretty printing functions for atoms and clauses *)

val debug : t CCFormat.printer

val pp_dimacs : t CCFormat.printer
