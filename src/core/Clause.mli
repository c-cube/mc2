
(** {1 Boolean Clauses} *)

open Solver_types

type t = clause

val make : ?tag:int -> atom list -> premise -> t
(** [make atoms premise] creates a clause with the given attributes. *)

val make_arr : ?tag:int -> atom array -> premise -> t
(** [make_arr atoms premise] creates a clause with the
    given attributes.
    Consumes the array. *)

val equal : t -> t -> bool
val hash : t -> int

val visited : t -> bool
val mark_visited : t -> unit
val clear_visited : t -> unit

val attached : t -> bool
val set_attached : t -> unit

val deleted : t -> bool
val set_deleted : t -> unit

val atoms : t -> atom array
val activity : t -> float
val name : t -> int
val premise : t -> premise
val get_tag : t -> int option (** Recover tag from a clause, if any *)

val gc_mark : t -> unit
val gc_unmark : t -> unit
val gc_marked : t -> bool

val pp_name : t CCFormat.printer
val pp : t CCFormat.printer (** nice printer *)
val debug : t CCFormat.printer (** very verbose printer *)

val pp_atoms : atom list CCFormat.printer
val debug_atoms : atom list CCFormat.printer
val debug_atoms_a : atom array CCFormat.printer

val pp_dimacs : t CCFormat.printer

module Tbl : CCHashtbl.S with type key = clause
