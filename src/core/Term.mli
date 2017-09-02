
(** {1 Modular Term Structure} *)

open Solver_types

type view = term_view = ..
type t = term

(** {2 Basics} *)

val id : t -> int (** Globally unique ID of this term *)
val view : t -> view
val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val pp : t CCFormat.printer

(** {2 ID Management} *)

val plugin_id_width : int
(** Number of bits dedicated to plugin IDs.
    There can be at most [2 ** plugin_id_width] plugins in a solver. *)

val plugin_id : t -> plugin_id (** Which plugin owns this term? *)
val plugin_specific_id : t -> int (** ID of the term for the plugin itself *)

val mark : t -> unit (** Mark the variable *)
val unmark : t -> unit (** Clear the fields of the variable. *)
val marked : t -> bool (** Was {!mark} called on this var? *)

val is_deleted : t -> bool
val level : t -> int
val reason : t -> reason option

val weight : t -> float (** Heuristic weight *)
val set_weight : t -> float -> unit

val field_get : Term_fields.field -> t -> bool
val field_set : Term_fields.field -> t -> unit
val field_clear : Term_fields.field -> t -> unit

val has_var : t -> bool (** is there a variable for the term? *)
val setup_var : t -> unit (** create a variable for the term *)

(** {2 Bool terms} *)

(* TODO: how to do negation, exactly? *)
module Bool : sig
  type t = bool_term

  val both_atoms_marked : t -> bool (** Did we see both polarities of this var in the same clause? *)
  val assigned_atom : t -> atom option (** if assigned and bool, return corresponding atom *)
  val assigned_atom_exn : t -> atom

  val pa : t -> atom
  val na : t -> atom
end

(** {2 Assignment view} *)

val assigned : t -> bool
val assignment : t -> assignment_view option (** Current assignment of this term *)

(** {2 Low Level constructors. Use at your own risks.} *)
(**/**)
module Unsafe : sig
  val max_plugin_id: int

  val mk_plugin_id : int -> plugin_id
  (** Convert an int into a plugin ID.
      Should only be used in {!Plugin_db}. *)
end
(**/**)

(** {2 Hashconsing of terms belonging to a Plugin} *)

module type TERM_ALLOC_OPS = sig
  val p_id : plugin_id (** ID of the theory *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
end

module Term_allocator(T : TERM_ALLOC_OPS) : sig
  val make : view -> Type.t -> tc_term -> t
  (** Make a term of the theory *)

  val delete : t -> unit
  (** Delete a term of the theory *)
end

