
(** {1 Modular Term Structure} *)

module Fields = Solver_types.Term_fields

type view = Solver_types.term_view
type plugin_id = Solver_types.plugin_id (** Unique ID of a plugin *)
type atom = Solver_types.atom
type t = Solver_types.term

(** {2 Basics} *)

val id : t -> int
(** Globally unique ID of this term *)

val view : t -> view

val equal : t -> t -> bool

val compare : t -> t -> int

val hash : t -> int

(** {2 ID Management} *)

val plugin_id_width : int
(** Number of bits dedicated to plugin IDs.
    There can be at most [2 ** plugin_id_width] plugins in a solver. *)

val plugin_id : t -> plugin_id
(** Which plugin owns this term? *)

val plugin_specific_id : t -> int
(** ID of the term for the plugin itself *)

(** {2 Low Level constructors. Use at your own risks.} *)
(**/**)
module Unsafe : sig
  val max_plugin_id: int

  val mk_plugin_id : int -> plugin_id
  (** Convert an int into a plugin ID.
      Should only be used in {!Plugin_db}. *)
end

val dummy : t
(** Dummy term. Do not use it in any function, just for initializing
    vectors. *)
(**/**)

(** {2 Hashconsing of terms belonging to a Plugin} *)

module type TERM_ALLOC_OPS = sig
  val p_id : plugin_id (** ID of the theory *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
end

module Term_allocator(T : TERM_ALLOC_OPS) : sig
  val make : view -> Type.t -> t
  (** Make a term of the theory *)

  val delete : t -> unit
  (** Delete a term of the theory *)
end

(* TODO: add a submodule for boolean terms (with their vars) *)
(* TODO: add this properly *)

val seen_both_atoms : t -> bool
(** Did we see both polarities of this var in the same clause? *)

val mark : t -> unit
(** Mark the variable *)

val seen: t -> bool
(** Was {!mark_var} called on this var? *)

val clear : t -> unit
(** Clear the fields of the variable. *)


val weight : t -> float
(** Heuristic weight *)
