
(** {1 Modular Term Structure} *)

open Solver_types

type view = term_view = ..
type t = term
type tc = tc_term

(** {2 Basics} *)

val id : t -> int (** Globally unique ID of this term *)
val view : t -> view
val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val pp : t CCFormat.printer
val debug : t CCFormat.printer
val debug_no_val : t CCFormat.printer (** like {!debug} but does not print val *)

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
val is_added : t -> bool
val level : t -> level (** decision/assignment level of the term *)
val level_for : t -> value -> level (** level for evaluating into this value *)
val var : t -> var
val ty : t -> Type.t
val reason : t -> reason option
val reason_exn : t -> reason
val eval : t -> eval_res
val is_bool : t -> bool

val level_semantic : t -> level
(** maximum level of subterms, or -1 if some subterm is not assigned *)

val level_sub : t -> level
(** maximum level of subterms, ignoring unassigned subterms *)

val max_level : level -> level -> level
(** maximum of the levels, or [-1] if either is [-1] *)

val iter_subterms : t -> t Iter.t
(** Iteration over subterms.
    When incrementing activity, adding new terms, etc.
    we want to be able to iterate over all subterms of a formula.  *)

val subterms : t -> t list

val decide_state_exn : t -> decide_state
(** Obtain decide state, or raises if the variable is not semantic *)

val weight : t -> float (** Heuristic weight *)
val set_weight : t -> float -> unit

val has_some_value : t -> bool
val has_value : t -> value -> bool
val value : t -> value option
val value_exn : t -> value

val mk_eq : t -> t -> t
(** Use the term's type to make two terms equal *)

val gc_unmark : t -> unit (** Unmark just this term *)
val gc_marked : t -> bool
val gc_mark : t -> unit (** Non recursive *)

val field_get : Term_fields.field -> t -> bool
val field_set : Term_fields.field -> t -> unit
val field_clear : Term_fields.field -> t -> unit

val has_var : t -> bool (** is there a variable for the term? *)
val setup_var : t -> unit (** create a variable for the term *)

val add_watch : t -> watcher:watcher -> unit
(** [add_watch t ~watcher:w] adds [w] to the list of watches of [t].
    [w] will be called whenever [t] is assigned *)

val add_watch_permanent : t -> watcher:(actions -> t -> unit) -> unit

val notify_watchers : t -> actions -> unit

(** {2 Bool terms} *)

module Bool : sig
  type t = bool_term

  val both_atoms_marked : t -> bool (** Did we see both polarities of this var in the same clause? *)
  val assigned_atom : t -> atom option (** if assigned and bool, return corresponding atom *)
  val assigned_atom_exn : t -> atom

  val pa_unsafe : t -> atom (** Positive atom (assumes [has_var t]) *)
  val na_unsafe : t -> atom (** Negative atom (assumes [has_var t]) *)

  val pa : t -> atom (** safe version of {!pa_unsafe}, call [setup_var] *)
  val na : t -> atom (** safe version of {!na_unsafe}, call [setup_var] *)

  val mk_eq : term -> term -> atom
  val mk_neq : term -> term -> atom

  val is_true : t -> bool
  val is_false : t -> bool
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

  val make_term : int -> term_view -> Type.t -> tc_term -> term
  (** Build a term. Careful with IDs! *)
end
(**/**)

(** {2 Typeclass} *)
module TC : sig
  type t = tc

  (** Make a new typeclass, directly *)
  val make :
    ?init:(actions -> term -> unit) ->
    ?delete:(term -> unit) ->
    ?subterms:(term_view -> (term->unit) -> unit) ->
    ?eval:(term -> eval_res) ->
    pp:term_view CCFormat.printer ->
    unit ->
    t

  (** Lazy builder *)

  type lazy_tc

  val lazy_from_val : t -> lazy_tc

  val lazy_make : unit -> lazy_tc
  (** Make a new typeclass, without providing the actual functions *)

  val lazy_get : lazy_tc -> tc
  (** Obtain the underlying typeclass;
      call only after {!lazy_complete} *)

  val lazy_complete :
    ?init:(actions -> term -> unit) ->
    ?delete:(term -> unit) ->
    ?subterms:(term_view -> (term->unit) -> unit) ->
    ?eval:(term -> eval_res) ->
    pp:term_view CCFormat.printer ->
    lazy_tc ->
    unit
    (** Now provide functions for this TC.
        @raise Failure if the TC is already defined *)
end

(** {2 Hashconsing of terms belonging to a Plugin} *)

module type TERM_ALLOC_OPS = sig
  val p_id : plugin_id (** ID of the theory *)
  val initial_size: int (** initial size of table *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
  val tc : TC.lazy_tc (** Typeclass for terms *)
end

module type TERM_ALLOC = sig
  val make : view -> Type.t -> t (** Make a term of the theory *)
  val delete : t -> unit (** Delete a term of the theory *)
  val iter_terms : term Iter.t (** All terms *)
  val gc_all : unit -> int (** GC all unmarked tems; unmark alive terms *)
end

module Term_allocator(T : TERM_ALLOC_OPS) : TERM_ALLOC

(** {2 Containers} *)

module Tbl : CCHashtbl.S with type key = term
module Map : CCMap.S with type key = term
module Set : CCSet.S with type elt = term

