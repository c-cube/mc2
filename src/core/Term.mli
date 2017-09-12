
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
val var : t -> var
val ty : t -> Type.t
val reason : t -> reason option
val reason_exn : t -> reason
val eval_bool : t -> eval_bool_res
val is_bool : t -> bool

val level_semantic : t -> level
(** maximum level of subterms, or -1 if some subterm is not assigned *)

val max_level : level -> level -> level
(** maximum of the levels, or -1 if either is -1 *)

val iter_subterms : t -> t Sequence.t
(** Iteration over subterms.
    When incrementing activity, adding new terms, etc.
    we want to be able to iterate over all subterms of a formula.  *)

val subterms : t -> t list

val recompute_state : level -> t -> unit
(** Recompute internal {!decide_state}, assuming the set of unit
    constraints changed (typically, after some backtracking) *)

val weight : t -> float (** Heuristic weight *)
val set_weight : t -> float -> unit

val has_value : t -> bool
val value : t -> term_assignment
val value_exn : t -> value

val mk_eq : t -> t -> t
(** Use the term's type to make two terms equal *)

val gc_unmark : t -> unit (** Unmark just this term *)
val gc_marked : t -> bool
val gc_mark_rec : t -> unit (** Mark term and its subterms, recursively *)

val dirty : t -> bool
val dirty_mark : t -> unit
val dirty_unmark : t -> unit

val field_get : Term_fields.field -> t -> bool
val field_set : Term_fields.field -> t -> unit
val field_clear : Term_fields.field -> t -> unit

val has_var : t -> bool (** is there a variable for the term? *)
val setup_var : t -> unit (** create a variable for the term *)

val add_watch : t -> t -> unit
(** [add_watch t u] adds [u] to the list of watches of [t]. [u] will be
    notified whenever [t] is assigned *)

(** Make a new typeclass *)
val tc_mk :
  ?init:(actions -> term -> unit) ->
  ?update_watches:(actions -> term -> watch:term -> watch_res) ->
  ?delete:(term -> unit) ->
  ?subterms:( term_view -> (term->unit) -> unit) ->
  ?eval_bool :( term -> eval_bool_res) ->
  pp:term_view CCFormat.printer ->
  unit ->
  tc

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

(** {2 1-term Watch Scheme} *)

module Watch1 : sig
  type t

  val dummy : t
  val make : term list -> t
  val make_a : term array -> t (** owns the array *)
  val iter : t -> term Sequence.t (** current watch(es) *)

  val init :
    t ->
    term ->
    on_all_set:(unit -> unit) ->
    unit
  (** [init w t ~on_all_set] initializes [w] (the watchlist) for
      term [t], by finding an unassigned term in the watchlist and
      registering [t] to it.
      If all terms are set, then it watches the one with the highest level
      and call [on_all_set ()]
  *)

  val update :
    t ->
    term ->
    watch:term ->
    on_all_set:(unit -> unit) ->
    watch_res
  (** [update w t ~watch ~on_all_set] updates [w] after [watch]
      has been assigned. It looks for another term in [w] for [t] to watch.
      If all terms are set, then it calls [on_all_set ()]
  *)
end

(** {2 2-terms Watch Scheme} *)

module Watch2 : sig
  type t

  val dummy : t
  val make : term list -> t
  val make_a : term array -> t (** owns the array *)
  val iter : t -> term Sequence.t (** current watch(es) *)

  val init :
    t ->
    term ->
    on_unit:(term -> unit) ->
    on_all_set:(unit -> unit) ->
    unit
  (** [init w t ~on_all_set] initializes [w] (the watchlist) for
      term [t], by finding an unassigned term in the watchlist and
      registering [t] to it.
      If exactly one term [u] is not set, then it calls [on_unit u].
      If all terms are set, then it watches the one with the highest level
      and call [on_all_set ()]
  *)

  val update :
    t ->
    term ->
    watch:term ->
    on_unit:(term -> unit) ->
    on_all_set:(unit -> unit) ->
    watch_res
  (** [update w t ~watch ~on_all_set] updates [w] after [watch]
      has been assigned. It looks for another term in [w] for [t] to watch.
      If exactly one term [u] is not set, then it calls [on_unit u].
      If all terms are set, then it calls [on_all_set ()]
  *)
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

(** {2 Hashconsing of terms belonging to a Plugin} *)

module type TERM_ALLOC_OPS = sig
  val p_id : plugin_id (** ID of the theory *)
  val initial_size: int (** initial size of table *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
end

module Term_allocator(T : TERM_ALLOC_OPS) : sig
  val make : view -> Type.t -> tc_term -> t (** Make a term of the theory *)
  val delete : t -> unit (** Delete a term of the theory *)
  val iter_terms : term Sequence.t (** All terms *)
  val gc_all : unit -> unit (** GC all unmarked tems; unmark alive terms *)
end

