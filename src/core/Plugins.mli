
(** {1 Plugins DB} *)

(** Stores a set of plugins.
    Plugins are responsible for most of the reasoning in the solver:
    - theory reasoning
    - custom terms
    - instantiation
    - evaluation
    - …

    Each plugin has a unique ID that is allocated by the DB.
*)

type id = Term.plugin_id
(** Uniquely identifies a given plugin. Should be small. *)

type term = Term.t

type t
(** A collection of plugins, responsible for all the non-purely-boolean
    reasoning in the solver *)

val create : unit -> t
(** Create a plugin DB *)

(** Main interface for plugins. Each plugin must abide by this
    interface. *)
module type PLUGIN = sig
  val id : id

  val name : string
  (** Descriptive name *)

  val iter_terms : Term.t Sequence.t
  (** Iterate on all terms known to the plugin. Used for
      checking all variables to assign, and for
      garbage collection. *)

  val gc_mark_sub : (Term.t -> unit) -> Term.view -> unit
  (** [gc_mark_sub f t] should call [f] on every subterm of [t]
      to retain them during GC *)

  val pp_term : Term.t CCFormat.printer -> Term.view CCFormat.printer
  (** [pp_term pp_sub] is a term-view printer.
      It is only ever called with terms that belong to this plugin,
      and can use [pp_sub] to call sub-terms in a generic way. *)
end

type plugin = (module PLUGIN)

type plugin_mk = id -> plugin
(** Plugin builder *)

exception Plugin_not_found of id

val owns_term : plugin -> term -> bool
(** Does this plugin own this term? *)

val pp_term : t -> term CCFormat.printer
(** Print term using the plugins from this DB.
    @raise Plugin_not_found if a subterm belongs to an unknown plugin. *)

val iter_terms : t -> Term.t Sequence.t
(** Iterate on all terms known to plugins.
    Used for checking all variables to assign, and for garbage collection. *)

val gc_mark_sub : t -> (Term.t -> unit) -> Term.t -> unit
(** [gc_mark_sub f t] should call [f] on every subterm of [t]
    to retain them during GC *)

val add_plugin : t -> plugin_mk -> plugin
(** [add_plugin db f] allocates a new plugin, stores it into [db],
    and returns it.
    @raise Failure if all plugin IDs have been allocated
*)

