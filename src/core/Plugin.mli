
(** {1 Plugins} *)

(** The operations for a solver plugin. A plugin can contribute types,
    terms, or other ways of implementing a theory. *)

open Solver_types

(** Heterogeneous tuple of services *)
type _ service_list =
  | S_nil : unit service_list
  | S_cons : 'a Service.Key.t * 'a * 'b service_list -> ('a * 'b) service_list

(** Heterogeneous tuple of keys *)
type _ service_key_list =
  | K_nil : unit service_key_list
  | K_cons : 'a Service.Key.t * 'b service_key_list -> ('a * 'b) service_key_list

(** Main interface for plugins. Each plugin must abide by this
    interface. *)
module type S = sig
  val id : plugin_id

  val name : string
  (** Descriptive name *)

  val provided_services : Service.any list
  (** List of provided services, to be registered for other plugins
      to use *)

  val check_if_sat : actions -> check_res
  (** Last call before answering "sat". If the current trail is not
      theory-satisfiable, the plugin {b MUST} give a conflict here. *)

  val iter_terms : term Sequence.t
  (** Iterate on all terms known to the plugin. Used for
      checking all variables to assign, and for
      garbage collection. *)

  val gc_all : unit -> int
  (** Garbage collect all unmarked terms
      @returns the number of collected (deleted) terms  *)
end

type t = (module S)

val owns_term : t -> term -> bool
val name : t -> string

(** {2 Factory} *)

module Factory : sig
  type plugin = t

  type t = Factory : {
      name: string;
      priority: int;
      (** how prioritary this plugin is. The lower, the earlier this plugin
          is loaded.
          {b NOTE}: if plugin [b] requires services provided by plugin [a],
            then we need to ensure [a.priority < b.priority] *)
      requires: 'a service_key_list;
      (** list of required services *)
      build: plugin_id -> 'a service_list -> plugin
      (** builder, taking:
          - the unique ID of the plugin
          - the list of services required by [requires]
      *)
    } -> t
  (** A plugin factory, i.e. the method to build a plugin with a given ID. *)

  val compare : t -> t -> int

  val make :
    ?priority:int ->
    name:string ->
    requires:'a service_key_list ->
    build:(plugin_id -> 'a service_list -> plugin) ->
    unit ->
    t
end
