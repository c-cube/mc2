(**************************************************************************)
(*                                                                        *)
(*                                  Cubicle                               *)
(*             Combining model checking algorithms and SMT solvers        *)
(*                                                                        *)
(*                  Sylvain Conchon, Evelyne Contejean                    *)
(*                  Francois Bobot, Mohamed Iguernelala, Alain Mebsout    *)
(*                  CNRS, Universite Paris-Sud 11                         *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)
(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2016 Guillaume Bury
Copyright 2016 Simon Cruanes
*)

(** McSat Theory

    This module defines what a theory must implement in order to
    be used in a MCSat solver.
*)

open Solver_types

type proof = Res.proof

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

  val gc_all : unit -> unit
  (** Garbage collect all unmarked terms *)
end

type t = (module S)

let[@inline] owns_term (module P : S) (t:term) : bool = Term.plugin_id t = P.id
let[@inline] name (module P : S) = P.name

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
end = struct
  type plugin = t

  type t = Factory : {
      name: string;
      priority: int;
      requires: 'a service_key_list;
      build: plugin_id -> 'a service_list -> plugin
    } -> t

  let compare (a:t)(b:t) =
    let Factory {priority=p_a; _} = a in
    let Factory {priority=p_b; _} = b in
    CCInt.compare p_a p_b

  let make ?(priority=50) ~name ~requires ~build () =
    Factory { priority; name; requires; build; }
end
