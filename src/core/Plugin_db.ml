
(** {1 Plugins DB} *)

type term = Term.t

type id = Term.plugin_id
(** Uniquely identifies a given plugin. Should be small. *)

(** Main interface for plugins. Each plugin must abide by this
    interface. *)
module type PLUGIN = sig
  val id : id

  val name : string
  (** Descriptive name *)

  val gc_mark_sub : (Term.t -> unit) -> Term.view -> unit
  (** [gc_mark_sub f t] should call [f] on every subterm of [t]
      to retain them during GC *)

  val gc_iter_terms : Term.t Sequence.t
  (** Iterate on all terms known to the plugin. Used for
      garbage collection. *)

  val pp_term : Term.t CCFormat.printer -> Term.view CCFormat.printer
  (** [pp_term pp_sub] is a term-view printer.
      It is only ever called with terms that belong to this plugin,
      and can use [pp_sub] to call sub-terms in a generic way. *)
end

type plugin = (module PLUGIN)

type plugin_mk = id -> plugin

exception Plugin_not_found of id

type t = {
  plugins: plugin CCVector.vector;
  (* the set of plugins *)
}


let[@inline] owns_term (module P : PLUGIN) (t:term) : bool =
  Term.plugin_id t = P.id

let add_plugin (db:t) (f:plugin_mk) : plugin =
  let id = CCVector.length db.plugins |> Term.Unsafe.mk_plugin_id in
  let p = f id in
  CCVector.push db.plugins p;
  p

let pp_term (db:t) out (t:term): unit =
  let rec aux out t =
    let id = Term.plugin_id t in
    if (id:>int) >= CCVector.length db.plugins then (
      raise (Plugin_not_found id);
    );
    let (module P) = CCVector.get db.plugins (id:>int) in
    P.pp_term aux out (Term.view t)
  in
  aux out t

let create() : t = {
  plugins=CCVector.create();
}
