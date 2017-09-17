
(** {1 Services} *)

(** A service is a feature provided by a plugin. A typical service
    would be a function to build terms, or to traverse all sub-terms,
    or to perform E-matching, etc.

    A registry is used to list all services provided by plugins and make
    them available to users of the library, or to other plugins.
*)

(** The way to access a service registered by some plugin *)
module Key : sig
  type 'a t (** Key for values of type ['a lazy_t] *)

  val make : string -> 'a t (** Make a key with given name *)
  val makef : ('a, Format.formatter, unit, 'b t) format4 -> 'a (** Fmt version of {!make} *)
  val name : _ t -> string (** Name of the key *)
end

type any = Any : 'a Key.t * 'a -> any
(** Existential wrapper around a service *)

module Registry : sig
  type t

  val create: unit -> t
  (** Create a registry *)

  val register : t -> 'a Key.t -> 'a -> unit
  (** Register a service *)

  val find : t -> 'a Key.t -> 'a option
  (** Find a service by its key *)

  val find_exn : t -> 'a Key.t -> 'a
  (** Find a service by its key
      @raise Util.Error if the key is not found *)

  val to_seq : t -> any Sequence.t
  (** all registered services *)
end
