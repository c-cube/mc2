
open Solver_types

type trace = paramod_trace
type step = paramod_step
type pclause = paramod_clause

module Step : sig
  type t = step

  val paramod : pclause -> t
  val subs : trace list -> t

  val pp : t Fmt.printer
end

module Trace : sig
  type t = trace

  val equal : t -> t -> bool
  val compare : t -> t -> int
  val hash : t -> int

  val pc_seq : t -> pclause Sequence.t
  (** Iterate on clauses used for atomic steps *)

  val clauses : t -> Clause.Set.t
  (** Set of clauses in a given trace *)

  val make : term -> term -> step list -> t
  (** [make lhs rhs steps] details how to rewrite [lhs] into [rhs]
      using the [steps]. *)

  val pp : t Fmt.printer

  module Tbl : CCHashtbl.S with type key = t
end

module PClause : sig
  type t = pclause

  val make : term -> term -> atom list -> premise -> t

  val lhs : t -> term
  val rhs : t -> term
  val guard : t -> atom list
  val premise : t -> premise

  val to_clause : t -> clause
  (** Turn the pclause to a clause. *)

  val pp : t Fmt.printer
  val debug : t Fmt.printer
end
