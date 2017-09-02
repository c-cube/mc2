(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(** Dot backend for proofs

    This module provides functions to export proofs into the dot graph format.
    Graphs in dot format can be used to generates images using the graphviz tool.
*)
open Mc2_core

module type S = Backend_intf.S
(** Interface for exporting proofs. *)

module type Arg = sig
  (** Term printing for DOT

      This module defines what functions are required in order to export
      a proof to the DOT format.
  *)

  type atom
  (** The type of atomic formuals *)

  type hyp
  type lemma
  type assumption
  (** The type of theory-specifi proofs (also called lemmas). *)

  val print_atom : Format.formatter -> atom -> unit
  (** Print the contents of the given atomic formulas.
      WARNING: this function should take care to escape and/or not output special
      reserved characters for the dot format (such as quotes and so on). *)

  val hyp_info : hyp -> string * string option * (Format.formatter -> unit -> unit) list
  val lemma_info : lemma -> string * string option * (Format.formatter -> unit -> unit) list
  val assumption_info : assumption -> string * string option * (Format.formatter -> unit -> unit) list
  (** Generate some information about the leafs of the proof tree. Currently this backend
      print each lemma/assumption/hypothesis as a single leaf of the proof tree.
      These function should return a triplet [(rule, color, l)], such that:
      - [rule] is a name for the proof (arbitrary, does not need to be unique, but
        should rather be descriptive)
      - [color] is a color name (optional) understood by DOT
      - [l] is a list of printers that will be called to print some additional information
  *)

end

module Default : Arg with type atom := Atom.t
                                 and type hyp := Clause.t
                                 and type lemma := Clause.t
                                 and type assumption := Clause.t
(** Provides a reasonnable default to instantiate the [Make] functor, assuming
    the original printing functions are compatible with DOT html labels. *)

module Make(A : Arg with type atom := Atom.t
                                and type hyp := Clause.t
                                and type lemma := Clause.t
                                and type assumption := Clause.t) : S with type t := Res.proof
(** Functor for making a module to export proofs to the DOT format. *)
