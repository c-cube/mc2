(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

(** Deduki backend for proofs

    Work in progress...
*)
open Minismt_core

module type S = Backend_intf.S

module type Arg = sig

  type lemma
  type proof
  type formula

  val print : Format.formatter -> formula -> unit
  val prove : Format.formatter -> lemma -> unit
  val context : Format.formatter -> proof -> unit
end

module Make :
  functor(A : Arg
    with type formula := Term.t
     and type lemma := Clause.t
     and type proof := Res.proof) ->
    S with type t := Res.proof
(** Functor to generate a backend to output proofs for the dedukti type checker. *)
