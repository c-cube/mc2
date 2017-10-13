
(** {1 Trivial plugin for SAT} *)

open Mc2_core
open Solver_types

let name = "sat"
let k_atom = Service.Key.make "sat.atom"

type term_view += Atom of int

let tc_term =
  let pp out = function
    | Atom i -> Format.fprintf out "P%d" i
    | _ -> assert false
  in
  Term.TC.make ~pp ()

let build p_id Plugin.S_nil : Plugin.t =
  let module T = Term.Term_allocator(struct
      let tc = Term.TC.lazy_from_val tc_term
      let p_id = p_id
      let initial_size = 64
      let equal a b = match a, b with
        | Atom i, Atom j -> i=j
        | _ -> false
      let hash = function Atom i -> CCHash.int i | _ -> assert false
    end) in
  let module P = struct
    let id = p_id
    let name = name
    let mk_atom i : atom =
      let sign = i>0 in
      let t = T.make (Atom (abs i)) Type.bool in
      if sign then Term.Bool.pa t else Term.Bool.na t

    let provided_services =
      [ Service.Any (k_atom, mk_atom);
      ]
    let check_if_sat _ = Sat
    let iter_terms = T.iter_terms
    let gc_all = T.gc_all
  end in
  (module P)

let plugin = Plugin.Factory.make ~requires:Plugin.K_nil ~name ~build ()

