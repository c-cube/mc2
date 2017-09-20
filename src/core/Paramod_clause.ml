
(** {1 Paramodulation Clause} *)

open Solver_types

type t = paramod_clause

let[@inline] make pc_lhs pc_rhs pc_guard pc_premise : t =
  { pc_guard; pc_lhs; pc_rhs; pc_premise; }

let[@inline] lhs c = c.pc_lhs
let[@inline] rhs c = c.pc_rhs
let[@inline] guard c = c.pc_guard
let[@inline] premise c = c.pc_premise

let to_clause (c:t) : clause =
  let atoms = Term.Bool.mk_eq (lhs c) (rhs c) :: List.map Atom.neg (guard c) in
  Clause.make atoms (premise c)

let pp out (c:t) : unit =
  Fmt.fprintf out "(@[<hv>@[%a@ := %a@]@ <= %a@])"
    Term.pp (lhs c) Term.pp (rhs c) (Util.pp_list Atom.pp) (guard c)

let debug out (c:t) : unit =
  Fmt.fprintf out "(@[<hv>@[%a@ := %a@]@ :guard %a@ :premise %a@])"
    Term.debug (lhs c) Term.debug (rhs c)
    (Util.pp_list Atom.debug) (guard c)
    Premise.pp (premise c)
