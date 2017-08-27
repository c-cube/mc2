
open Solver_types

type t = atom

(* TODO: migrate into term, with unsafe check that it's bool *)

(* Misc functions *)
let equal_atoms a b = St.(a.aid) = St.(b.aid)
let compare_atoms a b = Pervasives.compare St.(a.aid) St.(b.aid)

let seen a =
  let pos = (a == a.var.pa) in
  let seen_pos = Bool_var_fields.get field_seen_pos a.var.v_flags in
  let seen_neg = Bool_var_fields.get field_seen_neg a.var.v_flags in
  match seen_pos, seen_neg, pos with
    | false, false, _ -> false
    | true, true, _
    | true, _, true
    | false, _, false -> true
    | true, false, false
    | false, true, true -> false

let seen_both_atoms (v:bool_var) =
  let seen_pos = Bool_var_fields.get field_seen_pos v.v_flags in
  let seen_neg = Bool_var_fields.get field_seen_neg v.v_flags in
  seen_pos && seen_neg

let mark_atom a =
  let pos = (a == a.var.pa) in
  if pos then (
    a.var.v_flags <- Bool_var_fields.set field_seen_pos true a.var.v_flags
  ) else (
    a.var.v_flags <- Bool_var_fields.set field_seen_neg true a.var.v_flags
  )

let pp out a =
  Format.fprintf out "%s%d[%a][atom:@[<hov>%a@]]"
    (sign a) (a.var.vid+1) pp_value a E.Formula.print a.lit
