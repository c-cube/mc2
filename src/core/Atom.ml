
open Solver_types

type t = atom

let[@inline] equal a b = a.a_id = b.a_id
let[@inline] compare a b = CCInt.compare a.a_id b.a_id

(* negation of the atom *)
let[@inline] is_pos (a:t) : bool = match a.a_term.t_var with
  | V_bool { pa; _ } -> a==pa
  | V_none | V_semantic _ -> assert false

(* negation of the atom *)
let[@inline] neg (a:t) : t = match a.a_term.t_var with
  | V_bool { pa; na } -> if a==pa then na else pa
  | V_none | V_semantic _ -> assert false

let[@inline] is_true (a:t): bool = a.a_is_true
let[@inline] is_false (a:t): bool = is_true (neg a)
let[@inline] is_undef (a:t): bool = not (is_true a) && not (is_false a)
let[@inline] term (a:t) = a.a_term
let[@inline] level (a:t) = a.a_term.t_level
let[@inline] reason (a:t) = a.a_term.t_reason
let[@inline] watched (a:t) = a.a_watched

let mark (a:t) =
  if is_pos a then (
    a.a_term.t_fields <- Term_fields.set field_t_mark_pos true a.a_term.t_fields
  ) else (
    a.a_term.t_fields <- Term_fields.set field_t_mark_neg true a.a_term.t_fields
  )

let unmark (a:t) =
  if is_pos a then (
    a.a_term.t_fields <- Term_fields.set field_t_mark_pos false a.a_term.t_fields
  ) else (
    a.a_term.t_fields <- Term_fields.set field_t_mark_neg false a.a_term.t_fields
  )

let marked (a:t) : bool =
  if is_pos a then (
    Term_fields.get field_t_mark_pos a.a_term.t_fields
  ) else (
    Term_fields.get field_t_mark_neg a.a_term.t_fields
  )

let pp_level fmt t = Reason.pp fmt (t.t_level, t.t_reason)

let pp_value fmt a =
  if is_true a then
    Format.fprintf fmt "T%a" pp_level (term a)
  else if is_true (neg a) then
    Format.fprintf fmt "F%a" pp_level (term a)
  else
    Format.fprintf fmt ""

let pp pp_term out a =
  let sign = if is_pos a then "+" else "-" in
  Format.fprintf out "%s%d[%a][atom:@[<hov>%a@]]"
    sign (a.a_term.t_id+1) pp_value a pp_term a.a_term
