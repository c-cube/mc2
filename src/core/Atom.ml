
open Solver_types

type t = atom

let[@inline] equal a b = a.a_id = b.a_id
let[@inline] compare a b = CCInt.compare a.a_id b.a_id

(* negation of the atom *)
let[@inline] is_pos (a:t) : bool = match a.a_term.t_var with
  | Var_bool { pa; _ } -> a==pa
  | Var_none | Var_semantic _ -> assert false

(* negation of the atom *)
let[@inline] neg (a:t) : t = match a.a_term.t_var with
  | Var_bool { pa; na; _ } -> if a==pa then na else pa
  | Var_none | Var_semantic _ -> assert false

let[@inline] abs (a:t) : t = match a.a_term.t_var with
  | Var_bool { pa; _ } -> pa
  | Var_none | Var_semantic _ -> assert false

let[@inline] value (a:t) : bool_assignment = match a.a_term.t_var with
  | Var_bool {b_value;_} -> b_value
  | _ -> assert false

let[@inline] is_true (a:t): bool = match a.a_term.t_var with
  | Var_bool {b_value=B_true _;pa;_} when a==pa -> true
  | Var_bool {b_value=B_false _;na;_} when a==na -> true
  | _ -> false

let[@inline] is_false (a:t): bool = match a.a_term.t_var with
  | Var_bool {b_value=B_true _;na;_} when a==na -> true
  | Var_bool {b_value=B_false _;pa;_} when a==pa -> true
  | _ -> false

let[@inline] is_undef (a:t): bool = match value a with
  | B_none -> true
  | _ -> false

let[@inline] reason (a:t) = match a.a_term.t_var with
  | Var_bool {b_value=(B_true r|B_false r); _} -> Some r
  | _ -> None

let[@inline] term (a:t) = a.a_term
let[@inline] level (a:t) = a.a_term.t_level
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

let pp_level fmt a = Reason.pp fmt (a.a_term.t_level, reason a)

let pp_value fmt a =
  if is_true a then
    Format.fprintf fmt "T%a" pp_level a
  else if is_true (neg a) then
    Format.fprintf fmt "F%a" pp_level a
  else
    Format.fprintf fmt ""

let pp out a =
  let sign = if is_pos a then "+" else "-" in
  Format.fprintf out "%s%d[%a][atom:@[<hov>%a@]]"
    sign (a.a_term.t_id+1) pp_value a Term.pp a.a_term
