
open Solver_types

type t = atom

let[@inline] equal a b = a.a_id = b.a_id
let[@inline] compare a b = CCInt.compare a.a_id b.a_id
let[@inline] hash a = CCHash.int a.a_id

let[@inline] same_term a b = a.a_term == b.a_term

let[@inline] is_pos (a:t) : bool = match a.a_term.t_var with
  | Var_bool { pa; _ } -> a==pa
  | Var_none | Var_semantic _ -> assert false

let[@inline] is_neg (a:t) : bool = not (is_pos a)

(* negation of the atom *)
let[@inline] neg (a:t) : t = match a.a_term.t_var with
  | Var_bool { pa; na; _ } -> if a==pa then na else pa
  | Var_none | Var_semantic _ -> assert false

let[@inline] abs (a:t) : t = match a.a_term.t_var with
  | Var_bool { pa; _ } -> pa
  | Var_none | Var_semantic _ -> assert false

let[@inline] value (a:t): value option =
  if is_pos a then Term.value a.a_term
  else CCOpt.map Value.bool_neg (Term.value a.a_term)

let[@inline] is_true (a:t): bool =
  if is_pos a
  then Term.has_value a.a_term Value.true_
  else Term.has_value a.a_term Value.false_
let[@inline] is_false (a:t): bool =
  if is_pos a
  then Term.has_value a.a_term Value.false_
  else Term.has_value a.a_term Value.true_
let[@inline] has_some_value (a:t): bool = Term.has_some_value a.a_term
let[@inline] is_undef (a:t): bool = not (has_some_value a)

let[@inline] reason (a:t) : reason option = Term.reason a.a_term

let[@inline] term (a:t) = a.a_term
let[@inline] level (a:t) = Term.level a.a_term
let[@inline] watched (a:t) = a.a_watched

let[@inline] field_ (a:t) : Term_fields.field =
  if is_pos a then field_t_mark_pos else field_t_mark_neg

let[@inline] mark (a:t) =
  a.a_term.t_fields <- Term_fields.set (field_ a) true a.a_term.t_fields

let[@inline] unmark (a:t) =
  a.a_term.t_fields <- Term_fields.set (field_ a) false a.a_term.t_fields

let[@inline] marked (a:t) : bool =
  Term_fields.get (field_ a) a.a_term.t_fields

let pp_level fmt a = Reason.pp_opt fmt (level a, reason a)

let[@inline] mark_neg (a:t) = mark (neg a)
let[@inline] unmark_neg (a:t) = unmark (neg a)

let[@inline] eval (a:t) : eval_res =
  begin match Term.eval (term a) with
    | Eval_unknown -> Eval_unknown
    | Eval_into (v, subs) ->
      let v = if is_pos a then v else Value.bool_neg v in
      Eval_into (v, subs)
  end

let[@inline] is_absurd (a:t) : bool = match eval a with
  | Eval_into (V_false,[]) -> true
  | _ -> false

let pp_value fmt a =
  if is_true a then
    Format.fprintf fmt "T%a" pp_level a
  else if is_true (neg a) then
    Format.fprintf fmt "F%a" pp_level a

let debug out a =
  let sign = if is_pos a then "" else "¬" in
  let m_sign = if marked a then "[M]" else "" in
  Format.fprintf out "%s%a[%a]%s"
    sign Term.debug_no_val a.a_term pp_value a m_sign

let pp out a =
  let sign = if is_pos a then "" else "¬" in
  Format.fprintf out "%s%a" sign Term.pp a.a_term

module Set = CCSet.Make(struct
    type t = atom
    let compare = compare
  end)
