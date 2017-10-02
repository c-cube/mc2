
open Solver_types

type t = atom

let[@inline] equal a b = a.a_id = b.a_id
let[@inline] compare a b = CCInt.compare a.a_id b.a_id

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

let[@inline] value_bool (a:t): bool option = match Term.value a.a_term with
  | TA_none -> None
  | TA_assign{value=V_true;_} -> Some (is_pos a)
  | TA_assign{value=V_false;_} -> Some (not (is_pos a))
  | _ -> assert false

let[@inline] value_bool_exn (a:t): bool = match Term.value a.a_term with
  | TA_assign{value=V_true;_} -> is_pos a
  | TA_assign{value=V_false;_} -> not (is_pos a)
  | _ -> assert false

let[@inline] is_true (a:t): bool = match a.a_term.t_value, a.a_term.t_var with
  | TA_assign{value=V_true; _}, Var_bool{pa;_} when a==pa -> true
  | TA_assign{value=V_false;_}, Var_bool{na;_} when a==na -> true
  | _ -> false

let[@inline] is_false (a:t): bool = match a.a_term.t_value, a.a_term.t_var with
  | TA_assign{value=V_true; _}, Var_bool{na;_} when a==na -> true
  | TA_assign{value=V_false;_}, Var_bool{pa;_} when a==pa -> true
  | _ -> false

let[@inline] is_undef (a:t): bool = match Term.value a.a_term with
  | TA_none -> true
  | _ -> false
let[@inline] has_value (a:t): bool = not (is_undef a)

let[@inline] reason (a:t) = match a.a_term.t_value with
  | TA_both{reason_eval=reason;_}
  | TA_eval{reason;_}
  | TA_assign{reason;_} -> Some reason
  | _ -> None

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

let[@inline] eval_bool (a:t) : eval_bool_res =
  begin match Term.eval_bool (term a) with
    | Eval_unknown -> Eval_unknown
    | Eval_bool (v, subs) ->
      let v = if is_pos a then v else not v in
      Eval_bool (v, subs)
  end

let[@inline] is_absurd (a:t) : bool = match eval_bool a with
  | Eval_bool (false,[]) -> true
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
