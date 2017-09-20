
open Solver_types

type t = atom

let[@inline] equal a b = a.a_id = b.a_id
let[@inline] compare a b = CCInt.compare a.a_id b.a_id

let[@inline] same_term a b = a.a_term == b.a_term

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

let[@inline] value (a:t) : term_assignment = a.a_term.t_value
let[@inline] value_exn (a:t) : value = match value a with
  | TA_none -> assert false
  | TA_assign {value;_} -> value

let[@inline] value_bool (a:t): bool option = match value a with
  | TA_none -> None
  | TA_assign{value=V_true;_} -> Some true
  | TA_assign{value=V_false;_} -> Some false
  | _ -> assert false

let[@inline] value_bool_exn (a:t): bool = match value a with
  | TA_assign{value=V_true;_} -> true
  | TA_assign{value=V_false;_} -> false
  | _ -> assert false

let[@inline] is_true (a:t): bool = match a.a_term.t_value, a.a_term.t_var with
  | TA_assign{value=V_true; _}, Var_bool{pa;_} when a==pa -> true
  | TA_assign{value=V_false;_}, Var_bool{na;_} when a==na -> true
  | _ -> false

let[@inline] is_false (a:t): bool = match a.a_term.t_value, a.a_term.t_var with
  | TA_assign{value=V_true; _}, Var_bool{na;_} when a==na -> true
  | TA_assign{value=V_false;_}, Var_bool{pa;_} when a==pa -> true
  | _ -> false

let[@inline] is_undef (a:t): bool = match value a with
  | TA_none -> true
  | _ -> false
let[@inline] has_value (a:t): bool = match value a with
  | TA_assign _ -> true
  | TA_none -> false

let[@inline] reason (a:t) = match a.a_term.t_value with
  | TA_assign{reason;_} -> Some reason
  | _ -> None

let[@inline] term (a:t) = a.a_term
let[@inline] level (a:t) = Term.level a.a_term
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

let pp_level fmt a = Reason.pp_opt fmt (level a, reason a)

let[@inline] mark_neg (a:t) = mark (neg a)
let[@inline] unmark_neg (a:t) = unmark (neg a)

module Subst = struct
  type t = term_subst
  type cache = Term.Subst.rw_cache

  (* paramodulate inside atom *)
  let[@inline] apply ?(cache=Term.Subst.mk_cache()) (subst:term_subst) (a:atom) : atom =
    let t = Term.Subst.apply ~cache subst (term a) in
    assert (Term.is_bool t);
    if is_pos a then Term.Bool.pa t else Term.Bool.na t
end

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
  Format.fprintf out "%s%a[%a]"
    sign Term.debug_no_val a.a_term pp_value a

let pp out a =
  let sign = if is_pos a then "" else "¬" in
  Format.fprintf out "%s%a" sign Term.pp a.a_term

module Set = CCSet.Make(struct
    type t = atom
    let compare = compare
  end)
