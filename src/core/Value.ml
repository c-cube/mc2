
(** {1 Values} *)

open Solver_types
module Fmt = CCFormat

type t = value

let[@inline] is_bool = function V_true | V_false -> true | V_value _ -> false
let[@inline] is_true = function V_true -> true | _ -> false
let[@inline] is_false = function V_false -> true | _ -> false
let[@inline] as_bool = function V_true -> Some true | V_false -> Some false | _ -> None
let[@inline] as_bool_exn = function V_true -> true | V_false -> false | _ -> assert false

let[@inline] view v = match v with
  | V_true | V_false -> assert false
  | V_value{view;_} -> view
let[@inline] tc v = match v with
  | V_true | V_false -> assert false
  | V_value{tc;_} -> tc
let[@inline] equal v1 v2 = match v1, v2 with
  | V_true, V_true
  | V_false, V_false -> true
  | V_value {tc=tc1;view=v1}, V_value{view=v2;_} ->
    tc1.tcv_equal v1 v2
  | V_true, _
  | V_false, _
  | V_value _, _ -> false
let[@inline] hash v = match v with
  | V_true -> 10
  | V_false -> 20
  | V_value{view;tc} -> tc.tcv_hash view
let[@inline] pp out v = match v with
  | V_true -> Fmt.string out "true"
  | V_false -> Fmt.string out "false"
  | V_value {view;tc} -> tc.tcv_pp out view
let true_ = V_true
let false_ = V_false
let[@inline] of_bool b = if b then true_ else false_
let[@inline] make tc view : t = V_value { tc; view }

module Tbl = CCHashtbl.Make(struct
    type t = value
    let equal = equal
    let hash = hash
  end)
