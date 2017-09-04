
(** {1 Values} *)

open Solver_types

type t = value

let[@inline] equal v1 v2 = v1.val_tc.tcv_equal v1.val_view v2.val_view
let[@inline] hash v = v.val_tc.tcv_hash v.val_view
let[@inline] pp out v = v.val_tc.tcv_pp out v.val_view
let[@inline] make val_tc val_view : t = { val_tc; val_view }
