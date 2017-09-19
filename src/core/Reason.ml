
open Solver_types

type t = reason

let pp out = function
  | n, _ when n < 0 ->
    Format.fprintf out "%%"
  | n, Decision ->
    Format.fprintf out "@@%d" n
  | n, Bcp c ->
    Format.fprintf out "$%d@<1>←%s%d" n (Premise.prefix c.c_premise) c.c_name
  | n, Bcp_lazy c ->
    if Lazy.is_val c
    then (
      let lazy c = c in
      Format.fprintf out "$%d@<1>←%s%d" n (Premise.prefix c.c_premise) c.c_name
    ) else Format.fprintf out "$%d@<1>←<lazy>" n
  | n, Propagate_value {rw_into;_} ->
    Format.fprintf out "$%d@<1>←%a" n Term.debug rw_into
  | n, Semantic _ ->
    Format.fprintf out "$%d" n

let pp_opt out = function
  | n, _ when n < 0 ->
    Format.fprintf out "%%"
  | n, None ->
    Format.fprintf out "%d" n
  | n, Some r -> pp out (n,r)


