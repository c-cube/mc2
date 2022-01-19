
open Solver_types

type t = reason

let pp out = function
  | n, _ when n < 0 ->
    Format.fprintf out "%%"
  | n, Decision ->
    Format.fprintf out "@@%d" n
  | n, Bcp c ->
    Format.fprintf out "#%d@<1>←%a" n pp_clause_name c
  | n, Bcp_lazy c ->
    if Lazy.is_val c
    then (
      let lazy c = c in
      Format.fprintf out "#%d@<1>←%a" n pp_clause_name c
    ) else Format.fprintf out "#%d@<1>←<lazy>" n
  | n, Eval _ ->
    Format.fprintf out "$%d" n

let pp_opt out = function
  | n, _ when n < 0 ->
    Format.fprintf out "%%"
  | n, None ->
    Format.fprintf out "%d" n
  | n, Some r -> pp out (n,r)


