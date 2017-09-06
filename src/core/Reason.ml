
open Solver_types

type t = reason

let pp out = function
  | n, _ when n < 0 ->
    Format.fprintf out "%%"
  | n, None ->
    Format.fprintf out "%d" n
  | n, Some Decision ->
    Format.fprintf out "@@%d" n
  | n, Some Bcp c ->
    Format.fprintf out "$%d@<1>←%s%d" n (Premise.prefix c.c_premise) c.c_name
  | n, Some (Semantic _) ->
    Format.fprintf out "$%d" n

