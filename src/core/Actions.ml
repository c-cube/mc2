
(** {1 Actions for Plugins} *)

open Solver_types

type t = actions

let[@inline] push_clause acts c = acts.act_push_clause c
let[@inline] level acts = acts.act_level ()
let[@inline] propagate_bool_eval acts t b ~subs = acts.act_propagate_bool_eval t b ~subs
let[@inline] propagate_bool_lemma acts t b c = acts.act_propagate_bool_lemma t b c
let[@inline] raise_conflict acts atoms = acts.act_raise_conflict atoms
let[@inline] on_backtrack acts f = acts.act_on_backtrack f

