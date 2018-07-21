
(** {1 Actions for Plugins} *)

open Solver_types

type t = actions

let[@inline] push_clause acts c = acts.act_push_clause c
let[@inline] level acts = acts.act_level ()
let[@inline] propagate_bool_eval acts t b ~subs = acts.act_propagate_bool_eval t b ~subs
let[@inline] propagate_bool_lemma acts t b c l = acts.act_propagate_bool_lemma t b c l
let[@inline] raise_conflict acts atoms lemma = acts.act_raise_conflict atoms lemma
let[@inline] on_backtrack acts f = acts.act_on_backtrack f
let[@inline] declare_term_with_singleton_domain acts t =
  acts.act_declare_term_with_singleton_domain t

let[@inline] propagate_bool_lemma acts t b c l =
  acts.act_propagate_bool_lemma t b c l

