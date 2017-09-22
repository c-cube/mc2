
(** {1 Actions for Plugins} *)

open Solver_types

type t = actions

let[@inline] push_clause acts c = acts.act_push_clause c
let[@inline] level acts = acts.act_level ()
let[@inline] propagate_bool_eval acts t b ~subs = acts.act_propagate_bool_eval t b ~subs
let[@inline] propagate_bool_lemma acts t b c l = acts.act_propagate_bool_lemma t b c l
let[@inline] propagate_val_eval acts t v ~subs = acts.act_propagate_val_eval t v ~subs
let[@inline] propagate_val_lemma acts t v ~rw_into c l =
  acts.act_propagate_val_lemma t v ~rw_into c l
let[@inline] mark_dirty acts t = acts.act_mark_dirty t
let[@inline] raise_conflict acts atoms lemma = acts.act_raise_conflict atoms lemma
let[@inline] on_backtrack acts lvl f = acts.act_on_backtrack lvl f

let[@inline] propagate_bool_lemma acts t b c l =
  acts.act_propagate_bool_lemma t b c l

