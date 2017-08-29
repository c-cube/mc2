(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

open Solver_types

type proof = Res.proof

exception Sat
exception Unsat
exception UndecidedLit
exception Restart
exception Conflict of clause
exception Plugin_not_found of plugin_id

(* Log levels *)
let error = 1
let warn = 3
let info = 5
let debug = 50

(* Main heap for decisions, sorted by decreasing activity.

   Activity is used to decide on which variable to decide when propagation
   is done. Uses a heap to keep track of variable activity.
   When we add a variable (which wraps a formula), we also need to add all
   its subterms.
*)
module H = Heap.Make(struct
    type t = term
    let[@inline] idx t = t.t_idx
    let[@inline] set_idx t i = t.t_idx <- i
    let[@inline] cmp i j = Term.weight j < Term.weight i (* comparison by weight *)
    let dummy = dummy_term
  end)

(* full state of the solver *)
type t = {
  plugins: Plugin.t CCVector.vector;
  (* the plugins responsible for enforcing the semantics of terms *)

  (* Clauses are simplified for eficiency purposes. In the following
     vectors, the comments actually refer to the original non-simplified
     clause. *)

  clauses_hyps : clause Vec.t;
  (* clauses added by the user *)
  clauses_learnt : clause Vec.t;
  (* learnt clauses (tautologies true at any time, whatever the user level) *)
  clauses_temp : clause Vec.t;
  (* Temp clauses, corresponding to the local assumptions. This vec is used
     only to have an efficient way to access the list of local assumptions. *)

  clauses_root : clause Stack.t;
  (* Clauses that should propagate at level 0, but couldn't *)
  clauses_to_add : clause Stack.t;
  (* Clauses either assumed or pushed by the theory, waiting to be added. *)

  mutable unsat_conflict : clause option;
  (* conflict clause at [base_level], if any *)
  mutable next_decision : atom option;
  (* When the last conflict was a semantic one, this stores the next decision to make *)

  trail : term Vec.t;
  (* main stack containing assignments (either decisions or propagations) *)

  decision_levels : int Vec.t;
  (* decision levels in [trail]  *)

  backtrack_stack : (unit -> unit) Vec.t Vec.t;
  (* one set of undo actions for every decision level *)

  user_levels : int Vec.t;
  (* user levels in [clauses_temp] *)

  mutable th_head : int;
  (* Start offset in the queue {!trail} of
     unit facts not yet seen by the theory. *)
  mutable elt_head : int;
  (* Start offset in the queue {!trail} of
     unit facts to propagate, within the trail *)

  (* invariant:
     - during propagation, th_head <= elt_head
     - then, once elt_head reaches length trail, Th.assume is
       called so that th_head can catch up with elt_head
     - this is repeated until a fixpoint is reached;
     - before a decision (and after the fixpoint),
       th_head = elt_head = length trail
  *)


  mutable simpDB_props : int;
  (* remaining number of propagations before the next call to [simplify ()] *)
  mutable simpDB_assigns : int;
  (* number of toplevel assignments since last call to [simplify ()] *)

  order : H.t;
  (* Heap ordered by variable activity *)

  var_decay : float;
  (* inverse of the activity factor for variables. Default 1/0.999 *)
  clause_decay : float;
  (* inverse of the activity factor for clauses. Default 1/0.95 *)

  mutable var_incr : float;
  (* increment for variables' activity *)
  mutable clause_incr : float;
  (* increment for clauses' activity *)

  remove_satisfied : bool;
  (* Wether to remove satisfied learnt clauses when simplifying *)

  restart_inc : float;
  (* multiplicative factor for restart limit, default 1.5 *)
  mutable restart_first : int;
  (* intial restart limit, default 100 *)


  learntsize_inc : float;
  (* multiplicative factor for [learntsize_factor] at each restart, default 1.1 *)
  mutable learntsize_factor : float;
  (* initial limit for the number of learnt clauses, 1/3 of initial
      number of clauses by default *)

  mutable starts : int;
  mutable decisions : int;
  mutable propagations : int;
  mutable conflicts : int;
  mutable clauses_literals : int;
  mutable learnts_literals : int;
  mutable nb_init_clauses : int;
}

(* main building function *)
let create () : t = {
  plugins = CCVector.create();
  unsat_conflict = None;
  next_decision = None;

  clauses_hyps = Vec.make 0 dummy_clause;
  clauses_learnt = Vec.make 0 dummy_clause;
  clauses_temp = Vec.make 0 dummy_clause;

  clauses_root = Stack.create ();
  clauses_to_add = Stack.create ();

  th_head = 0;
  elt_head = 0;

  trail = Vec.make 601 dummy_term;
  backtrack_stack = Vec.make 601 (Vec.make_empty (fun () -> assert false));
  decision_levels = Vec.make 601 (-1);
  user_levels = Vec.make 10 (-1);

  order = H.create();

  var_incr = 1.;
  clause_incr = 1.;
  var_decay = 1. /. 0.95;
  clause_decay = 1. /. 0.999;

  simpDB_assigns = -1;
  simpDB_props = 0;

  remove_satisfied = false;

  restart_inc = 1.5;
  restart_first = 100;

  learntsize_factor = 1. /. 3. ;
  learntsize_inc = 1.1;

  starts = 0;
  decisions = 0;
  propagations = 0;
  conflicts = 0;
  clauses_literals = 0;
  learnts_literals = 0;
  nb_init_clauses = 0;
}

(** {2 Print} *)

let pp_term (db:t) out (t:term): unit =
  let rec aux out t =
    let id = Term.plugin_id t in
    if (id:>int) >= CCVector.length db.plugins then (
      raise (Plugin_not_found id);
    );
    let (module P) = CCVector.get db.plugins (id:>int) in
    P.pp_term aux out (Term.view t)
  in
  aux out t

let pp_atom env = Atom.pp (pp_term env)
let pp_clause env = Clause.pp (pp_term env)

let[@inline] plugins t = t.plugins

(* Misc functions *)
let[@inline] to_float i = float_of_int i
let[@inline] to_int f = int_of_float f

let[@inline] nb_clauses env = Vec.size env.clauses_hyps
(* let nb_vars    () = St.nb_elt () *)
let[@inline] decision_level env = Vec.size env.decision_levels
let[@inline] base_level env = Vec.size env.user_levels

(* how to add a plugin *)
let add_plugin (db:t) (fcty:Plugin.factory) : Plugin.t =
  let id = CCVector.length db.plugins |> Term.Unsafe.mk_plugin_id in
  let p =
    fcty
      ~on_backtrack:(fun lev f ->
        if lev >= decision_level db then f()
        else (
          Vec.push (Vec.get db.backtrack_stack lev) f
        ))
      ~plugin_id:id
  in
  CCVector.push db.plugins p;
  Log.debugf info (fun k->k "add plugin %s with ID %d" (Plugin.name p) id);
  p

(* obtain the plugin with this ID *)
let[@inline] get_plugin (env:t) (p_id:plugin_id): Plugin.t =
  try CCVector.get env.plugins p_id
  with _ ->
    Log.debugf error (fun k->k "cannot find plugin %d" p_id);
    assert false

let pp_clause db = Clause.pp (pp_term db)

(* Are the assumptions currently unsat ? *)
let[@inline] is_unsat t = match t.unsat_conflict with
  | Some _ -> true
  | None -> false

(* FIXME: remove this? just do it unconditionally, and simple cases like
   SAT will just not iterate at all.
   NOTE: might not even be useful, or maybe should be done when the
   term is activated *)

(* Iteration over subterms.
   When incrementing activity, we want to be able to iterate over
   all subterms of a formula. However, the function provided by the theory
   may be costly (if it walks a tree-like structure, and does some processing
   to ignore some subterms for instance), so we want to 'cache' the list
   of subterms of each formula, so we have a field [v_assignable]
   directly in variables to do so.  *)
let[@inline] iter_sub (env:t) (t:term): term Sequence.t =
  CCVector.to_seq env.plugins
  |> Sequence.flat_map
    (fun (module P : Plugin.S) -> P.iter_sub t)

(* iterate on all active terms *)
let[@inline] iter_terms (env:t) : term Sequence.t =
  CCVector.to_seq env.plugins
  |> Sequence.flat_map
    (fun (module P : Plugin.S) -> P.iter_terms)
  |> Sequence.filter Term.has_var

(* provision term (and its sub-terms) for future assignments *)
let add_term (env:t) (t:term): unit =
  let rec aux t =
    if Term.is_deleted t then (
      Util.errorf "(@[trying to add deleted term@ `%a`@])" (pp_term env) t
    ) else if Term.has_var t then (
      assert (t.t_var <> V_none);
      assert (t.t_idx >= 0);
    ) else (
      Term.setup_var t;
      (* add subterms *)
      iter_sub env t aux;
      (* add to priority queue for decision *)
      H.insert env.order t;
    )
  in aux t

(* put [t] in the heap of terms to decide *)
let schedule_decision_term (env:t) (t:term): unit =
  H.insert env.order t

(* Rather than iterate over all the heap when we want to decrease all the
   variables/literals activity, we instead increase the value by which
   we increase the activity of 'interesting' var/lits. *)
let var_decay_activity (env:t) =
  env.var_incr <- env.var_incr *. env.var_decay

let clause_decay_activity (env:t) =
  env.clause_incr <- env.clause_incr *. env.clause_decay

(* decay all variables because FP numbers are getting too high *)
let decay_all_terms (env:t): unit =
  iter_terms env
    (fun t -> Term.set_weight t (Term.weight t *. 1e-100));
  env.var_incr <- env.var_incr *. 1e-100;
  ()

(* increase activity of [t] *)
let bump_term_activity_aux (env:t) (t:term): unit =
  t.t_weight <- t.t_weight +. env.var_incr;
  if t.t_weight > 1e100 then (
    decay_all_terms env;
  );
  if H.in_heap t then (
    H.decrease env.order t
  )

(* increase activity of var [t] *)
let[@inline] bump_term_activity env (t:term): unit =
  bump_term_activity_aux env t;
  iter_sub env t (bump_term_activity_aux env)

let decay_all_learnt_clauses env : unit =
  Vec.iter
    (fun c -> c.c_activity <- c.c_activity *. 1e-20)
    env.clauses_learnt;
  env.clause_incr <- env.clause_incr *. 1e-20

(* increase activity of clause [c] *)
let[@inline] bump_clause_activity (env:t) (c:clause) : unit =
  c.c_activity <- c.c_activity +. env.clause_incr;
  if c.c_activity > 1e20 then (
    decay_all_learnt_clauses env;
  )

(* Simplification of clauses.

   When adding new clauses, it is desirable to 'simplify' them, i.e
   minimize the amount of literals in it, because it greatly reduces
   the search space for new watched literals during propagation.
   Additionally, we have to partition the lits, to ensure the watched
   literals (which are the first two lits of the clause) are appropriate.
   Indeed, it is better to watch true literals, and then unassigned literals.
   Watching false literals should be a last resort, and come with constraints
   (see add_clause).
*)
exception Trivial

(* [arr_to_list a i] converts [a.(i), ... a.(length a-1)] into a list *)
let arr_to_list arr i : _ list =
  if i >= Array.length arr then []
  else Array.to_list (Array.sub arr i (Array.length arr - i))

(* Eliminates atom doublons in clauses.
   returns [true] if something changed. *)
let eliminate_doublons clause : clause * bool =
  let duplicates = ref [] in
  let res = ref [] in
  Array.iter
    (fun a ->
       if Atom.marked a then duplicates := a :: !duplicates
       else (Atom.mark a; res := a :: !res))
    (Clause.atoms clause);
  (* cleanup *)
  let trivial =
    List.exists (fun a -> Term.Bool.both_atoms_marked a.a_term) !res
  in
  List.iter Atom.unmark !res;
  if trivial then (
    raise Trivial
  ) else if !duplicates = [] then (
    clause, false
  ) else (
    (* make a new clause, simplified *)
    Clause.make ~name:(Clause.fresh_lname ()) !res (History [clause]), true
  )

(* Partition literals for new clauses, into:
   - true literals (maybe makes the clause trivial if the lit is proved true at level 0)
   - unassigned literals, yet to be decided
   - false literals (not suitable to watch, those at level 0 can be removed from the clause)

   Then, true literals are put first, then unassigned ones, then false ones.
   This is suitable for watching the resulting clause.

   Clauses that propagated false lits are remembered,
   to reconstruct resolution proofs.
*)
let partition atoms : atom list * clause list =
  let rec partition_aux trues unassigned falses history i =
    if i >= Array.length atoms then (
      trues @ unassigned @ falses, history
    ) else (
      let a = atoms.(i) in
      if Atom.is_true a then (
        let l = Atom.level a in
        if l = 0 then (
          raise Trivial (* A var true at level 0 gives a trivially true clause *)
        ) else (
          (a :: trues) @ unassigned @ falses @
            (arr_to_list atoms (i + 1)), history
        )
      ) else if Atom.is_false a then (
        let l = Atom.level a in
        if l = 0 then (
          begin match a.a_term.t_reason with
            | Some (Bcp cl) ->
              partition_aux trues unassigned falses (cl :: history) (i + 1)
            (* A var false at level 0 can be eliminated from the clause,
               but we need to kepp in mind that we used another clause to simplify it. *)
            | Some (Semantic _) ->
              partition_aux trues unassigned falses history (i + 1)
            (* Semantic propagations at level 0 are, well not easy to deal with,
               this shouldn't really happen actually (because semantic propagations
               at level 0 should come with a proof). *)
            (* TODO: get a proof of the propagation. *)
            | None | Some Decision -> assert false
            (* The var must have a reason, and it cannot be a decision/assumption,
               since its level is 0. *)
          end
        ) else (
          partition_aux trues unassigned (a::falses) history (i + 1)
        )
      ) else (
        partition_aux trues (a::unassigned) falses history (i + 1)
      )
    )
  in
  partition_aux [] [] [] [] 0


(* Making a decision.
   Before actually creatig a new decision level, we check that all propagations
   have been done and propagated to the theory, i.e that the theoriy state
   indeed takes into account the whole stack of literals, i.e we have indeed
   reached a propagation fixpoint before making a new decision *)
let new_decision_level (env:t) : unit =
  assert (env.th_head = Vec.size env.trail);
  assert (env.elt_head = Vec.size env.trail);
  Vec.push env.decision_levels (Vec.size env.trail);
  ()

(* Attach/Detach a clause.
   A clause is attached (to its watching lits) when it is first added,
   either because it is assumed or learnt.
*)
let attach_clause (env:t) (c:clause): unit =
  assert (not (Clause.attached c));
  Log.debugf debug (fun k -> k "Attaching %a" (pp_clause env) c);
  Vec.push (Atom.neg c.c_atoms.(0)).a_watched c;
  Vec.push (Atom.neg c.c_atoms.(1)).a_watched c;
  Clause.set_attached c;
  ()

(* Backtracking.
   Used to backtrack, i.e cancel down to [lvl] excluded,
   i.e we want to go back to the state the solver was in
       when decision level [lvl] was created. *)
let cancel_until (env:t) (lvl:int) : unit =
  assert (lvl >= base_level env);
  (* Nothing to do if we try to backtrack to a non-existent level. *)
  if decision_level env <= lvl then (
    Log.debugf debug (fun k -> k "Already at level <= %d" lvl)
  ) else (
    Log.debugf info (fun k -> k "Backtracking to lvl %d" lvl);
    (* We set the head of the solver and theory queue to what it was. *)
    let head = ref (Vec.get env.decision_levels lvl) in
    env.elt_head <- !head;
    env.th_head <- !head;
    (* Now we need to cleanup the vars that are not valid anymore
       (i.e to the right of elt_head in the queue. *)
    for i = env.elt_head to Vec.size env.trail - 1 do
      (* A variable is unassigned, we nedd to add it back to
         the heap of potentially assignable variables, unless it has
         a level lower than [lvl], in which case we just move it back. *)
      let t = Vec.get env.trail i in
      if Term.level t <= lvl then (
        Vec.set env.trail !head t;
        head := !head + 1
      ) else (
        t.t_level <- -1;
        schedule_decision_term env t;
        begin match t.t_var with
          | V_none -> assert false
          | V_semantic v -> v.v_value <- None;
          | V_bool {pa; na} ->
            pa.a_is_true <- false;
            na.a_is_true <- false;
        end
      )
    done;
    (* call undo-actions registered by plugins *)
    while Vec.size env.backtrack_stack > lvl do
      let v = Vec.last env.backtrack_stack in
      Vec.iter (fun f -> f()) v;
      Vec.pop env.backtrack_stack;
    done;
    (* Resize the vectors according to their new size. *)
    Vec.shrink env.trail ((Vec.size env.trail) - !head);
    Vec.shrink env.decision_levels ((Vec.size env.decision_levels) - lvl);
  );
  assert (Vec.size env.decision_levels = Vec.size env.backtrack_stack);
  ()

(* Unsatisfiability is signaled through an exception, since it can happen
   in multiple places (adding new clauses, or solving for instance). *)
let report_unsat (env:t) (confl:clause) : _ =
  Log.debugf info (fun k -> k "@[Unsat conflict: %a@]" (pp_clause env) confl);
  env.unsat_conflict <- Some confl;
  raise Unsat

(* Simplification of boolean propagation reasons.
   When doing boolean propagation *at level 0*, it can happen
   that the clause cl, which propagates a formula, also contains
   other formulas, but has been simplified. in which case, we
   need to rebuild a clause with correct history, in order to
   be able to build a correct proof at the end of proof search. *)
let simpl_reason (env:t) : reason -> reason = function
  | (Bcp cl) as r ->
    let l, history = partition cl.c_atoms in
    begin match l with
      | [_] ->
        if history = [] then r
        (* no simplification has been done, so [cl] is actually a clause with only
           [a], so it is a valid reason for propagating [a]. *)
        else (
          (* Clauses in [history] have been used to simplify [cl] into a clause [tmp_cl]
             with only one formula (which is [a]). So we explicitly create that clause
             and set it as the cause for the propagation of [a], that way we can
             rebuild the whole resolution tree when we want to prove [a]. *)
          let c' =
            Clause.make ~name:(Clause.fresh_lname ()) l (History (cl :: history))
          in
          Log.debugf debug
            (fun k -> k "Simplified reason: @[<v>%a@,%a@]"
                (pp_clause env) cl (pp_clause env) c');
          Bcp c'
        )
      | _ ->
        Log.debugf error
          (fun k ->
             k
               "@[<v 2>Failed at reason simplification:@,%a@,%a@]"
               (Vec.print ~sep:"" (pp_atom env))
               (Vec.from_list l (List.length l) dummy_atom)
               (pp_clause env) cl);
        assert false
    end
  | r -> r

(* Boolean propagation.
   Wrapper function for adding a new propagated formula. *)
let enqueue_bool (env:t) (a:atom) ~level:lvl (reason:reason) : unit =
  if Atom.is_false a then (
    Log.debugf error
      (fun k->k "Trying to enqueue a false literal: %a" (pp_atom env) a);
    assert false
  );
  assert (not (Atom.is_true a) && Atom.level a < 0 &&
          Atom.reason a = None && lvl >= 0);
  (* simplify reason *)
  let reason =
    if lvl > 0 then reason
    else simpl_reason env reason
  in
  a.a_is_true <- true;
  a.a_term.t_level <- lvl;
  a.a_term.t_reason <- Some reason;
  Vec.push env.trail a.a_term;
  Log.debugf debug
    (fun k->k "Enqueue (%d): %a" (Vec.size env.trail) (pp_atom env) a);
  ()

(* atom [a] evaluates to [true] because of [terms] *)
let enqueue_semantic_bool_eval (env:t) (a:atom) (terms:term list) : unit =
  if Atom.is_true a then ()
  else (
    List.iter (add_term env) terms;
    (* level of propagations is [max_{t in terms} t.level] *)
    let lvl =
      List.fold_left
        (fun acc {t_level; _} ->
           assert (t_level > 0); max acc t_level)
        0 terms
    in
    enqueue_bool env a ~level:lvl (Semantic terms)
  )

(* MCsat semantic assignment *)
let enqueue_assign (env:t) (t:term) (value:value) (lvl:int) : unit =
  begin match t.t_var with
    | V_none | V_bool _ ->  assert false
    | V_semantic {v_value=Some _; _} ->
      Log.debugf error
        (fun k -> k "Trying to assign an already assigned literal: %a" (pp_term env) t);
      assert false
    | V_semantic ({v_value=None; _} as v) ->
      assert (t.t_level < 0);
      v.v_value <- Some value;
      t.t_level <- lvl;
      Vec.push env.trail t;
      Log.debugf debug
        (fun k->k "Enqueue (%d): %a" (Vec.size env.trail) (pp_term env) t);
  end

(* evaluate an atom for MCsat, if it's not assigned
   by boolean propagation/decision *)
let th_eval (env:t) (a:atom) : bool option =
  if Atom.is_true a || Atom.is_false a then None
  else (
    let p_id = Term.plugin_id a.a_term in
    let (module P : Plugin.S) = get_plugin env p_id in
    begin match P.eval_bool a.a_term with
      | Plugin.Unknown -> None
      | Plugin.Valued (b, l) ->
        let atom = if b then a else Atom.neg a in
        enqueue_semantic_bool_eval env atom l;
        Some b
    end
  )

(* find which level to backtrack to, given a conflict clause
   and a boolean stating whether it is a UIP ("Unique Implication Point")
   precond: the atom list is sorted by decreasing decision level *)
let backtrack_lvl (env:t) : atom list -> int * bool = function
  | [] | [_] ->
    0, true
  | a :: b :: _ ->
    assert (Atom.level a > base_level env);
    if Atom.level a > Atom.level b then (
      (* backtrack below [a], so we can propagate [not a] *)
      Atom.level b, true
    ) else (
      (* semantic split *)
      assert (Atom.level a = Atom.level b);
      assert (Atom.level a >= base_level env);
      max (Atom.level a - 1) (base_level env), false
    )

(* result of conflict analysis, containing the learnt clause and some
   additional info.

   invariant: cr_history's order matters, as its head is later used
   during pop operations to determine the origin of a clause/conflict
   (boolean conflict i.e hypothesis, or theory lemma) *)
type conflict_res = {
  cr_backtrack_lvl : int; (* level to backtrack to *)
  cr_learnt: atom list; (* lemma learnt from conflict *)
  cr_history: clause list; (* justification *)
  cr_is_uip: bool; (* conflict is UIP? *)
}

let get_atom i =
  match Vec.get env.trail i with
    | Lit _ -> assert false | Atom x -> x

(* conflict analysis for SAT
   Same idea as the mcsat analyze function (without semantic propagations),
   except we look the the Last UIP (TODO: check ?), and do it in an imperative
   and efficient manner. *)
let analyze_sat c_clause : conflict_res =
  let pathC  = ref 0 in
  let learnt = ref [] in
  let cond   = ref true in
  let blevel = ref 0 in
  let seen   = ref [] in
  let c      = ref (Some c_clause) in
  let tr_ind = ref (Vec.size env.trail - 1) in
  let history = ref [] in
  assert (decision_level () > 0);
  let conflict_level =
    Array.fold_left (fun acc p -> max acc p.var.v_level) 0 c_clause.atoms
  in
  Log.debugf debug
    (fun k -> k "Analyzing conflict (%d): %a" conflict_level St.pp_clause c_clause);
  while !cond do
    begin match !c with
      | None ->
        Log.debug debug "skipping resolution for semantic propagation"
      | Some clause ->
        Log.debugf debug (fun k->k "Resolving clause: %a" St.pp_clause clause);
        begin match clause.cpremise with
          | History _ -> bump_clause_activity clause
          | Hyp | Local | Lemma _ -> ()
        end;
        history := clause :: !history;
        (* visit the current predecessors *)
        for j = 0 to Array.length clause.atoms - 1 do
          let q = clause.atoms.(j) in
          assert (q.is_true || q.neg.is_true && q.var.v_level >= 0); (* unsure? *)
          if q.var.v_level <= 0 then begin
            assert (q.neg.is_true);
            match q.var.reason with
              | Some Bcp cl -> history := cl :: !history
              | _ -> assert false
          end;
          if not (seen_var q.var) then begin
            mark_var q.var;
            seen := q :: !seen;
            if q.var.v_level > 0 then begin
              bump_term_activity q.var;
              if q.var.v_level >= conflict_level then begin
                incr pathC;
              end else begin
                learnt := q :: !learnt;
                blevel := max !blevel q.var.v_level
              end
            end
          end
        done
    end;

    (* look for the next node to expand *)
    while
      let a = Vec.get env.trail !tr_ind in
      Log.debugf debug (fun k -> k "looking at: %a" St.pp a);
      begin match a with
        | Atom q ->
          (not (seen_var q.var)) ||
          (q.var.v_level < conflict_level)
        | Lit _ -> true
      end
    do
      decr tr_ind;
    done;
    let p = get_atom !tr_ind in
    decr pathC;
    decr tr_ind;
    begin match !pathC, p.var.reason with
      | 0, _ ->
        cond := false;
        learnt := p.neg :: (List.rev !learnt)
      | n, Some Semantic ->
        assert (n > 0);
        learnt := p.neg :: !learnt;
        c := None
      | n, Some Bcp cl ->
        assert (n > 0);
        assert (p.var.v_level >= conflict_level);
        c := Some cl
      | _ -> assert false
    end
  done;
  List.iter (fun q -> clear q.var) !seen;
  let l = List.fast_sort (fun p q -> compare q.var.v_level p.var.v_level) !learnt in
  let level, is_uip = backtrack_lvl l in
  { cr_backtrack_lvl = level;
    cr_learnt = l;
    cr_history = List.rev !history;
    cr_is_uip = is_uip;
  }

let analyze c_clause : conflict_res =
  analyze_sat c_clause
    (*
  if St.mcsat
  then analyze_mcsat c_clause
  else analyze_sat c_clause
       *)

(* add the learnt clause to the clause database, propagate, etc. *)
let record_learnt_clause (confl:clause) (cr:conflict_res): unit =
  begin match cr.cr_learnt with
    | [] -> assert false
    | [fuip] ->
      assert (cr.cr_backtrack_lvl = 0);
      if fuip.neg.is_true then
        report_unsat confl
      else begin
        let name = fresh_lname () in
        let uclause = make_clause name cr.cr_learnt (History cr.cr_history) in
        Vec.push env.clauses_learnt uclause;
        (* no need to attach [uclause], it is true at level 0 *)
        enqueue_bool fuip ~level:0 (Bcp uclause)
      end
    | fuip :: _ ->
      let name = fresh_lname () in
      let lclause = make_clause name cr.cr_learnt (History cr.cr_history) in
      Vec.push env.clauses_learnt lclause;
      attach_clause lclause;
      bump_clause_activity lclause;
      if cr.cr_is_uip then
        enqueue_bool fuip ~level:cr.cr_backtrack_lvl (Bcp lclause)
      else begin
        env.next_decision <- Some fuip.neg
      end
  end;
  var_decay_activity ();
  clause_decay_activity ()

(* process a conflict:
   - learn clause
   - backtrack
   - report unsat if conflict at level 0
*)
let add_boolean_conflict (confl:clause): unit =
  Log.debugf info (fun k -> k"Boolean conflict: %a"  St.pp_clause confl);
  env.next_decision <- None;
  env.conflicts <- env.conflicts + 1;
  assert (decision_level() >= base_level ());
  if decision_level() = base_level ()
  || CCArray.for_all (fun a -> a.var.v_level <= base_level ()) confl.atoms then
    report_unsat confl; (* Top-level conflict *)
  let cr = analyze confl in
  cancel_until (max cr.cr_backtrack_lvl (base_level ()));
  record_learnt_clause confl cr

(* Get the correct vector to insert a clause in. *)
let clause_vector c =
  match c.cpremise with
    | Hyp -> env.clauses_hyps
    | Local -> env.clauses_temp
    | Lemma _ | History _ -> env.clauses_learnt

(* swap elements of array *)
let swap_arr a i j =
  if i<>j then (
    let tmp = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- tmp;
  )

(* Add a new clause, simplifying, propagating, and backtracking if
   the clause is false in the current trail *)
let add_clause (init:clause) : unit =
  Log.debugf debug (fun k -> k "Adding clause: @[<hov>%a@]" St.pp_clause init);
  (* Insertion of new lits is done before simplification. Indeed, else a lit in a
     trivial clause could end up being not decided on, which is a bug. *)
  Array.iter (fun x -> insert_var_order (elt_of_var x.var)) init.atoms;
  let vec = clause_vector init in
  try
    let c, has_remove_doublons = eliminate_doublons init in
    if has_remove_doublons then (
      Log.debugf debug
        (fun k -> k "Doublons eliminated: %a :from %a" St.pp_clause c St.pp_clause init);
    );
    let atoms, history = partition c.atoms in
    let clause =
      if history = []
      then (
        (* update order of atoms *)
        List.iteri (fun i a -> c.atoms.(i) <- a) atoms;
        c
      )
      else make_clause (fresh_name ()) atoms (History (c :: history))
    in
    Log.debugf info (fun k->k "New clause: @[<hov>%a@]" St.pp_clause clause);
    match atoms with
      | [] ->
        (* Report_unsat will raise, and the current clause will be lost if we do not
           store it somewhere. Since the proof search will end, any of env.clauses_to_add
           or env.clauses_root is adequate. *)
        Stack.push clause env.clauses_root;
        report_unsat clause
      | [a]   ->
        cancel_until (base_level ());
        if a.neg.is_true then begin
          (* Since we cannot propagate the atom [a], in order to not lose
             the information that [a] must be true, we add clause to the list
             of clauses to add, so that it will be e-examined later. *)
          Log.debug debug "Unit clause, adding to clauses to add";
          Stack.push clause env.clauses_to_add;
          report_unsat clause
        end else if a.is_true then begin
          (* If the atom is already true, then it should be because of a local hyp.
             However it means we can't propagate it at level 0. In order to not lose
             that information, we store the clause in a stack of clauses that we will
             add to the solver at the next pop. *)
          Log.debug debug "Unit clause, adding to root clauses";
          assert (0 < a.var.v_level && a.var.v_level <= base_level ());
          Stack.push clause env.clauses_root;
          ()
        end else begin
          Log.debugf debug (fun k->k "Unit clause, propagating: %a" St.pp_atom a);
          Vec.push vec clause;
          enqueue_bool a ~level:0 (Bcp clause)
        end
      | a::b::_ ->
        Vec.push vec clause;
        if a.neg.is_true then (
          (* put the two atoms with highest decision level at the beginning
             of the clause, so that watch literals are always fine *)
          let ats = clause.atoms in
          Array.iteri
            (fun i a ->
               if i>0 && a.var.v_level > ats.(0).var.v_level then (
                 swap_arr ats 0 i
               ) else if i>1 && a.var.v_level > ats.(1).var.v_level then (
                 swap_arr ats 1 i;
               ))
            clause.atoms;
          assert(ats.(0).var.v_level >= ats.(1).var.v_level);
          attach_clause clause;
          add_boolean_conflict clause
        ) else (
          attach_clause clause;
          if b.neg.is_true && not a.is_true && not a.neg.is_true then (
            let lvl = List.fold_left (fun m a -> max m a.var.v_level) 0 atoms in
            cancel_until (max lvl (base_level ()));
            enqueue_bool a ~level:lvl (Bcp clause)
          )
        )
  with Trivial ->
    Vec.push vec init;
    Log.debugf info (fun k->k "Trivial clause ignored : @[%a@]" St.pp_clause init)

let flush_clauses () =
  if not (Stack.is_empty env.clauses_to_add) then begin
    let nbv = St.nb_elt () in
    let nbc = env.nb_init_clauses + Stack.length env.clauses_to_add in
    Iheap.grow_to_at_least env.order nbv;
    Vec.grow_to_at_least env.clauses_hyps nbc;
    Vec.grow_to_at_least env.clauses_learnt nbc;
    env.nb_init_clauses <- nbc;
    while not (Stack.is_empty env.clauses_to_add) do
      let c = Stack.pop env.clauses_to_add in
      add_clause c
    done
  end

type watch_res =
  | Watch_kept
  | Watch_removed

(* boolean propagation.
   [a] is the false atom, one of [c]'s two watch literals
   [i] is the index of [c] in [a.watched]
   @return whether [c] was removed from [a.watched]
*)
let propagate_in_clause (a:atom) (c:clause) (i:int): watch_res =
  let atoms = c.atoms in
  let first = atoms.(0) in
  if first == a.neg then (
    (* false lit must be at index 1 *)
    atoms.(0) <- atoms.(1);
    atoms.(1) <- first
  ) else assert (a.neg == atoms.(1));
  let first = atoms.(0) in
  if first.is_true
  then Watch_kept (* true clause, keep it in watched *)
  else (
    try (* look for another watch lit *)
      for k = 2 to Array.length atoms - 1 do
        let ak = atoms.(k) in
        if not (ak.neg.is_true) then begin
          (* watch lit found: update and exit *)
          atoms.(1) <- ak;
          atoms.(k) <- a.neg;
          (* remove [c] from [a.watched], add it to [ak.neg.watched] *)
          Vec.push ak.neg.watched c;
          assert (Vec.get a.watched i == c);
          Vec.fast_remove a.watched i;
          raise Exit
        end
      done;
      (* no watch lit found *)
      if first.neg.is_true then begin
        (* clause is false *)
        env.elt_head <- Vec.size env.trail;
        raise (Conflict c)
      end else begin
        match th_eval first with
          | None -> (* clause is unit, keep the same watches, but propagate *)
            enqueue_bool first ~level:(decision_level ()) (Bcp c)
          | Some true -> ()
          | Some false ->
            env.elt_head <- Vec.size env.trail;
            raise (Conflict c)
      end;
      Watch_kept
    with Exit ->
      Watch_removed
  )

(* propagate atom [a], which was just decided. This checks every
   clause watching [a] to see if the clause is false, unit, or has
   other possible watches
   @param res the optional conflict clause that the propagation might trigger *)
let propagate_atom a (res:clause option ref) : unit =
  let watched = a.watched in
  begin
    try
      let rec aux i =
        if i >= Vec.size watched then ()
        else (
          let c = Vec.get watched i in
          assert c.attached;
          let j = match propagate_in_clause a c i with
            | Watch_kept -> i+1
            | Watch_removed -> i (* clause at this index changed *)
          in
          aux j
        )
      in
      aux 0
    with Conflict c ->
      assert (!res = None);
      res := Some c
  end;
  ()

(* Propagation (boolean and theory) *)
let create_atom f =
  let a = atom f in
  ignore (th_eval a);
  a

let slice_get i =
  match Vec.get env.trail i with
    | Atom a ->
      Plugin_intf.Lit a.lit
    | Lit {term; assigned = Some v; _} ->
      Plugin_intf.Assign (term, v)
    | Lit _ -> assert false

let slice_push (l:formula list) (lemma:proof): unit =
  let atoms = List.rev_map create_atom l in
  let c = make_clause (fresh_tname ()) atoms (Lemma lemma) in
  Log.debugf info (fun k->k "Pushing clause %a" St.pp_clause c);
  Stack.push c env.clauses_to_add

let slice_propagate f = function
  | Plugin_intf.Eval l ->
    let a = atom f in
    enqueue_semantic_bool_eval a l
  | Plugin_intf.Consequence (causes, proof) ->
    let l = List.rev_map atom causes in
    if List.for_all (fun a -> a.is_true) l then
      let p = atom f in
      let c = make_clause (fresh_tname ())
          (p :: List.map (fun a -> a.neg) l) (Lemma proof) in
      if p.is_true then ()
      else if p.neg.is_true then
        Stack.push c env.clauses_to_add
      else begin
        Iheap.grow_to_at_least env.order (St.nb_elt ());
        insert_subterms_order p.var;
        enqueue_bool p ~level:(decision_level ()) (Bcp c)
      end
    else
      raise (Invalid_argument "Msat.Internal.slice_propagate")

let current_slice (): (_,_,_) Plugin_intf.slice = {
  Plugin_intf.start = env.th_head;
  length = (Vec.size env.trail) - env.th_head;
  get = slice_get;
  push = slice_push;
  propagate = slice_propagate;
}

(* full slice, for [if_sat] final check *)
let full_slice () : (_,_,_) Plugin_intf.slice = {
  Plugin_intf.start = 0;
  length = Vec.size env.trail;
  get = slice_get;
  push = slice_push;
  propagate = (fun _ -> assert false);
}

(* some boolean literals were decided/propagated within Msat. Now we
   need to inform the theory of those assumptions, so it can do its job.
   @return the conflict clause, if the theory detects unsatisfiability *)
let rec theory_propagate (): clause option =
  assert (env.elt_head = Vec.size env.trail);
  assert (env.th_head <= env.elt_head);
  if env.th_head = env.elt_head then
    None (* fixpoint/no propagation *)
  else begin
    let slice = current_slice () in
    env.th_head <- env.elt_head; (* catch up *)
    match Plugin.assume slice with
      | Plugin_intf.Sat ->
        propagate ()
      | Plugin_intf.Unsat (l, p) ->
        (* conflict *)
        let l = List.rev_map create_atom l in
        Iheap.grow_to_at_least env.order (St.nb_elt ());
        List.iter (fun a -> insert_var_order (elt_of_var a.var)) l;
        let c = St.make_clause (St.fresh_tname ()) l (Lemma p) in
        Some c
  end

(* fixpoint between boolean propagation and theory propagation
   @return a conflict clause, if any *)
and propagate (): clause option =
  (* First, treat the stack of lemmas added by the theory, if any *)
  flush_clauses ();
  (* Now, check that the situation is sane *)
  assert (env.elt_head <= Vec.size env.trail);
  if env.elt_head = Vec.size env.trail then
    theory_propagate ()
  else begin
    let num_props = ref 0 in
    let res = ref None in
    while env.elt_head < Vec.size env.trail do
      begin match Vec.get env.trail env.elt_head with
        | Lit _ -> ()
        | Atom a ->
          incr num_props;
          propagate_atom a res
      end;
      env.elt_head <- env.elt_head + 1;
    done;
    env.propagations <- env.propagations + !num_props;
    env.simpDB_props <- env.simpDB_props - !num_props;
    match !res with
      | None -> theory_propagate ()
      | _ -> !res
  end

(* remove some learnt clauses
   NOTE: so far we do not forget learnt clauses. We could, as long as
   lemmas from the theory itself are kept. *)
let reduce_db () = ()

(* Decide on a new literal, and enqueue it into the trail *)
let rec pick_branch_aux atom: unit =
  let v = atom.var in
  if v.v_level >= 0 then begin
    assert (v.pa.is_true || v.na.is_true);
    pick_branch_lit ()
  end else match Plugin.eval atom.lit with
    | Plugin_intf.Unknown ->
      env.decisions <- env.decisions + 1;
      new_decision_level();
      let current_level = decision_level () in
      enqueue_bool atom ~level:current_level Decision
    | Plugin_intf.Valued (b, l) ->
      let a = if b then atom else atom.neg in
      enqueue_semantic_bool_eval a l

and pick_branch_lit () =
  match env.next_decision with
    | Some atom ->
      env.next_decision <- None;
      pick_branch_aux atom
    | None ->
      begin try
          begin match St.get_elt (Iheap.remove_min f_weight env.order) with
            | E_lit l ->
              if l.l_level >= 0 then
                pick_branch_lit ()
              else begin
                let value = Plugin.assign l.term in
                env.decisions <- env.decisions + 1;
                new_decision_level();
                let current_level = decision_level () in
                enqueue_assign l value current_level
              end
            | E_var v ->
              pick_branch_aux v.pa
          end
        with Not_found -> raise Sat
      end

(* do some amount of search, until the number of conflicts or clause learnt
   reaches the given parameters *)
let search n_of_conflicts n_of_learnts: unit =
  let conflictC = ref 0 in
  env.starts <- env.starts + 1;
  while true do
    match propagate () with
      | Some confl -> (* Conflict *)
        incr conflictC;
        (* When the theory has raised Unsat, add_boolean_conflict
           might 'forget' the initial conflict clause, and only add the
           analyzed backtrack clause. So in those case, we use add_clause
           to make sure the initial conflict clause is also added. *)
        if confl.attached then
          add_boolean_conflict confl
        else
          add_clause confl

      | None -> (* No Conflict *)
        assert (env.elt_head = Vec.size env.trail);
        assert (env.elt_head = env.th_head);
        if Vec.size env.trail = St.nb_elt ()
        then raise Sat;
        if n_of_conflicts > 0 && !conflictC >= n_of_conflicts then begin
          Log.debug info "Restarting...";
          cancel_until (base_level ());
          raise Restart
        end;
        (* if decision_level() = 0 then simplify (); *)

        if n_of_learnts >= 0 &&
           Vec.size env.clauses_learnt - Vec.size env.trail >= n_of_learnts
        then reduce_db();

        pick_branch_lit ()
  done

let eval_level lit =
  let var, negated = make_boolean_var lit in
  if not var.pa.is_true && not var.na.is_true
  then raise UndecidedLit
  else assert (var.v_level >= 0);
  let truth = var.pa.is_true in
  let value = match negated with
    | Formula_intf.Negated -> not truth
    | Formula_intf.Same_sign -> truth
  in
  value, var.v_level

let eval lit = fst (eval_level lit)

let unsat_conflict () = env.unsat_conflict

let model () : (term * term) list =
  let opt = function Some a -> a | None -> assert false in
  Vec.fold
    (fun acc e -> match e with
       | Lit v -> (v.term, opt v.assigned)  :: acc
       | Atom _ -> acc)
    [] env.trail

(* fixpoint of propagation and decisions until a model is found, or a
   conflict is reached *)
let solve (): unit =
  Log.debug 5 "solve";
  if is_unsat () then raise Unsat;
  let n_of_conflicts = ref (to_float env.restart_first) in
  let n_of_learnts = ref ((to_float (nb_clauses())) *. env.learntsize_factor) in
  try
    while true do
      begin try
          search (to_int !n_of_conflicts) (to_int !n_of_learnts)
        with
          | Restart ->
            n_of_conflicts := !n_of_conflicts *. env.restart_inc;
            n_of_learnts   := !n_of_learnts *. env.learntsize_inc
          | Sat ->
            assert (env.elt_head = Vec.size env.trail);
            begin match Plugin.if_sat (full_slice ()) with
              | Plugin_intf.Sat -> ()
              | Plugin_intf.Unsat (l, p) ->
                let atoms = List.rev_map create_atom l in
                let c = make_clause (fresh_tname ()) atoms (Lemma p) in
                Log.debugf info (fun k -> k "Theory conflict clause: %a" St.pp_clause c);
                Stack.push c env.clauses_to_add
            end;
            if Stack.is_empty env.clauses_to_add then raise Sat
      end
    done
  with Sat -> ()

let assume ?tag cnf =
  List.iter
    (fun l ->
       let atoms = List.rev_map atom l in
       let c = make_clause ?tag (fresh_hname ()) atoms Hyp in
       Log.debugf debug (fun k -> k "Assuming clause: @[<hov 2>%a@]" pp_clause c);
       Stack.push c env.clauses_to_add)
    cnf

(* create a factice decision level for local assumptions *)
let push (): unit =
  Log.debug debug "Pushing a new user level";
  cancel_until (base_level ());
  Log.debugf debug
    (fun k -> k "@[<v>Status:@,@[<hov 2>trail: %d - %d@,%a@]"
        env.elt_head env.th_head (Vec.print ~sep:"" St.pp) env.trail);
  begin match propagate () with
    | Some confl ->
      report_unsat confl
    | None ->
      Log.debugf debug
        (fun k -> k "@[<v>Current trail:@,@[<hov>%a@]@]"
            (Vec.print ~sep:"" St.pp) env.trail);
      Log.debug info "Creating new user level";
      new_decision_level ();
      Vec.push env.user_levels (Vec.size env.clauses_temp);
      assert (decision_level () = base_level ())
  end

(* pop the last factice decision level *)
let pop (): unit =
  if base_level () = 0 then (
    Log.debug warn "Cannot pop (already at level 0)";
  ) else (
    Log.debug info "Popping user level";
    assert (base_level () > 0);
    env.unsat_conflict <- None;
    let n = Vec.last env.user_levels in
    Vec.pop env.user_levels; (* before the [cancel_until]! *)
    (* Add the root clauses to the clauses to add *)
    Stack.iter (fun c -> Stack.push c env.clauses_to_add) env.clauses_root;
    Stack.clear env.clauses_root;
    (* remove from env.clauses_temp the now invalid caluses. *)
    Vec.shrink env.clauses_temp (Vec.size env.clauses_temp - n);
    assert (Vec.for_all (fun c -> Array.length c.atoms = 1) env.clauses_temp);
    assert (Vec.for_all (fun c -> c.atoms.(0).var.v_level <= base_level ()) env.clauses_temp);
    cancel_until (base_level ())
  )

(* Add local hyps to the current decision level *)
let local l =
  let aux lit =
    let a = atom lit in
    Log.debugf info (fun k-> k "Local assumption: @[%a@]" pp_atom a);
    assert (decision_level () = base_level ());
    if a.is_true then ()
    else (
      let c = make_clause (fresh_hname ()) [a] Local in
      Log.debugf debug (fun k -> k "Temp clause: @[%a@]" pp_clause c);
      Vec.push env.clauses_temp c;
      if a.neg.is_true then (
        (* conflict between assumptions: UNSAT *)
        report_unsat c;
      ) else (
        (* Grow the heap, because when the lit is backtracked,
           it will be added to the heap. *)
        Iheap.grow_to_at_least env.order (St.nb_elt ());
        (* make a decision, propagate *)
        let level = decision_level() in
        enqueue_bool a ~level (Bcp c);
      )
    )
  in
  assert (base_level () > 0);
  begin match env.unsat_conflict with
    | None ->
      Log.debug info "Adding local assumption";
      cancel_until (base_level ());
      List.iter aux l
    | Some _ ->
      Log.debug warn "Cannot add local assumption (already unsat)"
  end

(* Check satisfiability *)
let check_clause c =
  let tmp = Array.map (fun a ->
      if a.is_true then true
      else if a.neg.is_true then false
      else raise UndecidedLit) c.atoms in
  let res = CCArray.exists (fun x -> x) tmp in
  if res then true
  else (
    Log.debugf debug
      (fun k -> k "Clause not satisfied: @[<hov>%a@]" St.pp_clause c);
    false
  )

let check_vec v =
  Vec.for_all check_clause v

let check_stack s =
  try
    Stack.iter (fun c -> if not (check_clause c) then raise Exit) s;
    true
  with Exit ->
    false

let check () =
  Stack.is_empty env.clauses_to_add &&
  check_stack env.clauses_root &&
  check_vec env.clauses_hyps &&
  check_vec env.clauses_learnt &&
  check_vec env.clauses_temp

(* Unsafe access to internal data *)

let hyps () = env.clauses_hyps

let history () = env.clauses_learnt

let temp () = env.clauses_temp

let trail () = env.trail

