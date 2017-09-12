(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

open Solver_types
module Fmt = CCFormat

type proof = Proof.t

exception Sat
exception Unsat
exception UndecidedLit
exception Restart
exception Conflict of clause

(* Log levels *)
let error = 1
let warn = 3
let info = 5
let debug = 15

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

  services: Service.Registry.t;
  (* services *)

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
  (* Clauses that should propagate at level 0, but couldn't because they were
     added at higher levels *)

  clauses_to_add : clause Stack.t;
  (* Clauses either assumed or pushed by the theory, waiting to be added. *)

  actions: actions lazy_t;
  (* set of actions available to plugins, pre-allocated *)

  mutable unsat_conflict : clause option;
  (* conflict clause at [base_level], if any *)
  mutable next_decision : atom option;
  (* When the last conflict was a semantic one, this stores the next decision to make *)

  trail : term Vec.t;
  (* main stack containing assignments (either decisions or propagations) *)

  decision_levels : level Vec.t;
  (* decision levels in [trail]  *)

  backtrack_stack : (unit -> unit) Vec.t Vec.t;
  (* one set of undo actions for every decision level *)
  (* TODO: do the same as {!trail} instead? i.e. unsorted vector of
     [(int,unit->unit)] + side vector for offsets, and do the same
     kind of moving trick during backtracking? *)

  user_levels : level Vec.t;
  (* user levels in [clauses_temp] *)

  dirty_terms: term Vec.t;
  (* set of terms made dirty by backtracking, whose [decide_state]
     must potentially be updated *)

  mutable elt_head : int;
  (* Start offset in the queue {!trail} of
     unit facts to propagate, within the trail.
     The slice between {!elt_head} and the end of {!trail} has not yet been
     boolean-propagated. *)

  mutable th_head : int;
  (* Start offset in the queue {!trail} of
     unit facts not yet seen by the theory.
     The slice between {!th_head} and the end of {!trail} has not yet
     been seen by the plugins *)

  (* invariant:
     - elt_head <= length trail
     - th_eval <= length trail
     - propagation does a block of BCP, then a block of theory,
       alternatively. Full BCP/theory propagation occurs before yielding
       control to the other.
     - theory propagation is done by calling terms' [update_watches]
       functions for every term on the trail after {!th_head},
       until {!th_head} can catch up with length of {!trail}
     - this is repeated until a fixpoint is reached;
     - before a decision (and after the fixpoint),
       th_head = elt_head = length trail
  *)

  term_heap : H.t;
  (* Heap ordered by variable activity *)

  var_decay : float;
  (* inverse of the activity factor for variables. Default 1/0.999 *)
  clause_decay : float;
  (* inverse of the activity factor for clauses. Default 1/0.95 *)

  seen_tmp : term Vec.t;
  (* temporary vector used during conflict analysis.
     Contains terms marked during analysis, to be unmarked at cleanup *)

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


  mutable learntsize_factor : float;
  (* initial limit for the number of learnt clauses, as a factor of initial
     number of clauses *)
  learntsize_inc : float;
  (* multiplicative factor for [learntsize_factor] at each restart *)

  mutable starts : int; (* number of (re)starts *)
  mutable decisions : int; (* number of decisions *)
  mutable propagations : int; (* number of propagations *)
  mutable conflicts : int; (* number of conflicts *)
  mutable n_learnt : int; (* total number of clauses learnt *)
  mutable n_gc: int; (* number of rounds of GC *)
  mutable n_deleted: int; (* number of deleted clauses *)
  mutable nb_init_clauses : int;
}

(** {2 Print} *)

(* obtain the plugin with this ID *)
let[@inline] get_plugin (env:t) (p_id:plugin_id) : Plugin.t =
  try CCVector.get env.plugins p_id
  with _ ->
    Log.debugf error (fun k->k "cannot find plugin %d" p_id);
    assert false

let[@inline] plugin_of_term (env:t) (t:term) : Plugin.t =
  get_plugin env (Term.plugin_id t)

let[@inline] plugins t = t.plugins
let[@inline] actions t = Lazy.force t.actions

(* Misc functions *)
let[@inline] to_float i = float_of_int i
let[@inline] to_int f = int_of_float f

let[@inline] nb_clauses env = Vec.size env.clauses_hyps
(* let nb_vars    () = St.nb_elt () *)
let[@inline] decision_level env = Vec.size env.decision_levels
let[@inline] base_level env = Vec.size env.user_levels

let[@inline] services env = env.services
let[@inline] plugins env = CCVector.to_seq env.plugins
let[@inline] get_service env (k:_ Service.Key.t) =
  Service.Registry.find env.services k

let[@inline] get_service_exn env (k:_ Service.Key.t) =
  Service.Registry.find_exn env.services k

(* how to add a plugin *)
let add_plugin (env:t) (fcty:Plugin.Factory.t) : Plugin.t =
  let id = CCVector.length env.plugins |> Term.Unsafe.mk_plugin_id in
  (* find services throught the list of keys *)
  let rec find_services
    : type a. a Plugin.service_key_list -> a Plugin.service_list
    = function
      | Plugin.K_nil -> Plugin.S_nil
      | Plugin.K_cons (k, tail) ->
        begin match get_service env k with
          | None ->
            Util.errorf "could not find service `%s`" (Service.Key.name k)
          | Some serv ->
            Plugin.S_cons (k, serv, find_services tail)
        end
  in
  let Plugin.Factory.Factory {requires; build; _} = fcty in
  let serv_list = find_services requires in
  let p = build id serv_list in
  CCVector.push env.plugins p;
  Log.debugf info (fun k->k "add plugin %s with ID %d" (Plugin.name p) id);
  let (module P) = p in
  List.iter
    (fun (Service.Any (k,s)) -> Service.Registry.register env.services k s)
    P.provided_services;
  p

(* Are the assumptions currently unsat ? *)
let[@inline] is_unsat t = match t.unsat_conflict with
  | Some _ -> true
  | None -> false

(* iterate on all active terms *)
let[@inline] iter_terms (env:t) : term Sequence.t =
  CCVector.to_seq env.plugins
  |> Sequence.flat_map
    (fun (module P : Plugin.S) -> P.iter_terms)
  |> Sequence.filter Term.has_var

let[@inline] term_init (env:t) (t:term) : unit =
  t.t_tc.tct_init (actions env) t

(* provision term (and its sub-terms) for future assignments.
   This is the function exposed to users and therefore it performs some checks. *)
let rec add_term (env:t) (t:term): unit =
  if Term.is_deleted t then (
    Util.errorf "(@[trying to add deleted term@ `%a`@])" Term.debug t
  ) else if Term.is_added t then (
    assert (Term.has_var t);
  ) else (
    Log.debugf 15 (fun k->k"(@[solver.add_term %a@])" Term.debug t);
    Term.field_set field_t_is_added t;
    Term.setup_var t;
    Term.iter_subterms t (add_term env); (* add subterms, recursively *)
    H.insert env.term_heap t; (* add to priority queue for decision *)
    term_init env t; (* setup watches, possibly propagating already *)
  )

let[@inline] add_atom (env:t) (a:atom) : unit = add_term env (Atom.term a)

(* put [t] in the heap of terms to decide *)
let[@inline] schedule_decision_term (env:t) (t:term): unit =
  H.insert env.term_heap t

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
    H.decrease env.term_heap t
  )

(* increase activity of var [t] *)
let[@inline] bump_term_activity env (t:term): unit =
  bump_term_activity_aux env t;
  Term.iter_subterms t (bump_term_activity_aux env)

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

(* make a decision for [t] based on its type *)
let[@inline] decide_term (env:t) (t:term): value =
  Type.decide (Term.ty t) (actions env) t

(* main building function *)
let create_real (actions:actions lazy_t) : t = {
  unsat_conflict = None;
  next_decision = None;

  plugins = CCVector.create();
  services = Service.Registry.create();
  actions;

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
  dirty_terms = Vec.make 50 dummy_term;
  seen_tmp = Vec.make 10 dummy_term;

  term_heap = H.create();

  var_incr = 1.;
  clause_incr = 1.;
  var_decay = 1. /. 0.95;
  clause_decay = 1. /. 0.999;

  remove_satisfied = false;

  restart_inc = 1.5;
  restart_first = 100;

  learntsize_factor = 1.5 ; (* can learn 3× as many clauses as present initially *)
  learntsize_inc = 1.2; (* 1.3× more learnt clauses after each restart *)

  starts = 0;
  decisions = 0;
  propagations = 0;
  conflicts = 0;
  n_learnt=0;
  n_gc=0;
  n_deleted=0;
  nb_init_clauses = 0;
}

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
let[@inline] arr_to_list arr i : _ list =
  if i >= Array.length arr then []
  else Array.to_list (Array.sub arr i (Array.length arr - i))

(* Eliminates atom duplicates in clauses.
   returns [true] if something changed. *)
let eliminate_duplicates (clause:clause) : clause * bool =
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
    Clause.make !res (Simplify clause), true
  )

(* Partition literals for new clauses, into:
   - true literals (maybe makes the clause trivial if the lit is proved true at level 0)
   - unassigned literals, yet to be decided
   - false literals (not suitable to watch, those at level 0 can be removed from the clause)

   Then, true literals are put first, then unassigned ones, then false ones.
   This is suitable for watching the resulting clause.

   Clauses that propagated false lits are remembered,
   to reconstruct resolution proofs.

   precondition: clause does not contain duplicates
*)
let partition_atoms (atoms:atom array) : atom list * clause list =
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
          begin match Term.reason a.a_term with
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

(* no propagation needed *)
let[@inline] fully_propagated (env:t) : bool =
  env.th_head = Vec.size env.trail &&
  env.elt_head = Vec.size env.trail

(* Making a decision.
   Before actually creatig a new decision level, we check that all propagations
   have been done and propagated to the theory, i.e that the theoriy state
   indeed takes into account the whole stack of literals, i.e we have indeed
   reached a propagation fixpoint before making a new decision *)
let new_decision_level (env:t) : unit =
  assert (fully_propagated env);
  Vec.push env.decision_levels (Vec.size env.trail);
  Vec.push env.backtrack_stack (Vec.make_empty (fun _ -> ()));
  ()

(* Attach/Detach a clause.
   A clause is attached (to its watching lits) when it is first added,
   either because it is assumed or learnt.
*)
let attach_clause (_env:t) (c:clause): unit =
  if not (Clause.attached c) then (
    Log.debugf debug (fun k -> k "Attaching %a" Clause.debug c);
    Vec.push (Atom.neg c.c_atoms.(0)).a_watched c;
    Vec.push (Atom.neg c.c_atoms.(1)).a_watched c;
    Clause.set_attached c;
  )

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
    Log.debugf info (fun k -> k "@{<Yellow>### Backtracking@} to lvl %d" lvl);
    (* We set the head of the solver and theory queue to what it was. *)
    let top = Vec.get env.decision_levels lvl in
    let head = ref top in
    (* Now we need to cleanup the vars that are not valid anymore
       (i.e to the right of elt_head in the queue).
       We do it left-to-right because that makes it easier to move
       elements whose level is actually lower than [lvl], by just
       moving them to [!head]. *)
    for i = top to Vec.size env.trail - 1 do
      (* A variable is unassigned, we nedd to add it back to
         the heap of potentially assignable variables, unless it has
         a level lower than [lvl], in which case we just move it back. *)
      let t = Vec.get env.trail i in
      if Term.level t <= lvl then (
        Vec.set env.trail !head t;
        head := !head + 1;
      ) else (
        t.t_level <- -1;
        t.t_value <- TA_none;
        schedule_decision_term env t;
      )
    done;
    (* elements we kept are already propagated, update pointers accordingly *)
    env.elt_head <- !head;
    env.th_head <- !head;
    (* Resize the vectors according to their new size. *)
    Vec.shrink env.trail !head;
    Vec.shrink env.decision_levels lvl;
    (* call undo-actions registered by plugins *)
    while Vec.size env.backtrack_stack > lvl do
      let v = Vec.last env.backtrack_stack in
      Vec.iter (fun f -> f()) v;
      Vec.pop env.backtrack_stack;
    done;
    (* refresh dirty variables *)
    let lvl = decision_level env in
    Vec.iter
      (fun t -> Term.dirty_unmark t; Term.recompute_state lvl t)
      env.dirty_terms;
    Vec.clear env.dirty_terms;
  );
  assert (Vec.size env.decision_levels = Vec.size env.backtrack_stack);
  ()

(* Unsatisfiability is signaled through an exception, since it can happen
   in multiple places (adding new clauses, or solving for instance). *)
let report_unsat (env:t) (confl:clause) : _ =
  Log.debugf info (fun k -> k "@[Unsat conflict: %a@]" Clause.debug confl);
  env.unsat_conflict <- Some confl;
  raise Unsat

(* Simplification of boolean propagation reasons {b at level 0}.
   When doing boolean propagation at level 0, it can happen
   that the clause cl, which propagates a formula, also contains
   other formulas, but has been simplified. in which case, we
   need to rebuild a clause with correct history, in order to
   be able to build a correct proof at the end of proof search. *)
let simpl_reason_level_0 : reason -> reason = function
  | (Bcp cl) as r ->
    let l, history = partition_atoms cl.c_atoms in
    begin match l with
      | [_] ->
        (* now the clause is unit, we should simplify it explicitly *)
        if history = [] then r
        (* no simplification has been done, so [cl] is actually a clause with only
               [a], so it is a valid reason for propagating [a]. *)
        else (
          (* Clauses in [history] have been used to simplify [cl] into a clause [tmp_cl]
             with only one formula (which is [a]). So we explicitly create that clause
             and set it as the cause for the propagation of [a], that way we can
             rebuild the whole resolution tree when we want to prove [a]. *)
          let c' =
            Clause.make l (Premise.hyper_res (cl :: history))
          in
          Log.debugf debug
            (fun k -> k "(@[simplified_reason@ :from %a@ :to %a@])"
                Clause.debug cl Clause.debug c');
          Bcp c'
        )
      | _ ->
        Util.errorf
          "(@[simpl_reason_level_0.fail@ :simp-atoms %a@ :bcp-from %a@])"
          Clause.debug_atoms l Clause.debug cl
    end
  | r -> r

(* Boolean propagation.
   Wrapper function for adding a new propagated formula. *)
let enqueue_bool (env:t) (a:atom) ~level:lvl (reason:reason) : unit =
  if Atom.is_false a then (
    Util.errorf "Trying to enqueue a false literal: %a" Atom.debug a
  );
  Log.debugf 15 (fun k->k "(@[enqueue_bool %a@ :reason %a@])"
      Atom.debug a Reason.pp (lvl,reason));
  assert (not (Atom.is_true a) && Atom.level a < 0 &&
          Atom.reason a = None && lvl >= 0);
  (* simplify reason *)
  let reason =
    if lvl > 0 then reason
    else simpl_reason_level_0 reason
  in
  (* assign term *)
  let value = Value.of_bool (Atom.is_pos a) in
  a.a_term.t_value <- TA_assign{value;reason};
  a.a_term.t_level <- lvl;
  Vec.push env.trail a.a_term;
  env.propagations <- env.propagations + 1;
  Log.debugf debug
    (fun k->k "Enqueue (%d/%d): %a" (Vec.size env.trail)(decision_level env) Atom.debug a);
  ()

(* atom [a] evaluates to [true] because of [terms] *)
let enqueue_semantic_bool_eval (env:t) (a:atom) (terms:term list) : unit =
  if Atom.is_true a then ()
  else (
    assert (List.for_all Term.is_added terms);
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
let enqueue_assign (env:t) (t:term) (value:value) (reason:reason) (lvl:int) : unit =
  if Term.has_value t then (
    Log.debugf error
      (fun k -> k "Trying to assign an already assigned literal: %a" Term.debug t);
    assert false
  );
  assert (t.t_level < 0);
  t.t_value <- TA_assign {value;reason};
  t.t_level <- lvl;
  Vec.push env.trail t;
  Log.debugf debug
    (fun k->k "Enqueue (%d/%d): %a" (Vec.size env.trail)(decision_level env) Term.debug t);
  ()

(* evaluate an atom for MCsat, if it's not assigned
   by boolean propagation/decision *)
let th_eval (env:t) (a:atom) : bool option =
  if Atom.is_true a || Atom.is_false a then None
  else (
    begin match Term.eval_bool a.a_term with
      | Eval_unknown -> None
      | Eval_bool (b, l) ->
        let atom = if b then a else Atom.neg a in
        enqueue_semantic_bool_eval env atom l;
        Some b
    end
  )

(* find which level to backtrack to, given a conflict clause
   and a boolean stating whether it is a UIP ("Unique Implication Point")
   precondition: the atoms with highest decision level are first in the array *)
let backtrack_lvl (env:t) (a:atom array) : int * bool =
  if Array.length a <= 1 then (
    0, true (* unit or empty clause *)
  ) else (
    assert (Atom.level a.(0) > base_level env);
    if Atom.level a.(0) > Atom.level a.(1) then (
      (* backtrack below [a], so we can propagate [not a] *)
      Atom.level a.(1), true
      (* NOTE: (to explore)
         since we can propagate at level [a.(1).level] wherever we want
         we might also want to backtrack at [a.(0).level-1] but still
         propagate [¬a.(0)] at a lower level? That would save current decisions *)
    ) else (
      (* semantic split *)
      assert (Atom.level a.(0) = Atom.level a.(1));
      assert (Atom.level a.(0) >= base_level env);
      max (Atom.level a.(0) - 1) (base_level env), false
    )
  )

(* move atoms assigned at high levels first *)
let[@inline] put_high_level_atoms_first (arr:atom array) : unit =
  Array.iteri
    (fun i a ->
       if i>0 && Atom.level a > Atom.level arr.(0) then (
         (* move first to second, [i]-th to first, second to [i] *)
         let tmp = arr.(1) in
         arr.(1) <- arr.(0);
         arr.(0) <- arr.(i);
         if i>1 then (
           arr.(i) <- tmp;
         );
       ) else if i>1 && Atom.level a > Atom.level arr.(1) then (
         Util.swap_arr arr 1 i;
       ))
    arr

(* result of conflict analysis, containing the learnt clause and some
   additional info.

   invariant: cr_history's order matters, as its head is later used
   during pop operations to determine the origin of a clause/conflict
   (boolean conflict i.e hypothesis, or theory lemma) *)
type conflict_res = {
  cr_backtrack_lvl : int; (* level to backtrack to *)
  cr_learnt: atom array; (* lemma learnt from conflict *)
  cr_history: clause list; (* justification *)
  cr_is_uip: bool; (* conflict is UIP? *)
  cr_confl : clause; (* original conflict clause *)
}

(* Conflict analysis for MCSat, looking for the last UIP
   (Unique Implication Point) in an efficient imperative manner.
   We do not really perform a series of resolution, but just keep enough
   information for proof reconstruction.
*)
let analyze_conflict (env:t) (c_clause:clause) : conflict_res =
  let pathC = ref 0 in (* number of literals >= conflict level. *)
  let learnt = ref [] in (* the resulting clause to be learnt *)
  let continue = ref true in (* used for termination of loop *)
  let seen  = env.seen_tmp in (* terms marked during analysis, to be unmarked at cleanup *)
  let c = ref (Some c_clause) in (* current clause to do (hyper)resolution on *)
  let tr_ind = ref (Vec.size env.trail - 1) in (* pointer in trail. starts at top, only goes down. *)
  let history = ref [] in (* proof object *)
  assert (decision_level env > 0);
  Vec.clear env.seen_tmp;
  let conflict_level =
    (Array.fold_left[@inlined])
      (fun acc p -> max acc (Atom.level p)) 0 c_clause.c_atoms
  in
  Log.debugf debug
    (fun k -> k "(@[analyze_conflict (%d/%d)@ :conflict %a@])"
        conflict_level (decision_level env) Clause.debug c_clause);
  assert (conflict_level >= 0);
  (* now loop until there is either:
     - the clause is empty (found unsat)
     - one decision term with level strictly greater than the other
       terms level (the UIP)
     - all terms at maximal level are semantic propagations ("semantic split")

     as long as this is not reached, we pick the highest (propagated)
     literal of the clause and do resolution with the clause that
     propagated it. Note that there cannot be two decision literals
     above the conflict_level.

     [pathC] is used to count how many literals are on top level and is
     therefore central for termination.
  *)
  while !continue do
    (* if we have a clause, do resolution on it by marking all its
       literals that are not "seen" yet. *)
    begin match !c with
      | None ->
        Log.debug debug "skipping resolution for semantic propagation"
      | Some clause ->
        Log.debugf debug
          (fun k->k "(@[analyze_conflict.resolving@ :clause %a@])" Clause.debug clause);
        (* increase activity since [c] participates in a conflict *)
        begin match clause.c_premise with
          | Hyper_res _ -> bump_clause_activity env clause
          | Hyp | Local | Simplify _ | Lemma _ -> ()
        end;
        history := clause :: !history;
        (* visit the current predecessors *)
        for j = 0 to Array.length clause.c_atoms - 1 do
          let q = clause.c_atoms.(j) in
          assert (Atom.is_true q || Atom.is_false q && Atom.level q >= 0); (* unsure? *)
          if Atom.level q <= 0 then (
            (* must be a 0-level propagation *)
            assert (Atom.level q=0);
            begin match Atom.reason q with
              | Some (Bcp cl) -> history := cl :: !history
              | _ -> assert false
            end
          );
          (* if we have not explored this atom yet, do it now.
             It can either be part of the final clause, or it can lead
             to resolution with another clause *)
          if not (Term.marked q.a_term) then (
            Term.mark q.a_term;
            Vec.push seen q.a_term;
            if Atom.level q > 0 then (
              bump_term_activity env q.a_term;
              if Atom.level q >= conflict_level then (
                incr pathC;
              ) else (
                (* [q] will be part of the learnt clause *)
                learnt := q :: !learnt;
              )
            )
          )
        done
    end;

    (* look for the next node to expand by going down the trail *)
    while
      let t = Vec.get env.trail !tr_ind in
      Log.debugf 30 (fun k -> k "(@[conflict_analyze.at_trail_elt@ %a@])" Term.debug t);
      begin match t.t_var with
        | Var_none -> assert false
        | Var_semantic _ -> true (* skip semantic assignments *)
        | Var_bool _ ->
          (* skip a term if:
             - it is not marked (not part of resolution), OR
             - below conflict level
          *)
          not (Term.marked t) || Term.level t < conflict_level
      end
    do
      decr tr_ind;
    done;
    (* now [t] is the term to analyze. *)
    let t = Vec.get env.trail !tr_ind in
    let p = Term.Bool.assigned_atom_exn t in
    (* [t] will not be part of the learnt clause, let's decrease [pathC] *)
    decr pathC;
    decr tr_ind;
    let reason = Term.reason_exn t in
    Log.debugf 30
      (fun k->k"(@[<hv>conflict_analyze.check_done:@ %a@ :pathC %d@ :reason %a@])"
          Term.debug t !pathC Reason.pp (Term.level t,reason));
    begin match !pathC, reason with
      | 0, _ ->
        (* [t] is the UIP, or we have a semantic split *)
        continue := false;
        learnt := Atom.neg p :: !learnt
      | n, Semantic _ ->
        assert (n > 0);
        learnt := Atom.neg p :: !learnt;
        c := None
      | n, Bcp cl ->
        assert (n > 0);
        assert (Atom.level p >= conflict_level);
        c := Some cl
      | _ -> assert false
    end
  done;
  Vec.iter Term.unmark env.seen_tmp;
  Vec.clear env.seen_tmp;
  (* put high level atoms first *)
  let learnt_a = Array.of_list !learnt in
  put_high_level_atoms_first learnt_a;
  let level, is_uip = backtrack_lvl env learnt_a in
  { cr_backtrack_lvl = level;
    cr_learnt = learnt_a;
    cr_history = List.rev !history;
    cr_is_uip = is_uip;
    cr_confl = c_clause;
  }

(* add the learnt clause to the clause database, propagate, etc. *)
let record_learnt_clause (env:t) (cr:conflict_res): unit =
  begin match cr.cr_learnt with
    | [||] -> assert false
    | [|fuip|] ->
      assert (cr.cr_backtrack_lvl = 0);
      env.n_learnt <- env.n_learnt + 1;
      if Atom.is_false fuip then (
        report_unsat env cr.cr_confl
      ) else (
        let uclause =
          Clause.make_arr cr.cr_learnt (Premise.hyper_res cr.cr_history)
        in
        Vec.push env.clauses_learnt uclause;
        Log.debugf debug (fun k->k "(@[learn_clause_0:@ %a@])" Clause.debug uclause);
        (* no need to attach [uclause], it is true at level 0 *)
        enqueue_bool env fuip ~level:0 (Bcp uclause)
      )
    | c_learnt ->
      let fuip = c_learnt.(0) in
      let premise = match cr.cr_history with
        | [] -> assert false
        | [c] -> Simplify c
        | l -> Premise.hyper_res l
      in
      let lclause = Clause.make_arr c_learnt premise in
      Vec.push env.clauses_learnt lclause;
      env.n_learnt <- env.n_learnt + 1;
      Log.debugf debug (fun k->k "(@[learn_clause:@ %a@])" Clause.debug lclause);
      attach_clause env lclause;
      bump_clause_activity env lclause;
      if cr.cr_is_uip then (
        enqueue_bool env fuip ~level:cr.cr_backtrack_lvl (Bcp lclause)
      ) else (
        (* semantic split: pick negation of one of top-level lits *)
        env.next_decision <- Some (Atom.neg fuip)
      )
  end;
  var_decay_activity env;
  clause_decay_activity env

(* process a conflict:
   - learn clause
   - backtrack
   - report unsat if conflict at level 0
*)
let add_conflict (env:t) (confl:clause): unit =
  Log.debugf info (fun k -> k"@{<Yellow>## add_conflict@}: %a" Clause.debug confl);
  env.next_decision <- None;
  env.conflicts <- env.conflicts + 1;
  assert (decision_level env >= base_level env);
  if decision_level env = base_level env ||
     CCArray.for_all
       (fun a -> Atom.level a <= base_level env)
       confl.c_atoms
  then (
    report_unsat env confl; (* Top-level conflict *)
  );
  let cr = analyze_conflict env confl in
  cancel_until env (max cr.cr_backtrack_lvl (base_level env));
  record_learnt_clause env cr

(* Get the correct vector to insert a clause in. *)
let clause_vector env c = match c.c_premise with
  | Hyp -> env.clauses_hyps
  | Local -> env.clauses_temp
  | Lemma _ | Simplify _ | Hyper_res _ -> env.clauses_learnt

(* Add a new clause, simplifying, propagating, and backtracking if
   the clause is false in the current trail *)
let add_clause (env:t) (init:clause) : unit =
  Log.debugf debug (fun k -> k "Adding clause: @[<hov>%a@]" Clause.debug init);
  (* Insertion of new lits is done before simplification. Indeed, else a lit in a
     trivial clause could end up being not decided on, which is a bug. *)
  Array.iter (fun a -> add_term env a.a_term) init.c_atoms;
  let vec = clause_vector env init in
  try
    let c, has_dedup = eliminate_duplicates init in
    if has_dedup then (
      Log.debugf debug
        (fun k -> k "Doublons eliminated:@ %a@ :from %a" Clause.debug c Clause.debug init);
    );
    let atoms, history = partition_atoms c.c_atoms in
    let clause =
      if history = []
      then (
        (* update order of atoms *)
        List.iteri (fun i a -> c.c_atoms.(i) <- a) atoms;
        c
      ) else (
        Clause.make atoms (Premise.hyper_res (c :: history))
      )
    in
    Log.debugf info (fun k->k "@{<green>New clause@}: @[<hov>%a@]" Clause.debug clause);
    begin match atoms with
      | [] ->
        (* Report_unsat will raise, and the current clause will be lost if we do not
           store it somewhere. Since the proof search will end, any of env.clauses_to_add
           or env.clauses_root is adequate. *)
        Stack.push clause env.clauses_root;
        report_unsat env clause
      | [a]   ->
        cancel_until env (base_level env);
        if Atom.is_false a then (
          (* Since we cannot propagate the atom [a], in order to not lose
             the information that [a] must be true, we add clause to the list
             of clauses to add, so that it will be e-examined later. *)
          Log.debug debug "Unit clause, adding to clauses to add";
          Stack.push clause env.clauses_to_add;
          report_unsat env clause
        ) else if Atom.is_true a then (
          (* If the atom is already true, then it should be because of a local hyp.
             However it means we can't propagate it at level 0. In order to not lose
             that information, we store the clause in a stack of clauses that we will
             add to the solver at the next pop. *)
          Log.debug debug "Unit clause, adding to root clauses";
          assert (0 < Atom.level a && Atom.level a <= base_level env);
          Stack.push clause env.clauses_root;
          ()
        ) else (
          Log.debugf debug (fun k->k "Unit clause, propagating: %a" Atom.debug a);
          Vec.push vec clause;
          enqueue_bool env a ~level:0 (Bcp clause)
        )
      | a::b::_ ->
        Vec.push vec clause;
        if Atom.is_false a then (
          (* put the two atoms with highest decision level at the beginning
             of the clause, so that watch literals are always fine *)
          let ats = clause.c_atoms in
          put_high_level_atoms_first ats;
          assert(Atom.level ats.(0) >= Atom.level ats.(1));
          attach_clause env clause;
          add_conflict env clause
        ) else (
          attach_clause env clause;
          if Atom.is_false b && Atom.is_undef a then (
            let lvl = List.fold_left (fun m a -> max m (Atom.level a)) 0 atoms in
            cancel_until env (max lvl (base_level env));
            enqueue_bool env a ~level:lvl (Bcp clause)
          )
        )
    end
  with Trivial ->
    Vec.push vec init;
    Log.debugf info (fun k->k "Trivial clause ignored : @[%a@]" Clause.debug init)

(* really add clauses pushed by plugins to the solver *)
let flush_clauses (env:t) =
  if not (Stack.is_empty env.clauses_to_add) then (
    let nbc = env.nb_init_clauses + Stack.length env.clauses_to_add in
    Vec.grow_to_at_least env.clauses_hyps nbc;
    Vec.grow_to_at_least env.clauses_learnt nbc;
    env.nb_init_clauses <- nbc;
    while not (Stack.is_empty env.clauses_to_add) do
      let c = Stack.pop env.clauses_to_add in
      add_clause env c
    done
  )

(* boolean propagation.
   [a] is the false atom, one of [c]'s two watch literals
   [i] is the index of [c] in [a.watched]
   @return whether [c] was removed from [a.watched]
*)
let propagate_in_clause (env:t) (a:atom) (c:clause) : watch_res =
  let atoms = c.c_atoms in
  let first = atoms.(0) in
  if first == Atom.neg a then (
    (* false lit must be at index 1 *)
    atoms.(0) <- atoms.(1);
    atoms.(1) <- first
  ) else (
    assert (Atom.neg a == atoms.(1));
  );
  let first = atoms.(0) in
  if Atom.is_true first
  then Watch_keep (* true clause, keep it in watched *)
  else (
    try (* look for another watch lit *)
      for k = 2 to Array.length atoms - 1 do
        let ak = atoms.(k) in
        if not (Atom.is_false ak) then (
          (* watch lit found: update and exit *)
          atoms.(1) <- ak;
          atoms.(k) <- Atom.neg a;
          (* remove [c] from [a.watched], add it to [ak.neg.watched] *)
          Vec.push (Atom.neg ak).a_watched c;
          raise Exit
        )
      done;
      (* no watch lit found *)
      if Atom.is_false first then (
        (* clause is false *)
        env.elt_head <- Vec.size env.trail;
        raise (Conflict c)
      ) else (
        begin match th_eval env first with
          | None -> (* clause is unit, keep the same watches, but propagate *)
            enqueue_bool env first ~level:(decision_level env) (Bcp c)
          | Some true -> ()
          | Some false ->
            env.elt_head <- Vec.size env.trail;
            raise (Conflict c)
        end
      );
      Watch_keep
    with Exit ->
      Watch_remove
  )

(* propagate atom [a], which was just decided. This checks every
   clause watching [a] to see if the clause is false, unit, or has
   other possible watches
   @param res the optional conflict clause that the propagation might trigger *)
let propagate_atom (env:t) (a:atom) : unit =
  let watched = a.a_watched in
  let i = ref 0 in
  while !i < Vec.size watched do
    let c = Vec.get watched !i in
    assert (Clause.attached c);
    if Clause.deleted c
    then Vec.fast_remove watched !i (* remove *)
    else begin match propagate_in_clause env a c with
      | Watch_keep -> incr i
      | Watch_remove ->
        Vec.fast_remove watched !i;
        (* remove clause [c] from watches, then look again at [!i]
           since it's now another clause *)
    end
  done

(* [t] is watching [watch], which has been assigned *)
let[@inline] propagate_in_watching_term (env:t) (t:term) ~watch =
  t.t_tc.tct_update_watches (actions env) t ~watch

(* propagate in every term that watches [t] *)
let propagate_term (env:t) (t:term): unit =
  let lazy watched = t.t_watches in
  let i = ref 0 in
  while !i < Vec.size watched do
    let u = Vec.get watched !i in
    assert (Term.is_added u);
    if Term.is_deleted u
    then Vec.fast_remove watched !i
    else begin match propagate_in_watching_term env u ~watch:t with
      | Watch_keep -> incr i
      | Watch_remove ->
        Vec.fast_remove watched !i;
        (* remove [u] from terms watching [t];
           inspect [!i] again since it's now another term *)
    end
  done

let debug_eval_bool out = function
  | Eval_unknown -> Fmt.string out "unknown"
  | Eval_bool (b, subs) ->
    Fmt.fprintf out "(@[<hv>%B@ :subs (@[%a@])@])" b (Util.pp_list Term.debug) subs

(* some terms were decided/propagated. Now we
   need to inform the plugins about these assignments, so they can do their job.
   @return the conflict clause, if a plugin detects unsatisfiability *)
let rec theory_propagate (env:t) : clause option =
  assert (env.elt_head <= Vec.size env.trail);
  if env.th_head = Vec.size env.trail then (
    if env.elt_head = Vec.size env.trail then (
      None (* fixpoint reached for both theory propagation and BCP *)
    ) else (
      propagate env (* need to do BCP *)
    )
  ) else (
    (* consider one element *)
    let t = Vec.get env.trail env.th_head in
    env.th_head <- env.th_head + 1;
    (* notify all terms watching [t] to perform semantic propagation *)
    begin match propagate_term env t with
      | () -> theory_propagate env (* next propagation *)
      | exception (Conflict c) -> Some c (* conflict *)
    end
  )

(* Boolean propagation.
   @return a conflict clause, if any *)
and bool_propagate (env:t) : clause option =
  if env.elt_head = Vec.size env.trail then (
    theory_propagate env (* BCP done, now notify plugins *)
  ) else (
    let t = Vec.get env.trail env.elt_head in
    env.elt_head <- env.elt_head + 1;
    (* propagate [t], if boolean *)
    begin match t.t_var with
      | Var_none -> assert false
      | Var_semantic _ -> bool_propagate env
      | Var_bool _ ->
        env.propagations <- env.propagations + 1;
        (* propagate the atom that has been assigned to [true] *)
        let a = Term.Bool.assigned_atom_exn t in
        begin match propagate_atom env a with
          | () -> bool_propagate env (* next propagation *)
          | exception Conflict c -> Some c (* conflict *)
        end
    end
  )

(* Fixpoint between boolean propagation and theory propagation.
   Does BCP first.
   @return a conflict clause, if any *)
and propagate (env:t) : clause option =
  (* First, treat the stack of lemmas added by the theory, if any *)
  flush_clauses env;
  (* Now, check that the situation is sane *)
  assert (env.elt_head <= Vec.size env.trail);
  bool_propagate env

(* [a] is part of a conflict/learnt clause, but might not be evaluated yet.
   Evaluate it, save its value, and ensure it is indeed false. *)
let eval_atom_to_false (env:t) (a:atom): unit =
  if Atom.has_value a then (
    assert (Atom.is_false a);
  ) else (
    let v = Term.eval_bool a.a_term in
    Log.debugf debug (fun k->k "(@[atom_must_be_false@ %a@ :eval_to %a@])"
        Atom.debug a debug_eval_bool v);
    begin match v, Atom.is_pos a with
      | Eval_bool (false, subs), true
      | Eval_bool (true, subs), false ->
        enqueue_semantic_bool_eval env (Atom.neg a) subs
      | _ -> assert false
    end
  )

(* build the "actions" available to the plugins *)
let mk_actions (env:t) : actions =
  let act_on_backtrack lev f : unit =
    if lev=0 then () (* never do it *)
    else if lev > decision_level env then f()
    else (
      Vec.push (Vec.get env.backtrack_stack (lev-1)) f
    )
  and act_level (): level = decision_level env
  and act_push_clause (c:clause) : unit =
    Log.debugf debug (fun k->k "Pushing clause %a" Clause.debug c);
    Stack.push c env.clauses_to_add
  and act_raise_conflict (type a) (atoms:atom list) (lemma:lemma): a =
    Log.debugf debug (fun k->k
        "(@[<hv>raise_conflict@ :clause %a@ :lemma %a@])"
        Clause.debug_atoms atoms Lemma.pp lemma);
    env.elt_head <- Vec.size env.trail;
    (* add atoms, also evaluate them if not already false *)
    List.iter
      (fun a ->
         add_atom env a;
         eval_atom_to_false env a)
      atoms;
    let c = Clause.make atoms (Lemma lemma) in
    raise (Conflict c)
  and act_propagate_bool t (b:bool) ~(subs:term list) : unit =
    Log.debugf debug
      (fun k->k "(@[<hv>Semantic propagate %a@ :val %B@ :subs (@[<hv>%a@])@])"
        Term.debug t b (Util.pp_list Term.debug) subs);
    let a = if b then Term.Bool.pa_unsafe t else Term.Bool.na_unsafe t in
    enqueue_semantic_bool_eval env a subs
  and act_mark_dirty (t:term): unit =
    if not (Term.dirty t) then (
      Log.debugf debug (fun k->k "(@[Mark dirty@ %a@])" Term.debug t);
      Term.dirty_mark t;
      Vec.push env.dirty_terms t;
    )
  in
  { act_on_backtrack;
    act_push_clause;
    act_mark_dirty;
    act_level;
    act_raise_conflict;
    act_propagate_bool;
  }

(* main constructor *)
let create () : t =
  let rec env = lazy (create_real actions)
  and actions = lazy (mk_actions (Lazy.force env)) in
  let env = Lazy.force env in
  (* add builtins *)
  ignore (add_plugin env Builtins.plugin);
  env

(* Decide on a new literal, and enqueue it into the trail *)
let rec pick_branch_aux (env:t) (atom:atom) : unit =
  let t = atom.a_term in
  if t.t_level >= 0 then (
    assert (not (Atom.is_undef atom));
    pick_branch_lit env
  ) else (
    (* does this boolean term eval to [true]? *)
    (* TODO: should the plugin already have propagated this?
       or is it an optim? *)
    begin match Term.eval_bool t with
      | Eval_unknown ->
        (* do a decision *)
        env.decisions <- env.decisions + 1;
        new_decision_level env;
        Log.debugf debug (fun k->k "(@[bool_decide@ %a@])" Atom.debug atom);
        let current_level = decision_level env in
        enqueue_bool env atom ~level:current_level Decision
      | Eval_bool (b, l) ->
        (* already evaluates in the trail *)
        let a = if b then atom else Atom.neg atom in
        enqueue_semantic_bool_eval env a l
    end
  )

and pick_branch_lit (env:t) : unit =
  begin match env.next_decision with
    | Some atom ->
      env.next_decision <- None;
      pick_branch_aux env atom
    | None ->
      (* look into the heap for the next decision *)
      if H.is_empty env.term_heap then (
        raise Sat (* full trail! *)
      ) else (
        (* pick some term *)
        let t = H.remove_min env.term_heap in
        if Term.is_deleted t then pick_branch_lit env (* try next *)
        else begin match t.t_var with
          | Var_none ->  assert false
          | Var_bool {pa; _} ->
            (* TODO: phase saving *)
            pick_branch_aux env pa
          | Var_semantic _ ->
            (* semantic decision, delegate to plugin *)
            if t.t_level >= 0 then (
              pick_branch_lit env (* assigned already *)
            ) else (
              let value = decide_term env t in
              env.decisions <- env.decisions + 1;
              new_decision_level env;
              let current_level = decision_level env in
              enqueue_assign env t value Decision current_level
            )
        end
      )
  end

(* remove some learnt clauses, and the terms that are not reachable from
   any clause.
   The number of learnt clauses after reduction must be [downto] *)
let reduce_db (env:t) ~down_to : unit =
  Log.debugf 2 (fun k->k"@{<Yellow>## reduce_db@}");
  assert (Stack.is_empty env.clauses_to_add);
  env.n_gc <- env.n_gc + 1;
  (* remove some clauses *)
  let n_clauses = Vec.size env.clauses_learnt in
  assert (down_to <= n_clauses);
  Log.debugf 4
    (fun k->k"(@[reduce_db.remove_learnt@ :n_total %d@ :downto %d@])" n_clauses down_to);
  (* sort learnt clauses by decreasing activity *)
  Vec.sort env.clauses_learnt
    (fun c1 c2 -> CCFloat.compare (Clause.activity c2)(Clause.activity c1));
  (* pop clauses *)
  while Vec.size env.clauses_learnt > down_to do
    let c = Vec.pop_last env.clauses_learnt in
    Log.debugf 15 (fun k->k"(@[reduce_db.remove_clause@ %a@ :activity %f@])"
        Clause.debug c (Clause.activity c));
    Clause.set_deleted c;
    env.n_deleted <- env.n_deleted + 1;
  done;
  (* mark alive terms, starting from alive clauses and from the trail *)
  Stack.iter Clause.gc_mark env.clauses_root;
  Vec.iter Clause.gc_mark env.clauses_hyps;
  Vec.iter Clause.gc_mark env.clauses_learnt;
  Vec.iter Clause.gc_mark env.clauses_temp;
  Vec.iter Term.gc_mark_rec env.trail;
  (* now collect terms *)
  CCVector.iter
    (fun (module P : Plugin.S) -> P.gc_all ())
    env.plugins;
  ()

(* do some amount of search, until the number of conflicts or clause learnt
   reaches the given parameters *)
let search (env:t) n_of_conflicts : unit =
  Log.debugf 5
    (fun k->k "(@[@{<yellow>search@}@ :nconflicts %d@])" n_of_conflicts);
  let conflictC = ref 0 in
  env.starts <- env.starts + 1;
  while true do
    begin match propagate env with
      | Some confl -> (* Conflict *)
        incr conflictC;
        attach_clause env confl;
        add_conflict env confl
      | None ->
        (* No conflict after propagation *)
        assert (env.elt_head = Vec.size env.trail);
        assert (env.elt_head = env.th_head);
        if H.is_empty env.term_heap then (
          raise Sat;
        );
        (* should we restart? *)
        if n_of_conflicts > 0 && !conflictC >= n_of_conflicts then (
          Log.debug info "Restarting...";
          cancel_until env (base_level env);
          raise Restart
        );
        (* if decision_level() = 0 then simplify (); *)

        (* next decision *)
        pick_branch_lit env
    end
  done

(* evaluate [a] and also return its level *)
let eval_level (a:atom) =
  let lvl = Atom.level a in
  if Atom.is_true a then true, lvl
  else if Atom.is_false a then false, lvl
  else (
    begin match Term.eval_bool a.a_term with
      | Eval_unknown -> raise UndecidedLit
      | Eval_bool (b, l) ->
        (* level is highest level of terms used to eval into [b] *)
        let lvl = List.fold_left (fun l t -> max l (Term.level t)) 0 l in
        if Atom.is_pos a then b, lvl else not b, lvl
    end
  )

let[@inline] eval a = fst (eval_level a)

let[@inline] unsat_conflict (env:t) = env.unsat_conflict

(* extract model *)
let model (env:t) : assignment_view list =
  Vec.fold
    (fun acc t -> match Term.value t with
       | TA_none -> assert false
       | TA_assign {value;_} ->
         let asgt = match Value.as_bool value with
           | Some b -> A_bool (t, b)
           | None -> A_semantic (t, value)
         in
         asgt :: acc )
    [] env.trail

type final_check_res =
  | FC_sat
  | FC_propagate
  | FC_conflict of clause

(* do the final check for plugins.
   returns a conflict clause in case of failure *)
let final_check (env:t) : final_check_res =
  try
    CCVector.iter
      (fun (module P : Plugin.S) ->
         begin match P.check_if_sat (actions env) with
           | Sat -> ()
           | Unsat (l,p) ->
             (* conflict *)
             List.iter (add_atom env) l;
             let c = Clause.make l (Lemma p) in
             raise (Conflict c)
         end)
      env.plugins;
    if fully_propagated env && Stack.is_empty env.clauses_to_add
    then FC_sat
    else FC_propagate
  with Conflict c ->
    FC_conflict c

(* fixpoint of propagation and decisions until a model is found, or a
   conflict is reached *)
let solve ?(gc=true) ?(restarts=true) (env:t) : unit =
  Log.debugf 2 (fun k->k"@{<Green>#### Solve@}");
  if is_unsat env then (
    raise Unsat;
  );
  (* initial limits for conflicts and learnt clauses *)
  let n_of_conflicts = ref (to_float env.restart_first) in
  let n_of_learnts =
    ref (CCFloat.max 50. ((to_float (nb_clauses env)) *. env.learntsize_factor))
  in
  try
    while true do
      begin
        try
          let nconf = if restarts then to_int !n_of_conflicts else max_int in
          search env nconf
        with
          | Restart ->
            (* garbage collect, if needed *)
            if gc &&
               !n_of_learnts >= 0. &&
               float(Vec.size env.clauses_learnt - Vec.size env.trail) >= !n_of_learnts
            then (
              let n = (to_int !n_of_learnts) + 1 in
              reduce_db env ~down_to:n
            );

            (* increment parameters to ensure termination *)
            n_of_conflicts := !n_of_conflicts *. env.restart_inc;
            n_of_learnts   := !n_of_learnts *. env.learntsize_inc;
          | Sat ->
            assert (fully_propagated env);
            begin match final_check env with
              | FC_sat -> raise Sat
              | FC_conflict c ->
                Log.debugf info (fun k -> k "Theory conflict clause: %a" Clause.debug c);
                Stack.push c env.clauses_to_add
              | FC_propagate -> () (* need to propagate *)
            end;
      end
    done
  with Sat -> ()

let assume env ?tag (cnf:atom list list) =
  List.iter
    (fun l ->
       let c = Clause.make ?tag l Hyp in
       Log.debugf debug (fun k->k "Assuming clause: @[<hov 2>%a@]" Clause.debug c);
       Stack.push c env.clauses_to_add)
    cnf

(* create a factice decision level for local assumptions *)
let push (env:t) : unit =
  Log.debug debug "Pushing a new user level";
  cancel_until env (base_level env);
  Log.debugf debug
    (fun k -> k "@[<v>Status:@,@[<hov 2>trail: %d - %d@,%a@]"
        env.elt_head env.th_head (Vec.print ~sep:"" Term.debug) env.trail);
  begin match propagate env with
    | Some confl ->
      report_unsat env confl
    | None ->
      Log.debugf debug
        (fun k -> k "@[<v>Current trail:@,@[<hov>%a@]@]"
            (Vec.print ~sep:"" Term.debug) env.trail);
      new_decision_level env;
      Log.debugf info
        (fun k->k"Creating new user level (cur_level %d)" (decision_level env));
      Vec.push env.user_levels (Vec.size env.clauses_temp);
      assert (decision_level env = base_level env)
  end

(* pop the last factice decision level *)
let pop (env:t) : unit =
  if base_level env = 0 then (
    Log.debug warn "Cannot pop (already at level 0)";
  ) else (
    Log.debug info "Popping user level";
    assert (base_level env > 0);
    env.unsat_conflict <- None;
    let n = Vec.last env.user_levels in
    Vec.pop env.user_levels; (* before the [cancel_until]! *)
    (* FIXME: shouldn't this be done only when the last level is [pop()]'d? *)
    (* Add the root clauses to the clauses to add *)
    Stack.iter (fun c -> Stack.push c env.clauses_to_add) env.clauses_root;
    Stack.clear env.clauses_root;
    (* remove from env.clauses_temp the now invalid clauses. *)
    Vec.shrink env.clauses_temp n;
    assert (Vec.for_all (fun c -> Array.length c.c_atoms = 1) env.clauses_temp);
    assert (Vec.for_all (fun c -> Atom.level c.c_atoms.(0) <= base_level env) env.clauses_temp);
    cancel_until env (base_level env)
  )

(* Add local hyps to the current decision level *)
let local (env:t) (l:atom list) : unit =
  let aux a =
    Log.debugf info (fun k-> k "Local assumption: @[%a@]" Atom.debug a);
    assert (decision_level env = base_level env);
    if Atom.is_true a then ()
    else (
      let c = Clause.make [a] Local in
      Log.debugf debug (fun k -> k "Temp clause: @[%a@]" Clause.debug c);
      Vec.push env.clauses_temp c;
      if Atom.is_false a then (
        (* conflict between assumptions: UNSAT *)
        report_unsat env c;
      ) else (
        (* make a decision, propagate *)
        let level = decision_level env in
        enqueue_bool env a ~level (Bcp c);
      )
    )
  in
  assert (base_level env >= 0);
  if base_level env = 0 then (
    invalid_arg "Solver.local: need to `push` before";
  );
  begin match env.unsat_conflict with
    | None ->
      Log.debug info "Adding local assumption";
      cancel_until env (base_level env);
      List.iter aux l
    | Some _ ->
      Log.debug warn "Cannot add local assumption (already unsat)"
  end

(* Check satisfiability *)
let check_clause (c:clause) : bool =
  let res =
    CCArray.exists
      (fun a ->
         Atom.value_bool a |> CCOpt.get_lazy (fun () -> raise UndecidedLit))
      c.c_atoms
  in
  if res then true
  else (
    Log.debugf debug
      (fun k -> k "Clause not satisfied: @[<hov>%a@]" Clause.debug c);
    false
  )

let[@inline] check_vec v = Vec.for_all check_clause v

let[@inline] check_stack s =
  Sequence.of_stack s
  |> Sequence.for_all check_clause

let check (env:t) : bool =
  Stack.is_empty env.clauses_to_add &&
  check_stack env.clauses_root &&
  check_vec env.clauses_hyps &&
  check_vec env.clauses_learnt &&
  check_vec env.clauses_temp

(* Unsafe access to internal data *)

let hyps env = env.clauses_hyps
let history env = env.clauses_learnt
let temp env = env.clauses_temp
let trail env = env.trail

(* stats *)

let pp_stats out (s:t): unit =
  Fmt.fprintf out
    "(@[stats@ :n_conflicts %d@ :n_learnt %d@ \
     :n_decisions %d@ :n_propagations %d@ :n_restarts %d@ \
     :n_initial %d@ :n_gc %d@ :n_deleted %d@]"
    s.conflicts s.n_learnt s.decisions s.propagations s.starts
    (Vec.size s.clauses_hyps) s.n_gc s.n_deleted

