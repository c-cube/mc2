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
exception UndecidedLit of term
exception Restart
exception Out_of_time
exception Out_of_space

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

  backtrack_stack : (unit -> unit) Vec.t;
  (* one set of undo actions for every decision level *)

  backtrack_levels: level Vec.t;
  (* offsets in [backtrack_stack] *)

  user_levels : level Vec.t;
  (* user levels in [clauses_temp] *)

  mutable bcp_head : int;
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

  tmp_term_vec : term Vec.t;
  (* temporary vector used during conflict analysis.
     Contains terms marked during analysis, to be unmarked at cleanup *)

  mutable var_incr : float;
  (* increment for variables' activity *)
  mutable clause_incr : float;
  (* increment for clauses' activity *)

  restart_inc : float;
  (* multiplicative factor for restart limit, default 1.5 *)
  mutable restart_first : int;
  (* intial restart limit, default 100 *)


  mutable learntsize_factor : float;
  (* initial limit for the number of learnt clauses, as a factor of initial
     number of clauses *)
  mutable learntsize_inc : float;
  (* multiplicative factor for [learntsize_factor] at each restart *)

  mutable starts : int; (* number of (re)starts *)
  mutable decisions : int; (* number of decisions *)
  mutable bool_decisions : int; (* number of boolean decisions *)
  mutable propagations : int; (* number of propagations *)
  mutable conflicts : int; (* number of conflicts *)
  mutable n_learnt : int; (* total number of clauses learnt *)
  mutable n_gc_c: int; (* number of rounds of GC for clauses *)
  mutable n_gc_t: int; (* number of rounds of GC for terms *)
  mutable n_deleted_c: int; (* number of deleted clauses *)
  mutable n_deleted_t: int; (* numbet of deleted terms *)
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
let[@inline] plugins env = CCVector.to_iter env.plugins
let[@inline] get_service env (k:_ Service.Key.t) =
  Service.Registry.find env.services k

let[@inline] get_service_exn env (k:_ Service.Key.t) =
  Service.Registry.find_exn env.services k

let[@inline] err_undecided_lit t = raise (UndecidedLit t)

let() = Printexc.register_printer
    (function
      | UndecidedLit t ->
        Some (Error.err_sprintf "undecided_lit: %a" Term.debug t)
      | Out_of_space -> Some "Unknown"
      | Out_of_time -> Some "Timeout"
      | _ -> None)

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
            Error.errorf "could not find service `%s`" (Service.Key.name k)
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
let[@inline] iter_terms (env:t) : term Iter.t =
  CCVector.to_iter env.plugins
  |> Iter.flat_map
    (fun (module P : Plugin.S) -> P.iter_terms)
  |> Iter.filter Term.has_var

let[@inline] term_init (env:t) (t:term) : unit =
  t.t_tc.tct_init (actions env) t

(* provision term (and its sub-terms) for future assignments.
   This is the function exposed to users and therefore it performs some checks. *)
let[@unrolled 1] rec add_term (env:t) (t:term): unit =
  if Term.is_deleted t then (
    Error.errorf "(@[trying to add deleted term@ `%a`@])" Term.debug t
  ) else if Term.is_added t then (
    assert (Term.has_var t);
  ) else (
    Log.debugf 15 (fun k->k"(@[solver.add_term %a@])" Term.debug t);
    Term.field_set field_t_is_added t;
    Term.setup_var t;
    Term.iter_subterms t (add_term env); (* add subterms, recursively *)
    (* does the term have a value, or do we need to decide on it? *)
    begin match Term.eval t with
      | Eval_into (value, []) ->
        t.t_assign <- TA_assign {value;reason=Eval [];level=0};
      | Eval_into (value, l) when List.for_all (fun t -> Term.level t=0) l ->
        t.t_assign <- TA_assign {value;reason=Eval l;level=0};
      | _ ->
        H.insert env.term_heap t; (* add to priority queue for decision *)
    end;
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
  let ty = (Term.ty t) in
  if ty == Bool then
    (* this case doesn't seem to happen *)
    env.bool_decisions <- env.bool_decisions + 1;
  Type.decide ty (actions env) t

let[@inline] assign_term (env:t) (t:term) value reason level : unit =
  assert (t.t_assign == TA_none);
  t.t_assign <- TA_assign {value;reason;level};
  Vec.push env.trail t

(* main building function *)
let create_real (actions:actions lazy_t) : t = {
  unsat_conflict = None;
  next_decision = None;

  plugins = CCVector.create();
  services = Service.Registry.create();
  actions;

  clauses_hyps = Vec.create();
  clauses_learnt = Vec.create();
  clauses_temp = Vec.create();

  clauses_root = Stack.create ();
  clauses_to_add = Stack.create ();

  th_head = 0;
  bcp_head = 0;

  trail = Vec.create();
  backtrack_stack = Vec.make 601 (fun () -> assert false);
  backtrack_levels = Vec.make 10 (-1);
  decision_levels = Vec.make 601 (-1);
  user_levels = Vec.make 10 (-1);
  tmp_term_vec = Vec.create();

  term_heap = H.create();

  var_incr = 1.;
  clause_incr = 1.;
  var_decay = 1. /. 0.95;
  clause_decay = 1. /. 0.999;

  restart_inc = 1.5;
  restart_first = 100;

  learntsize_factor = 1.5 ; (* can learn 3× as many clauses as present initially *)
  learntsize_inc = 1.5; (* n× more learnt clauses after each restart *)

  starts = 0;
  decisions = 0;
  bool_decisions = 0;
  propagations = 0;
  conflicts = 0;
  n_learnt=0;
  n_gc_c=0;
  n_gc_t=0;
  n_deleted_c=0;
  n_deleted_t=0;
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

(* Eliminates atom duplicates in clauses, and remove absurd atoms.
   returns [true] if something changed. *)
let eliminate_duplicates_and_absurd (clause:clause) : clause * bool =
  let duplicates = ref [] in
  let removed_absurd = ref false in
  let res = ref [] in
  Array.iter
    (fun a ->
       if Atom.marked a then duplicates := a :: !duplicates
       else if Atom.is_absurd a then removed_absurd := true
       else (Atom.mark a; res := a :: !res))
    (Clause.atoms clause);
  (* cleanup *)
  let trivial =
    List.exists (fun a -> Term.Bool.both_atoms_marked a.a_term) !res
  in
  Array.iter Atom.unmark clause.c_atoms;
  if trivial then (
    raise Trivial
  ) else if not !removed_absurd && !duplicates = [] then (
    clause, false
  ) else (
    (* make a new clause, simplified *)
    Clause.make !res (Simplify clause), true
  )

(* simplify clause by removing duplicates *)
let simplify_clause (c:clause) : clause =
  let c', has_simplified = eliminate_duplicates_and_absurd c in
  if has_simplified then (
    Log.debugf 15
      (fun k -> k "(@[solver.simplify_clause@ :into %a@ :from %a@])"
          Clause.debug c' Clause.debug c);
  );
  c'

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
let partition_atoms (atoms:atom array) : atom list * raw_premise_step list =
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
          (* A var false at level 0 can be eliminated from the clause,
             but we need to keep in mind that we used another clause to simplify it. *)
          begin match Term.reason a.a_term with
            | Some (Bcp cl | Bcp_lazy (lazy cl)) ->
              partition_aux trues unassigned falses
                (cl :: history) (i + 1)
            | Some (Eval []) ->
              partition_aux trues unassigned falses history (i + 1)
            | Some (Eval l) when List.for_all (fun t->Term.level t=0) l ->
              partition_aux trues unassigned falses history (i + 1)
            | Some (Eval _) -> assert false
            (* Evaluation at level 0 are, well not easy to deal with,
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
  env.bcp_head = Vec.size env.trail

(* Making a decision.
   Before actually creatig a new decision level, we check that all propagations
   have been done and propagated to the theory, i.e that the theoriy state
   indeed takes into account the whole stack of literals, i.e we have indeed
   reached a propagation fixpoint before making a new decision *)
let new_decision_level (env:t) : unit =
  assert (fully_propagated env);
  Vec.push env.decision_levels (Vec.size env.trail);
  Vec.push env.backtrack_levels (Vec.size env.backtrack_stack);
  ()

(* Attach/Detach a clause.
   A clause is attached (to its watching lits) when it is first added,
   either because it is assumed or learnt.
*)
let attach_clause (_env:t) (c:clause): unit =
  if not (Clause.attached c) then (
    Log.debugf debug (fun k -> k "(@[solver.attach_clause@ %a@])" Clause.debug c);
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
    let backtrack_top = Vec.get env.backtrack_levels lvl in
    env.th_head <- top; (* will need to repropagate from there *)
    let head = ref top in
    (* Now we need to cleanup the vars that are not valid anymore
       (i.e to the right of propagate_head in the queue).
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
        Log.debugf 50 (fun k->k "pop term %a (in heap %B, deleted %B)"
                          Term.debug t (H.in_heap t) (Term.is_deleted t));
        t.t_assign <- TA_none;
        if not (Term.is_deleted t) then (
          schedule_decision_term env t;
        )
      );
    done;
    (* elements we kept are already BCP, update pointers accordingly *)
    env.bcp_head <- !head;
    (* Resize the vectors according to their new size. *)
    Vec.shrink env.trail !head;
    Vec.shrink env.decision_levels lvl;
    Vec.shrink env.backtrack_levels lvl;
    (* call undo-actions registered by plugins *)
    while Vec.size env.backtrack_stack > backtrack_top do
      let f = Vec.pop env.backtrack_stack in
      f();
    done;
  );
  assert (Vec.size env.decision_levels = Vec.size env.backtrack_levels);
  ()

exception Conflict of clause

(* Unsatisfiability is signaled through an exception, since it can happen
   in multiple places (adding new clauses, or solving for instance). *)
let report_unsat (env:t) (confl:clause) : _ =
  Log.debugf info
    (fun k -> k "(@[@{<Yellow>solver.unsat_conflict@}:@ %a@])" Clause.debug confl);
  env.unsat_conflict <- Some confl;
  raise Unsat

(* Simplification of boolean propagation reasons {b at level 0}.
   When doing boolean propagation at level 0, it can happen
   that the clause cl, which propagates a formula, also contains
   other formulas, but has been simplified. in which case, we
   need to rebuild a clause with correct history, in order to
   be able to build a correct proof at the end of proof search. *)
let simpl_reason_level_0 : reason -> reason = function
  | (Bcp cl | Bcp_lazy (lazy cl)) as r ->
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
            Clause.make l (Premise.raw_steps (cl :: history))
          in
          Log.debugf debug
            (fun k -> k "(@[simplified_reason@ :from %a@ :to %a@])"
                Clause.debug cl Clause.debug c');
          Bcp c'
        )
      | _ ->
        Error.errorf
          "(@[simpl_reason_level_0.fail@ :simp-atoms %a@ :bcp-from %a@])"
          Clause.debug_atoms l Clause.debug cl
    end
  | r -> r

(* Boolean propagation.
   Wrapper function for adding a new propagated formula. *)
let enqueue_bool (env:t) (a:atom) ~level:level (reason:reason) : unit =
  if Atom.is_false a then (
    Error.errorf "(@[solver.enqueue_bool.atom_is_false@ %a@])" Atom.debug a
  ) else if Atom.is_true a then (
    Log.debugf 15 (fun k->k "(@[solver.enqueue_bool.already_true@ %a@])" Atom.debug a);
  ) else (
    assert (level >= 0);
    (* simplify reason *)
    let reason =
      if level > 0 then reason
      else simpl_reason_level_0 reason
    in
    (* assign term *)
    let value = Value.of_bool (Atom.is_pos a) in
    assign_term env a.a_term value reason level;
    Log.debugf debug
      (fun k->k "(@[solver.enqueue_bool (%d/%d)@ %a@ :reason %a@])"
          (Vec.size env.trail)(decision_level env) Atom.debug a Reason.pp (level,reason));
    ()
  )

(* atom [a] evaluates to [true] because of [terms] *)
let enqueue_semantic_bool_eval (env:t) (a:atom) (terms:term list) : unit =
  if Atom.is_true a then ()
  else if Atom.is_false a then (
    (* conflict *)
    begin match Term.reason_exn a.a_term with
      | Bcp c | Bcp_lazy (lazy c) ->
        raise (Conflict c)
      | Decision -> assert false
      | Eval _ -> assert false
    end
  ) else (
    assert (List.for_all Term.is_added terms);
    (* level of propagations is [max_{t in terms} t.level] *)
    let lvl =
      List.fold_left
        (fun acc t ->
           let t_lvl = Term.level t in
           assert (t_lvl >= 0); max acc t_lvl)
        0 terms
    in
    env.propagations <- env.propagations + 1;
    enqueue_bool env a ~level:lvl (Eval terms)
  )

(* atom [a] evaluates to [true] because of [terms] *)
let enqueue_bool_theory_propagate (env:t) (a:atom)
    ~lvl (atoms:atom list) (lemma: lemma) : unit =
  if Atom.is_true a then ()
  else (
    let c = Clause.make atoms (Lemma lemma) |> simplify_clause in
    env.propagations <- env.propagations + 1;
    enqueue_bool env a ~level:lvl (Bcp c)
  )

(* MCsat semantic assignment *)
let enqueue_assign (env:t) (t:term) (value:value) (reason:reason) ~(level:int) : unit =
  (* assert (not (H.in_heap t)); *)
  if Term.has_some_value t then (
    Log.debugf error
      (fun k -> k "Trying to assign an already assigned literal: %a" Term.debug t);
    assert false
  );
  assert (t.t_assign = TA_none);
  assign_term env t value reason level;
  Log.debugf debug
    (fun k->k "(@[solver.enqueue_semantic (%d/%d)@ %a@ :reason %a@])"
        (Vec.size env.trail) (decision_level env)
        Term.debug t Reason.pp (level,reason));
  ()

(* evaluate an atom for MCsat, if it's not assigned
   by boolean propagation/decision *)
let th_eval (env:t) (a:atom) : value option =
  if Atom.is_true a || Atom.is_false a then None
  else (
    begin match Atom.eval a with
      | Eval_unknown -> None
      | Eval_into (b, l) ->
        let atom =
          if Value.is_true b then a
          else (
            assert (Value.is_false b);
            Atom.neg a
          )
        in
        enqueue_semantic_bool_eval env atom l;
        Some b
    end
  )

let pp_subs out l : unit =
  let pp_p out t =
    Fmt.fprintf out "(@[%a@ @<1>→ %a@])" Term.debug t Value.pp (Term.value_exn t)
  in
  Fmt.fprintf out "(@[<v>%a@])" (Util.pp_list pp_p) l

let debug_eval out = function
  | Eval_unknown -> Fmt.string out "unknown"
  | Eval_into (v, subs) ->
    Fmt.fprintf out "(@[<hv>%a@ :subs (@[<v>%a@])@])" Value.pp v pp_subs subs

(* [a] is part of a conflict/learnt clause, but might not be evaluated yet.
   Evaluate it, save its value, and ensure it is indeed false. *)
let eval_atom_to_false ~save (env:t) (a:atom): unit =
  if Atom.has_some_value a then (
    Log.debugf debug (fun k->k "(@[atom_must_be_false@ %a@])" Atom.debug a);
    assert (
      let ok = Atom.is_false a || Atom.can_eval_to_false a in
      if not ok then (
        Log.debugf 0 (fun k->k "(@[<2>atom should be false:@ %a@])" Atom.debug a);
      );
      ok);
  ) else (
    let v = Atom.eval a in
    Log.debugf debug (fun k->k "(@[atom_must_be_false@ %a@ :eval_to %a@])"
                         Atom.debug a debug_eval v);
    begin match v with
      | Eval_into (V_false, subs) ->
        (* update value, if it doesn't have one already *)
        if save then (
          enqueue_semantic_bool_eval env (Atom.neg a) subs
        )
      | _ ->
        Log.debugf 0 (fun k->k "(@[<2>atom should be false:@ %a@])" Atom.debug a);
        assert false
    end
  )

(* move atoms assigned at high levels first *)
let[@inline] put_high_level_atoms_first (arr:atom array) : unit =
  Array.iteri
    (fun i a ->
       if i>0 && Atom.level a > Atom.level arr.(0) then (
         (* move first to second, [i]-th to first, second to [i] *)
         if i=1 then (
           Util.swap_arr arr 0 1;
         ) else (
           let tmp = arr.(1) in
           arr.(1) <- arr.(0);
           arr.(0) <- arr.(i);
           arr.(i) <- tmp;
         );
       ) else if i>1 && Atom.level a > Atom.level arr.(1) then (
         Util.swap_arr arr 1 i;
       ))
    arr

let[@inline] level_subs (l:term list) : level =
  List.fold_left (fun l t -> max l (Term.level t)) 0 l

(* find how the atom can be false, either by assignment or by evaluation *)
let[@inline] atom_as_false (a:atom) : (reason * level) option =
  if Atom.is_false a then Some (Term.reason_exn a.a_term, Atom.level a)
  else match Atom.eval a with
    | Eval_into (V_false, subs) -> Some (Eval subs, level_subs subs)
    | _ -> None

(** {2 Conflict Analysis} *)

(* Conflict analysis for MCSat, looking for the last UIP
   We do not really perform a series of resolution/paramodulation,
   but just keep enough information for proof reconstruction.
*)

module Conflict = struct
  type t = clause

  let[@inline] pp out (c:t) = Clause.debug out c

  let[@inline] level (c:t) : level =
    Array.fold_left
      (fun acc p -> max acc (Atom.level p)) 0 c.c_atoms
end

module Conflict_res = struct
  (* result of conflict analysis, containing the learnt clause and some
     additional info.

     invariant: cr_history's order matters, as its head is later used
     during pop operations to determine the origin of a clause/conflict
     (boolean conflict i.e hypothesis, or theory lemma) *)
  type t = {
    cr_backtrack_lvl : int; (* level to backtrack to *)
    cr_learnt: atom array; (* lemma learnt from conflict *)
    cr_history: raw_premise_step list; (* justification: conflict clause + proof steps *)
    cr_is_uip: bool; (* conflict is UIP? *)
  }
end

module Analyze : sig
  val analyze : t -> clause -> Conflict_res.t
end = struct
  (* state for conflict analysis *)
  type state = {
    cs_conflict_level: int; (* conflict level *)
    mutable cs_continue: bool;
    mutable cs_n_to_analyze: int; (* number of atoms yet to analyze *)
    mutable cs_ptr_trail: int; (* current offset in the trail *)
    mutable cs_clause: clause option; (* current clause to analyze *)
    mutable cs_learnt: atom list; (* resulting clause to be learnt *)
    mutable cs_history: raw_premise_step list; (* proof object *)
  }

  (** terms seen so far, for cleanup *)
  let[@inline] seen (env:t) = env.tmp_term_vec

  (* find which level to backtrack to, given a conflict clause
     and a boolean stating whether it is a UIP ("Unique Implication Point")
     precondition: the atoms with highest decision level are first in the array *)
  let backtrack_lvl (env:t) (a:atom array) : int * bool =
    if Array.length a <= 1 then (
      0, true (* unit or empty clause *)
    ) else (
      assert (Atom.level a.(0) >= base_level env);
      assert (Atom.level a.(1) >= base_level env);
      if Atom.level a.(0) > Atom.level a.(1) then (
        (* backtrack below [a], so we can propagate [not a] *)
        Atom.level a.(1), true
        (* NOTE: (to explore)
           since we can propagate at level [a.(1).level] wherever we want
           we might also want to backtrack at [a.(0).level-1] but still
           propagate [¬a.(0)] at a lower level? That would save current decisions *)
      ) else (
        (* NOTE: clauses can be deduced that are not semantic splits
           nor regular conflict clause, thanks to paramodulation *)
        assert (Atom.level a.(0) >= Atom.level a.(1));
        assert (Atom.level a.(0) >= base_level env);
        max (Atom.level a.(0) - 1) (base_level env), false
      )
    )


  (* loop until there is either:
     - the clause is empty (found unsat)
     - one decision term with level strictly greater than the other
       terms level (the UIP)
     - all terms at maximal level are semantic propagations ("semantic split")

     as long as this is not reached, we pick the highest (propagated)
     literal of the clause and do resolution with the clause that
     propagated it. Note that there cannot be two decision literals
     above the conflict_level.
  *)
  let analyze_loop (env:t) (st:state) : unit =
    while st.cs_continue do
      (* if we have a clause, do resolution on it by marking all its
         literals that are not "seen" yet. *)
      begin match st.cs_clause with
        | None ->
          Log.debug debug "(analyze_conflict.skip_resolution)"
        | Some clause ->
          Log.debugf debug
            (fun k->k "(@[analyze_conflict.resolving@ :clause %a@])" Clause.debug clause);
          (* increase activity since [c] participates in a conflict *)
          begin match clause.c_premise with
            | P_raw_steps _ | P_steps _ -> bump_clause_activity env clause
            | Hyp | Local | Simplify _ | Lemma _ -> ()
          end;
          st.cs_history <- clause :: st.cs_history;
          (* visit the current predecessors *)
          for j = 0 to Array.length clause.c_atoms - 1 do
            let q = clause.c_atoms.(j) in
            assert (Atom.is_true q || Atom.is_false q && Atom.level q >= 0); (* unsure? *)
            if Atom.level q <= 0 then (
              (* Must be a 0-level propagation. [q] is not part
                 of the conflict clause, because it will be useless,
                 but we still keep track of it in the proof. *)
              assert (Atom.level q=0 && Atom.is_false q);
              begin match Atom.reason_exn q with
                | Bcp cl | Bcp_lazy (lazy cl) ->
                  st.cs_history <- cl :: st.cs_history
                | Eval [] -> () (* absurd *)
                | Eval l -> assert (List.for_all (fun t->Term.level t=0) l);
                | _ -> assert false
              end
            );
            (* if we have not explored this atom yet, do it now.
               It can either be part of the final clause, or it can lead
               to resolution with another clause *)
            if not (Term.marked q.a_term) then (
              Term.mark q.a_term;
              Vec.push (seen env) q.a_term;
              (* only atoms above level 0 can participate to the conflict,
                 these proved at level 0 would bring no information *)
              if Atom.level q > 0 then (
                bump_term_activity env q.a_term;
                if Atom.level q >= st.cs_conflict_level then (
                  st.cs_n_to_analyze <- 1 + st.cs_n_to_analyze;
                ) else (
                  (* [q] will be part of the learnt clause *)
                  st.cs_learnt <- q :: st.cs_learnt;
                )
              )
            )
          done
      end;

      (* look for the next node to expand by going down the trail *)
      while
        let t = Vec.get env.trail st.cs_ptr_trail in
        Log.debugf 30 (fun k -> k "(@[conflict_analyze.at_trail_elt@ %a@])" Term.debug t);
        begin match t.t_var with
          | Var_none -> assert false
          | Var_semantic _ -> true (* skip semantic assignments *)
          | Var_bool _ ->
            (* skip a term if:
               - it is not marked (not part of resolution), OR
               - below conflict level
            *)
            not (Term.marked t) || Term.level t < st.cs_conflict_level
        end
      do
        st.cs_ptr_trail <- st.cs_ptr_trail - 1;
      done;
      (* now [t] is the term to analyze. *)
      let t = Vec.get env.trail st.cs_ptr_trail in
      let p = Term.Bool.assigned_atom_exn t in
      st.cs_n_to_analyze <- st.cs_n_to_analyze - 1;
      st.cs_ptr_trail <- st.cs_ptr_trail - 1;
      let reason = Term.reason_exn t in
      Log.debugf 30
        (fun k->k"(@[<hv>conflict_analyze.check_done:@ %a@ :n_to_analyze %d@ :reason %a@])"
            Term.debug t st.cs_n_to_analyze Reason.pp (Term.level t,reason));
      begin match st.cs_n_to_analyze, reason with
        | 0, _ ->
          (* [t] is the UIP, or we have a semantic split *)
          st.cs_continue <- false;
          st.cs_learnt <- Atom.neg p :: st.cs_learnt
        | n, Eval _ ->
          assert (n > 0);
          st.cs_learnt <- Atom.neg p :: st.cs_learnt;
          st.cs_clause <- None
        | n, (Bcp cl | Bcp_lazy (lazy cl))->
          assert (n > 0);
          assert (Atom.level p >= st.cs_conflict_level);
          st.cs_clause <- Some cl
        | _ -> assert false
      end
    done;
    ()

  let analyze (env:t) (c:clause) : Conflict_res.t =
    assert (decision_level env > 0);
    let conflict_level = Conflict.level c in
    let st = {
      cs_n_to_analyze=0;
      cs_learnt=[];
      cs_continue=true;
      cs_clause=Some c;
      cs_ptr_trail=(Vec.size env.trail - 1);
      cs_history=[];
      cs_conflict_level=conflict_level;
    } in
    Vec.clear (seen env);
    Log.debugf 15
      (fun k -> k "(@[analyze_conflict (%d/%d)@ :conflict %a@])"
          conflict_level (decision_level env) Clause.debug c);
    assert (conflict_level >= 0);
    analyze_loop env st;
    Vec.iter Term.unmark (seen env);
    Vec.clear (seen env);
    (* put high level atoms first *)
    let learnt_a = Array.of_list st.cs_learnt in
    put_high_level_atoms_first learnt_a;
    Log.debugf debug
      (fun k -> k "(@[analyze_conflict.learnt@ %a@])" Clause.debug_atoms_a learnt_a);
    let level, is_uip = backtrack_lvl env learnt_a in
    {Conflict_res.
      cr_backtrack_lvl = level;
      cr_learnt = learnt_a;
      cr_history = List.rev st.cs_history;
      cr_is_uip = is_uip;
    }
end

(* add the learnt clause to the clause database, propagate, etc. *)
let record_learnt_clause (env:t) (cr:Conflict_res.t): unit =
  let open Conflict_res in
  begin match cr.cr_learnt with
    | [||] ->
      (* empty clause *)
      let c = Clause.make_arr [||] (Premise.raw_steps_or_simplify cr.cr_history) in
      report_unsat env c
    | [|fuip|] ->
      assert (cr.cr_backtrack_lvl = 0);
      env.n_learnt <- env.n_learnt + 1;
      let uclause =
        Clause.make_arr cr.cr_learnt (Premise.raw_steps_or_simplify cr.cr_history)
        |> simplify_clause
      in
      add_atom env fuip;
      if Atom.is_false fuip then (
        assert (Atom.level fuip = 0);
        report_unsat env uclause
      ) else (
        Vec.push env.clauses_learnt uclause;
        Log.debugf debug (fun k->k "(@[learn_clause_0:@ %a@])" Clause.debug uclause);
        (* no need to attach [uclause], it is true at level 0 *)
        env.propagations <- env.propagations + 1;
        enqueue_bool env fuip ~level:0 (Bcp uclause)
      )
    | c_learnt ->
      let fuip = c_learnt.(0) in
      let premise = Premise.raw_steps_or_simplify cr.cr_history in
      let lclause = Clause.make_arr c_learnt premise |> simplify_clause in
      Vec.push env.clauses_learnt lclause;
      Array.iter (add_atom env) lclause.c_atoms;
      env.n_learnt <- env.n_learnt + 1;
      Log.debugf debug
        (fun k->k "(@[learn_clause:@ %a@ :backtrack-lvl %d@])"
            Clause.debug lclause cr.cr_backtrack_lvl);
      attach_clause env lclause;
      bump_clause_activity env lclause;
      if cr.cr_is_uip then (
        env.propagations <- env.propagations + 1;
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
    report_unsat env confl (* Top-level conflict *)
  );
  let cr = Analyze.analyze env confl in
  cancel_until env (max cr.Conflict_res.cr_backtrack_lvl (base_level env));
  record_learnt_clause env cr

(* Get the correct vector to insert a clause in. *)
let[@unrolled 1] rec vec_to_insert_clause_into env c = match c.c_premise with
  | Hyp -> env.clauses_hyps
  | Local -> env.clauses_temp
  | Simplify d -> vec_to_insert_clause_into env d
  | Lemma _ | P_raw_steps _ | P_steps _ -> env.clauses_learnt

(* Add a new clause, simplifying, propagating, and backtracking if
   the clause is false in the current trail *)
let add_clause (env:t) (c0:clause) : unit =
  Log.debugf debug (fun k -> k "(@[solver.add_clause@ %a@])" Clause.debug c0);
  (* Insertion of new lits is done before simplification. Indeed, else a lit in a
     trivial clause could end up being not decided on, which is a bug. *)
  let vec = vec_to_insert_clause_into env c0 in
  try
    (* add atoms first, so as to evaluate absurd ones, etc. *)
    Array.iter (add_atom env) c0.c_atoms;
    (* now simplify *)
    let c = simplify_clause c0 in
    let atoms, history = partition_atoms c.c_atoms in
    let clause =
      if history = []
      then (
        (* update order of atoms *)
        List.iteri (fun i a -> c.c_atoms.(i) <- a) atoms;
        c
      ) else (
        Clause.make atoms (Premise.raw_steps (c :: history))
      )
    in
    Log.debugf info (fun k->k "(@{<green>solver.new_clause@}@ %a@])" Clause.debug clause);
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
          Log.debug debug "(solver.add_clause: unit_clause adding to clauses to add)";
          Stack.push clause env.clauses_to_add;
          report_unsat env clause
        ) else if Atom.is_true a then (
          (* If the atom is already true, then it should be because of a local hyp.
             However it means we can't propagate it at level 0. In order to not lose
             that information, we store the clause in a stack of clauses that we will
             add to the solver at the next pop. *)
          Log.debug debug "(solver.add_clause: unit clause, adding to root clauses)";
          assert (0 < Atom.level a && Atom.level a <= base_level env);
          Stack.push clause env.clauses_root;
          ()
        ) else (
          Log.debugf debug
            (fun k->k "(@[solver.add_clause: unit clause, propagating@ :atom %a@])" Atom.debug a);
          Vec.push vec clause;
          env.propagations <- env.propagations + 1;
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
            env.propagations <- env.propagations + 1;
            enqueue_bool env a ~level:lvl (Bcp clause)
          )
        )
    end
  with Trivial ->
    (* ignore clause. *)
    Log.debugf info
      (fun k->k "(@[solver.add_clause: trivial clause ignored@ :c %a@])" Clause.debug c0);
    (*Vec.push vec c0;*)
    ()

(* really add clauses pushed by plugins to the solver *)
let flush_clauses (env:t) =
  if not (Stack.is_empty env.clauses_to_add) then (
    let nbc = env.nb_init_clauses + Stack.length env.clauses_to_add in
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
  assert (Array.length c.c_atoms >= 2);
  let first = Array.unsafe_get atoms 0 in
  if first == Atom.neg a then (
    (* false lit must be at index 1 *)
    Array.unsafe_set atoms 0 (Array.unsafe_get atoms 1);
    Array.unsafe_set atoms 1 first;
  ) else (
    assert (Atom.neg a == atoms.(1));
  );
  let first = Array.unsafe_get atoms 0 in
  if Atom.is_true first
  then Watch_keep (* true clause, keep it in watched *)
  else (
    try (* look for another watch lit *)
      for k = 2 to Array.length atoms - 1 do
        let ak = Array.unsafe_get atoms k in
        if not (Atom.is_false ak) then (
          (* watch lit found: update and exit *)
          Array.unsafe_set atoms 1 ak;
          Array.unsafe_set atoms k (Atom.neg a);
          (* remove [c] from [a.watched], add it to [ak.neg.watched] *)
          Vec.push (Atom.neg ak).a_watched c;
          raise_notrace Exit
        )
      done;
      (* no watch lit found *)
      if Atom.is_false first then (
        (* clause is false *)
        env.bcp_head <- Vec.size env.trail;
        raise_notrace (Conflict c)
      ) else (
        begin match th_eval env first with
          | None -> (* clause is unit, keep the same watches, but propagate *)
            env.propagations <- env.propagations + 1;
            Log.debugf 30
              (fun k->k
                  "(@[<hv>solver.propagate_in_clause.@{<yellow>propagate_bool@}@ %a@ :in-clause %a@])"
                  Atom.debug first Clause.debug c);
            enqueue_bool env first ~level:(decision_level env) (Bcp c)
          | Some V_true -> ()
          | Some V_false ->
            env.bcp_head <- Vec.size env.trail;
            raise_notrace (Conflict c)
          | Some _ -> assert false
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
let propagate_term_real (env:t) (t:term) watched: unit =
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

(* propagate term by notifying all watchers. This is the fast path
   in case there are no watchers. *)
let[@inline] propagate_term (env:t) (t:term) : unit =
  if Vec.size t.t_watches > 0 then (
    propagate_term_real env t t.t_watches
  )

(* some terms were decided/propagated. Now we
   need to inform the plugins about these assignments, so they can do their job.
   @return the conflict clause, if a plugin detects unsatisfiability *)
let rec theory_propagate (env:t) : clause option =
  assert (env.bcp_head <= Vec.size env.trail);
  if env.th_head = Vec.size env.trail then (
    if env.bcp_head = Vec.size env.trail then (
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
  if env.bcp_head = Vec.size env.trail then (
    theory_propagate env (* BCP done, now notify plugins *)
  ) else (
    let t = Vec.get env.trail env.bcp_head in
    env.bcp_head <- env.bcp_head + 1;
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
  assert (env.bcp_head <= Vec.size env.trail);
  bool_propagate env

module Actions : sig
  val make : t -> actions
end = struct
  let[@inline] on_backtrack (env:t) (f:unit->unit) : unit =
    Vec.push env.backtrack_stack f

  let raise_conflict (env:t) (atoms:atom list) (lemma:lemma) : 'a =
    Log.debugf debug (fun k->k
                         "(@[<hv>@{<yellow>raise_conflict@}@ :clause %a@ :lemma %a@])"
                         Clause.debug_atoms atoms Lemma.pp lemma);
    env.bcp_head <- Vec.size env.trail;
    env.th_head <- Vec.size env.trail;
    (* cleanup list of atoms, removing duplicates and absurd lits *)
    let atoms =
      Atom.Set.of_list atoms
      |> Atom.Set.to_list
      |> List.filter (fun a -> not (Atom.is_absurd a))
    in
    (* add atoms, also evaluate them if not already false *)
    List.iter
      (fun a ->
         add_atom env a;
         eval_atom_to_false ~save:true env a)
      atoms;
    let c = Clause.make atoms (Lemma lemma) in
    raise (Conflict c)

  let propagate_bool_eval (env:t) t (b:bool) ~(subs:term list) : unit =
    Log.debugf 5
      (fun k->k
          "(@[<hv>solver.@{<yellow>semantic_propagate_bool@}@ %a@ :val %B@ :subs %a@])"
          Term.debug t b pp_subs subs);
    let a = if b then Term.Bool.pa_unsafe t else Term.Bool.na_unsafe t in
    enqueue_semantic_bool_eval env a subs

  let propagate_bool_lemma (env:t) t (v:bool) atoms lemma : unit =
    let a = if v then Term.Bool.pa_unsafe t else Term.Bool.na_unsafe t in
    let lvl = List.fold_left
        (fun lvl b ->
           if not (Atom.equal a b) then (
             add_atom env b;
             eval_atom_to_false ~save:true env b;
             max lvl (Atom.level b)
           ) else lvl)
        0 atoms
    in
    Log.debugf 5
      (fun k->k "(@[<hv>solver.@{<yellow>theory_propagate_bool@}@ %a@ :val %B@ :lvl %d@ :clause %a@])"
          Term.debug t v lvl Clause.debug_atoms atoms);
    enqueue_bool_theory_propagate env a ~lvl atoms lemma

  (* build the "actions" available to the plugins *)
  let make (env:t) : actions =
    let act_level (): level = decision_level env
    and act_push_clause (c:clause) : unit =
      Log.debugf debug
        (fun k->k "(@[solver.@{<yellow>push_clause@}@ %a@])" Clause.debug c);
      Stack.push c env.clauses_to_add
    in
    { act_on_backtrack=on_backtrack env;
      act_push_clause;
      act_level;
      act_raise_conflict=raise_conflict env;
      act_propagate_bool_eval=propagate_bool_eval env;
      act_propagate_bool_lemma=propagate_bool_lemma env;
    }
end

(* main constructor *)
let create () : t =
  let rec env = lazy (create_real actions)
  and actions = lazy (Actions.make (Lazy.force env)) in
  let env = Lazy.force env in
  (* add builtins *)
  ignore (add_plugin env Builtins.plugin);
  env

(* Decide on a new literal, and enqueue it into the trail *)
let rec pick_branch_aux (env:t) (atom:atom) : unit =
  let t = atom.a_term in
  if Term.has_some_value t then (
    assert (not (Atom.is_undef atom));
    pick_branch_lit env
  ) else (
    (* does this boolean term eval to [true]? *)
    (* TODO: should the plugin already have propagated this?
       or is it an optim? *)
    begin match Term.eval t with
      | Eval_unknown ->
        (* do a decision *)
        env.decisions <- env.decisions + 1;
        env.bool_decisions <- env.bool_decisions + 1;
        new_decision_level env;
        Log.debugf debug (fun k->k "(@[solver.bool_decide@ %a@])" Atom.debug atom);
        let current_level = decision_level env in
        enqueue_bool env atom ~level:current_level Decision
      | Eval_into (b, l) ->
        (* already evaluates in the trail *)
        let a =
          if Value.is_true b then atom
          else (
            assert (Value.is_false b);
            Atom.neg atom
          )
        in
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
            if Term.has_some_value t then (
              pick_branch_lit env (* assigned already *)
            ) else (
              let value = decide_term env t in
              env.decisions <- env.decisions + 1;
              new_decision_level env;
              let current_level = decision_level env in
              enqueue_assign env t value Decision ~level:current_level
            )
        end
      )
  end

(* recursively mark clause [c] and its atoms *)
let rec gc_mark_clause (c:clause) : unit =
  if not (Clause.gc_marked c) then (
    Log.debugf 15 (fun k->k "(@[gc_mark_clause@ %a@])" Clause.pp_name c);
    Clause.gc_mark c;
    Array.iter (gc_mark_atom ~mark_clause:true) c.c_atoms;
  )

(* recursively mark [t] and its subterms *)
and gc_mark_term ~mark_clause (t:term) : unit =
  if not (Term.gc_marked t) then (
    Term.gc_mark t;
    Term.iter_subterms t (gc_mark_term ~mark_clause);
    if mark_clause then begin match Term.reason t with
      | Some (Bcp c) ->
        if Clause.attached c then (
          gc_mark_clause c
        )
      | Some (Bcp_lazy c) when Lazy.is_val c ->
        let lazy c = c in
        if Clause.attached c then (
          gc_mark_clause c
        );
      | _ -> ()
    end;
  )

and[@inline] gc_mark_atom ~mark_clause (a:atom) =
  gc_mark_term ~mark_clause (Atom.term a)

(* remove some learnt clauses, and the terms that are not reachable from
   any clause.
   The number of learnt clauses after reduction must be [downto] *)
let gc_clauses (env:t) ~down_to : unit =
  Log.debugf 2 (fun k->k"@{<Yellow>## gc_clauses@}");
  assert (Stack.is_empty env.clauses_to_add);
  env.n_gc_c <- env.n_gc_c + 1;
  (* remove some clauses *)
  let n_clauses = Vec.size env.clauses_learnt in
  assert (down_to <= n_clauses);
  Log.debugf 4
    (fun k->k"(@[gc_clauses.remove_learnt@ :n_total %d@ :downto %d@])" n_clauses down_to);
  (* mark terms of the trail alive, as well as clauses that propagated them,
     and mark permanent clauses *)
  Vec.iter (gc_mark_term ~mark_clause:true) env.trail;
  Stack.iter gc_mark_clause env.clauses_root;
  Vec.iter gc_mark_clause env.clauses_hyps;
  Vec.iter gc_mark_clause env.clauses_temp;
  (* sort learnt clauses by decreasing activity, but put marked clauses first *)
  Vec.sort env.clauses_learnt
    (fun c1 c2 -> CCFloat.compare (Clause.activity c2)(Clause.activity c1));
  (* collect learnt clauses *)
  let kept_clauses = Vec.create() in (* low activity, but needed *)
  while Vec.size env.clauses_learnt > 0 &&
        Vec.size env.clauses_learnt + Vec.size kept_clauses > down_to do
    let c = Vec.pop env.clauses_learnt in
    if Clause.gc_marked c then (
      Vec.push kept_clauses c; (* keep this one, it's alive *)
    ) else (
      (* remove the clause *)
      Log.debugf 15 (fun k->k"(@[gc_clauses.remove_clause@ %a@ :activity %f@])"
                        Clause.debug c (Clause.activity c));
      Clause.set_deleted c;
      env.n_deleted_c <- env.n_deleted_c + 1;
    )
  done;
  Vec.append env.clauses_learnt kept_clauses;
  (* mark terms from learnt clauses which are still alive *)
  Vec.iter gc_mark_clause env.clauses_learnt;
  (* collect dead terms *)
  CCVector.iter
    (fun (module P : Plugin.S) ->
       let n = P.gc_all() in
       env.n_deleted_t <- env.n_deleted_t + n)
    env.plugins;
  (* unmark clauses for next GC *)
  Stack.iter Clause.gc_unmark env.clauses_root;
  Vec.iter Clause.gc_unmark env.clauses_temp;
  Vec.iter Clause.gc_unmark env.clauses_hyps;
  Vec.iter Clause.gc_unmark env.clauses_learnt;
  ()

(* GC all terms that are neither in the trail nor in any active clause *)
let gc_terms (env:t) : unit =
  Log.debugf 2 (fun k->k"@{<Yellow>## gc_terms@}");
  env.n_gc_t <- env.n_gc_t + 1;
  assert (Stack.is_empty env.clauses_to_add);
  (* marking *)
  Vec.iter (gc_mark_term ~mark_clause:false) env.trail;
  let f_clause c = Array.iter (gc_mark_atom ~mark_clause:false) c.c_atoms in
  Stack.iter f_clause env.clauses_root;
  Stack.iter f_clause env.clauses_to_add;
  Vec.iter f_clause env.clauses_hyps;
  Vec.iter f_clause env.clauses_temp;
  Vec.iter f_clause env.clauses_learnt;
  (* collect dead terms *)
  CCVector.iter
    (fun (module P : Plugin.S) ->
       let n = P.gc_all() in
       env.n_deleted_t <- env.n_deleted_t + n)
    env.plugins;
  ()

(* check if time/memory limits are exceeded;
   raise exception to exit *)
let check_limits ~time ~memory () =
  let t = Sys.time () in
  let heap_size = (Gc.quick_stat ()).Gc.heap_words in
  let s = float heap_size *. float Sys.word_size /. 8. in
  if t > time then (
    raise Out_of_time
  ) else if s > memory then (
    raise Out_of_space
  )

let pp_progress (env:t) : unit =
  Printf.printf "\r\027[K[%.2fs] [start %d|confl %d|decision %d|props %d|\
                 gc_c %d|del_c %d|gc_t %d|del_t %d]%!"
    (Sys.time ()) env.starts env.conflicts env.decisions env.propagations
    env.n_gc_c env.n_deleted_c env.n_gc_t env.n_deleted_t

(* do some amount of search, until the number of conflicts or clause learnt
   reaches the given parameters *)
let search (env:t) ~gc ~time ~memory ~progress ?switch n_of_conflicts : unit =
  Log.debugf 5
    (fun k->k "(@[@{<yellow>solver.search@}@ :nconflicts %d@])" n_of_conflicts);
  let conflictC = ref 0 in
  env.starts <- env.starts + 1;
  while true do
    Log.debugf 50
      (fun k->k "(@[cur-heap@ %a@])" (Util.pp_iter Term.pp) @@ H.to_iter env.term_heap);
    begin match propagate env with
      | Some confl -> (* Conflict *)
        incr conflictC;
        (* attach_clause env confl; (* NOTE: better learn only learnt clause *) *)
        add_conflict env confl
      | None ->
        (* No conflict after propagation *)
        assert (fully_propagated env);
        if H.is_empty env.term_heap then (
          Log.debugf 3 (fun k->k"@{<yellow>found SAT@}");
          raise Sat;
        );
        (* should we restart? *)
        if n_of_conflicts > 0 && !conflictC >= n_of_conflicts then (
          Log.debug info "Restarting…";
          cancel_until env (base_level env);
          raise Restart
        );
        (* if decision_level() = 0 then simplify (); *)

        (* check time/memory limits every 2^k rounds *)
        if Util.Switch.activated_opt switch then raise Out_of_time;
        if env.conflicts = ((env.conflicts lsr 8) lsl 8) then (
          if progress then pp_progress env;
          check_limits ~time ~memory ();

          (* GC terms from time to time *)
          if gc &&
             env.conflicts > 0 &&
             env.conflicts = ((env.conflicts lsr 13) lsl 13) then (
            gc_terms env;
          )
        );

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
    begin match Atom.eval a with
      | Eval_unknown -> err_undecided_lit a.a_term
      | Eval_into(b, l) ->
        (* level is highest level of terms used to eval into [b] *)
        let lvl = level_subs l in
        Value.as_bool_exn b, lvl
    end
  )

let[@inline] eval a = fst (eval_level a)

let[@inline] unsat_conflict (env:t) = env.unsat_conflict

(* extract model *)
let model (env:t) : assignment_view list =
  Vec.fold
    (fun acc t -> match Term.value t with
       | None -> assert false
       | Some value ->
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
let solve
    ?(gc=true)
    ?(restarts=true)
    ?(time=max_float)
    ?(memory=max_float)
    ?(progress=false)
    ?switch
    (env:t)
  : unit =
  Log.debugf 2 (fun k->k"@{<Green>#### Solve@}");
  if is_unsat env then (
    raise Unsat;
  );
  let _alarm_progress =
    if progress then Some (Gc.create_alarm (fun () -> pp_progress env)) else None
  in
  (* initial limits for conflicts and learnt clauses *)
  let n_of_conflicts = ref (to_float env.restart_first) in
  let n_of_learnts =
    ref (CCFloat.max 50. ((to_float (nb_clauses env)) *. env.learntsize_factor))
  in
  let rec loop () =
    if Util.Switch.activated_opt switch then raise Out_of_time
    else (
      match
        let nconf = if restarts then to_int !n_of_conflicts else max_int in
        search env ~gc ~time ~memory ~progress ?switch nconf
      with
      | () -> ()
      | exception Restart ->
        (* garbage collect clauses, if needed *)
        if gc &&
           !n_of_learnts >= 0. &&
           float(Vec.size env.clauses_learnt - Vec.size env.trail) >= !n_of_learnts
        then (
          let n = (to_int !n_of_learnts) + 1 in
          gc_clauses env ~down_to:n;
        );

        (* increment parameters to ensure termination *)
        n_of_conflicts := !n_of_conflicts *. env.restart_inc;
        n_of_learnts   := !n_of_learnts *. env.learntsize_inc;
        (* diminish by how much n_of_learnts increases *)
        env.learntsize_inc <- 1. +. (env.learntsize_inc -. 1.) /. 1.3 ;
        loop()
      | exception Sat -> check_sat ()
    )
  and check_sat () =
    assert (fully_propagated env);
    begin match final_check env with
      | FC_sat -> () (* done *)
      | FC_conflict c ->
        Log.debugf info
          (fun k -> k "(@[solver.theory_conflict_clause@ %a@])" Clause.debug c);
        Stack.push c env.clauses_to_add;
        loop()
      | FC_propagate ->
        loop() (* need to propagate *)
    end
  in
  CCFun.finally
    ~h:(fun () -> CCOpt.iter Gc.delete_alarm _alarm_progress)
    ~f:loop

let assume env ?tag (cnf:atom list list) =
  List.iter
    (fun l ->
       let c = Clause.make ?tag l Hyp in
       Log.debugf debug (fun k->k "(@[solver.assume_clause@ %a@])" Clause.debug c);
       Stack.push c env.clauses_to_add)
    cnf

(* create a factice decision level for local assumptions *)
let push (env:t) : unit =
  Log.debug debug "(solver.push)";
  cancel_until env (base_level env);
  Log.debugf 30
    (fun k->k"(@[solver.push.status@ :prop_head %d/%d@ :trail (@[<hv>%a@])@])"
        env.bcp_head env.th_head (Vec.pp ~sep:"" Term.debug) env.trail);
  begin match propagate env with
    | Some c -> report_unsat env c
    | None ->
      Log.debugf 30
        (fun k -> k "(@[<v>solver.current_trail@ (@[<hv>%a@])@])"
            (Vec.pp ~sep:"" Term.debug) env.trail);
      new_decision_level env;
      Log.debugf info
        (fun k->k"(@[<hv>solver.create_new_user_level@ :cur-level %d@])" (decision_level env));
      Vec.push env.user_levels (Vec.size env.clauses_temp);
      assert (decision_level env = base_level env)
  end

(* pop the last factice decision level *)
let pop (env:t) : unit =
  if base_level env = 0 then (
    Log.debug warn "Cannot pop (already at level 0)";
  ) else (
    Log.debug info "(solver.pop)";
    assert (base_level env > 0);
    env.unsat_conflict <- None;
    let n = Vec.pop env.user_levels in (* before the [cancel_until]! *)
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

exception Bad_model of string

let bad_model msg = raise (Bad_model msg)
let bad_modelf msg = Fmt.ksprintf ~f:bad_model msg

(* Check satisfiability *)
let check_clause (c:clause) : unit =
  let res = CCArray.exists Atom.is_true c.c_atoms in
  if not res then (
    bad_modelf "Clause not satisfied: @[<hov>%a@]" Clause.debug c
  )

let check_term (t:term) : unit = match Term.value t, Term.eval t with
  | None, Eval_unknown ->
    () (* no value, can happen if atom only occurs in trivial clauses *)
  | None, Eval_into _ -> ()
  | Some _, Eval_unknown -> ()
  | Some v1, Eval_into (v2,_) ->
    if not (Value.equal v1 v2) then (
      bad_modelf "@[<hv>inconsistency: term `%a`@ :assigned-to %a@ :eval-to %a@]"
        Term.debug t Value.pp v1 Value.pp v2
    )

let[@inline] check_terms (env:t) = iter_terms env check_term

let[@inline] check_vec v = Vec.iter check_clause v

let[@inline] check_stack s = Stack.iter check_clause s

let check (env:t) : (unit,string) result =
  try
    assert (Stack.is_empty env.clauses_to_add);
    check_stack env.clauses_root;
    check_vec env.clauses_hyps;
    check_vec env.clauses_learnt;
    check_vec env.clauses_temp;
    check_terms env;
    Ok ()
  with Bad_model msg -> Error msg

(* Unsafe access to internal data *)

let hyps env = env.clauses_hyps
let history env = env.clauses_learnt
let temp env = env.clauses_temp
let trail env = env.trail

(* stats *)

let pp_stats out (s:t): unit =
  Fmt.fprintf out
    "(@[stats@ :n_conflicts %d@ \
     :n_decisions %d@ :n_bool_decisions %d@ :n_propagations %d@ :n_restarts %d@ \
     :n_learnt %d@ :n_initial %d@ \
     @[:gc_c %d@ :deleted_c %d@]@ \
     @[:gc_t %d :deleted_t %d@]@])"
    s.conflicts s.decisions s.bool_decisions s.propagations s.starts s.n_learnt
    (Vec.size s.clauses_hyps) s.n_gc_c s.n_deleted_c s.n_gc_t s.n_deleted_t

let[@inline] clear_progress () = print_string "\r\027[K";
