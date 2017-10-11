(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

open Solver_types

module Fmt = CCFormat

let merge = List.merge Atom.compare

let _c = ref 0
let fresh_pcl_name () = incr _c; "R" ^ (string_of_int !_c)

(* find set of duplicates in [c] *)
let find_duplicates (c:clause) : atom list =
  let r =
    Array.fold_left
      (fun acc a -> if Atom.marked a then a :: acc else (Atom.mark a; acc))
      [] c.c_atoms
  in
  Array.iter Atom.unmark c.c_atoms;
  r

(* Comparison of clauses by their lists of atoms *)
let[@inline] cl_list_eq c d = CCList.equal Atom.equal c d
let[@inline] prove conclusion = conclusion

(* Interface exposed *)
type t = clause
and node = {
  conclusion : clause;
  step : step;
}
and step =
  | Hypothesis
  | Assumption
  | Lemma of lemma
  | Deduplicate of t * atom list
  | Hyper_res of {
      init: t;
      steps: premise_step list; (* list of steps to apply to [init] *)
    }

let[@inline] conclusion n = n.conclusion
let[@inline] step n = n.step

let pp_clause_step out = function
  | Step_resolve {c;pivot} ->
    Fmt.fprintf out "(@[res@ %a@ :on %a@])" Clause.debug c Term.debug pivot
  | Step_paramod pa ->
    begin match pa.pa_learn with
      | None ->
        Fmt.fprintf out "(@[param_false@ %a@ :by %a@])"
          Atom.debug pa.pa_init Paramod.Trace.pp pa.pa_trace
      | Some learn ->
        Fmt.fprintf out "(@[param@ %a@ :into %a@ :by %a@])"
          Atom.debug pa.pa_init Atom.debug learn Paramod.Trace.pp pa.pa_trace
    end

let debug_step out (s:step) : unit = match s with
  | Hypothesis -> Fmt.string out "hypothesis"
  | Assumption -> Fmt.string out "assumption"
  | Lemma l -> Fmt.fprintf out "(@[lemma %a@])" Lemma.pp l
  | Deduplicate (c,l) ->
    Fmt.fprintf out "(@[<hv>dedup@ :from %a@ :on (@[%a@])@])" Clause.debug c
      Clause.debug_atoms l
  | Hyper_res {init;steps} ->
    Fmt.fprintf out "(@[<hv>hyper_res@ :init %a@ %a@])"
      Clause.debug init (Util.pp_list pp_clause_step) steps

let[@inline] mk_node conclusion step = {conclusion; step}

module Reconstruct : sig
  val expand : t -> node
  val recompute_update_proof_of_atom : atom -> value -> t
  val prove_unsat : clause -> t
  val prove_atom : atom -> t option
end = struct
  let[@inline] to_clean_clause (c:clause) : atom Sequence.t =
    Sequence.of_array c.c_atoms

  (* atoms to cleanup in this step *)
  let to_clean_step (s:raw_premise_step) : atom Sequence.t = match s with
    | RP_resolve c -> to_clean_clause c
    | RP_paramod pa ->
      fun yield ->
        yield pa.pa_init;
        CCOpt.iter yield pa.pa_learn;
        begin
          Paramod.Trace.pc_seq pa.pa_trace
          |> Sequence.flat_map_l Paramod.PClause.guard
          |> Sequence.map Atom.neg
          |> Sequence.iter yield
        end

  let to_clean_steps (l:_ list): atom Sequence.t =
    Sequence.of_list l
    |> Sequence.flat_map to_clean_step

  (* atoms added to the clause by this step *)
  let atom_of_step (p:raw_premise_step) : atom Sequence.t = match p with
    | RP_resolve c -> Sequence.of_array c.c_atoms
    | RP_paramod pa ->
      (* simulate [lhs = rhs <- guard] as [¬ lhs | rhs | ¬guard] *)
      Sequence.of_list
        [ Sequence.return (Atom.neg pa.pa_init);
          CCOpt.to_seq pa.pa_learn;
          (Paramod.Trace.pc_seq pa.pa_trace
           |> Sequence.flat_map_l Paramod.PClause.guard
           |> Sequence.map Atom.neg);
        ]
      |> Sequence.flatten

  (* find pivots of hyper resolution, and sort steps in a valid order *)
  let rebuild_steps (init:clause) (l:raw_premise_step list) : premise_step list =
    (* graph that connects atoms to the step that can remove them,
       if they are not present in the final clause *)
    let a_graph = Atom.Tbl.create 32 in
    Array.iter (fun a -> Atom.Tbl.add a_graph a []; Atom.mark a) init.c_atoms;
    List.iter
      (fun step ->
         begin match step with
           | RP_paramod pa -> 
             if not (Atom.marked pa.pa_init) then (
               Util.errorf "(@[proof.expand.rewrite_absent_atom@ %a@ :with %a@])"
                 Atom.pp pa.pa_init Premise.pp_raw_premise_step step
             );
             Atom.Tbl.replace a_graph pa.pa_init
               (step :: Atom.Tbl.get_or ~default:[] a_graph pa.pa_init);
             (* mark atoms to remove *)
             CCOpt.iter Atom.mark pa.pa_learn;
             begin
               Paramod.Trace.pc_seq pa.pa_trace
               |> Sequence.flat_map_l Paramod.PClause.guard
               |> Sequence.iter Atom.mark_neg
             end;
           | RP_resolve c ->
             let elim_sth = ref false in
             Array.iter
               (fun a ->
                  let a_neg = Atom.neg a in
                  (* is [a] used to remove [a_neg] from an intermediate clause
                     in the proof? *)
                  if Atom.marked a_neg then (
                    if !elim_sth then (
                      Util.errorf "(@[proof.expand.multiple_pivots@ %a@])"
                        Premise.pp_raw_premise_step step
                    );
                    elim_sth := true;
                    Atom.Tbl.replace a_graph a_neg
                      (step :: Atom.Tbl.get_or ~default:[] a_graph a_neg);
                  ) else (
                    (* [a] belongs in the intermediate clause,
                       and might be removed by later steps. *)
                    Atom.mark a;
                  ))
               c.c_atoms;
             (* check that one "pivot" was found *)
             if not !elim_sth then (
               Util.errorf "(@[proof.expand.pivot_missing@ %a@])"
                 Premise.pp_raw_premise_step step
             );
         end)
      l;
    (* cleanup *)
    begin
      (Sequence.append (to_clean_clause init) (to_clean_steps l))
      |> Sequence.iter Atom.unmark
    end;
    (* traverse the graph in topological order to rebuild a correct proof,
       and find pivots properly *)
    let rec aux acc (a:atom) : premise_step list =
      if Atom.marked a then acc
      else (
        Atom.mark a;
        (* explore steps which remove [a] from final clause, if any *)
        let l = Atom.Tbl.get_or ~default:[] a_graph a in
        List.fold_left
          (fun acc step ->
             begin match step with
               | RP_paramod pa ->
                 let acc = CCOpt.fold aux acc pa.pa_learn in
                 let acc =
                   Paramod.Trace.pc_seq pa.pa_trace
                   |> Sequence.flat_map_l Paramod.PClause.guard
                   |> Sequence.map Atom.neg
                   |> Sequence.fold aux acc
                 in
                 Step_paramod pa :: acc
               | RP_resolve c ->
                 let pivot = a.a_term in
                 let acc =
                   Array.fold_left
                     (fun acc a' ->
                        if Term.equal pivot (Atom.term a') then acc
                        else aux acc a')
                     acc c.c_atoms
                 in
                 Step_resolve {pivot;c} :: acc
             end)
          acc l
      )
    in
    let steps = Array.fold_left aux [] init.c_atoms in
    (* cleanup *)
    begin
      (Sequence.append (to_clean_clause init) (to_clean_steps l))
      |> Sequence.iter Atom.unmark
    end;
    steps

  (* debug raw premise, verbose *)
  let debug_raw_premise_step out = function
    | RP_resolve c -> Fmt.fprintf out "(@[resolve %a@])" Clause.debug c
    | RP_paramod pa ->
      begin match pa.pa_learn with
        | None ->
          Fmt.fprintf out "(@[paramod_away %a→⊥@ :with %a@])"
            Atom.debug pa.pa_init Paramod.Trace.pp pa.pa_trace
        | Some learn ->
          Fmt.fprintf out "(@[paramod %a@ → %a@ :with %a@])"
            Atom.debug pa.pa_init Atom.debug learn Paramod.Trace.pp pa.pa_trace
      end

  let expand (conclusion:clause) : node =
    Log.debugf 15 (fun k -> k "(@[proof.expanding@ %a@])" Clause.debug conclusion);
    begin match conclusion.c_premise with
      | Lemma l -> mk_node conclusion (Lemma l)
      | Hyp -> mk_node conclusion Hypothesis
      | Local -> mk_node conclusion Assumption
      | P_steps {init;steps} ->
        let step = Hyper_res {init;steps} in
        mk_node conclusion step
      | Simplify c ->
        let duplicates = find_duplicates c in
        mk_node conclusion (Deduplicate (c, duplicates))
      | P_raw_steps [] ->
        Util.errorf "proof: resolution error (no premise)@ %a@ :premise %a"
          Clause.debug conclusion Premise.pp conclusion.c_premise
      | P_raw_steps [_] ->
        Util.errorf "proof: resolution error (wrong hyperres)@ %a@ :premise %a"
          Clause.debug conclusion Premise.pp conclusion.c_premise
      | P_raw_steps ((RP_resolve c::r) as l) ->
        Log.debugf 30 (fun k->k"(@[<hv>proof.expanding.raw@ %a@])"
            (Util.pp_list debug_raw_premise_step) l);
        (* find pivots for hyper-resolution *)
        let steps = rebuild_steps c r in
        (* update premise to memoize proof *)
        conclusion.c_premise <- Premise.steps c steps;
        let step = Hyper_res {init=c; steps} in
        mk_node conclusion step
      | P_raw_steps (c::_) ->
        Util.errorf "proof: resolution error (wrong first premise)@ %a"
          Premise.pp_raw_premise_step c
    end

  (* update reason of a *)
  let[@inline] set_atom_reason (a:atom) (r:reason) : unit =
    begin match a.a_term.t_assign with
      | TA_none -> assert false
      | TA_assign{value;_} ->
        a.a_term.t_assign <- TA_assign{value;reason=r;level=0}
    end

  (* update proof of atom [a] with additional information at level 0 *)
  let rec recompute_update_proof_of_atom (a:atom) (v:value) : clause =
    assert (Atom.level a >= 0);
    begin match Atom.reason a with
      | Some (Bcp c) ->
        Log.debugf 10
          (fun k -> k "(@[<hv>proof.analyzing@ :atom %a@ :val %a@ :bcp %a@])"
              Atom.debug a Value.pp v Clause.debug c);
        if Array.length c.c_atoms = 1 then (
          Log.debugf 15 (fun k -> k "(@[<hv>proof.analyze.keep_old_reason@ %a@])" Atom.debug a);
          c
        ) else (
          let premise =
            Array.fold_left
              (fun acc b ->
                 if Atom.equal (Atom.neg a) b then acc
                 else (
                   let c = recompute_update_proof_of_atom b Value.false_ in
                   RP_resolve c :: acc
                 ))
              []
              c.c_atoms
          in
          let premise = Premise.raw_steps (RP_resolve c :: premise) in
          let c' = Clause.make [Atom.neg a] premise in
          (* update reason *)
          set_atom_reason a (Bcp c');
          Log.debugf 15
            (fun k -> k "(@[<hv>proof.analyze.new_reason@ %a@ :bcp %a@])" Atom.debug a Clause.debug c');
          c'
        )
      | _ ->
        Util.errorf "(@[proof.analyze.cannot_prove_atom@ %a@])" Atom.debug a
    end

  let prove_unsat (conflict:clause) : clause =
    if Array.length conflict.c_atoms = 0 then conflict
    else (
      Log.debugf 2 (fun k -> k "(@[@{<Green>proof.proving_unsat@}@ :from %a@])" Clause.debug conflict);
      let premise =
        Array.fold_left
          (fun acc a ->
             assert (Atom.is_false a);
             RP_resolve (recompute_update_proof_of_atom a Value.false_) :: acc)
          [] conflict.c_atoms
      in
      let premise = Premise.raw_steps (RP_resolve conflict :: premise) in
      let res = Clause.make [] premise in
      Log.debugf 2 (fun k -> k "(@[@{<Green>proof.proof_found@}@ %a@ :premise %a@])"
          Clause.debug res Premise.pp premise);
      res
    )

  let prove_atom a =
    if Atom.is_true a && Atom.level a = 0 then (
      Some (recompute_update_proof_of_atom a Value.true_)
    ) else (
      None
    )
end

include Reconstruct

(* Proof nodes manipulation *)
let is_leaf = function
  | Hypothesis
  | Assumption
  | Lemma _ -> true
  | Deduplicate _ | Hyper_res _ -> false

let[@inline] parents_steps l : t list =
  CCList.flat_map
    (function
      | Step_resolve {c;_} -> [c]
      | Step_paramod pa -> Paramod.Trace.clauses pa.pa_trace |> Clause.Set.to_list)
    l

let[@inline] parents_raw_steps l : t list =
  CCList.filter_map
    (function
      | RP_resolve c -> Some c
      | _ -> None)
    l

let parents = function
  | Hypothesis
  | Assumption
  | Lemma _ -> []
  | Deduplicate (p, _) -> [p]
  | Hyper_res {init;steps} ->
    init :: parents_steps steps

let expl = function
  | Hypothesis -> "hypothesis"
  | Assumption -> "assumption"
  | Lemma _ -> "lemma"
  | Deduplicate  _ -> "deduplicate"
  | Hyper_res _ -> "hyper_res"

(* Compute unsat-core *)
let unsat_core proof =
  (* visit recursively the proof of [c] to find the unsat core (the leaves)
     @param res partial result (subset of unsat-core)
     @param visited set of clauses for which the `visited` flag should be cleared
     @param k continuation to call with results *)
  let rec aux res visited c k =
    if Clause.visited c then (
      k res visited
    ) else (
      Clause.mark_visited c;
      begin match c.c_premise with
        | Hyp | Local -> k (c :: res) visited
        | Lemma _ -> k res visited (* ignore lemmas *)
        | Simplify d -> aux res (c :: visited) d k
        | P_steps {init;steps} ->
          aux_l res (init::visited) (parents_steps steps) k
        | P_raw_steps cs -> aux_l res (c::visited) (parents_raw_steps cs) k
      end
    )
  and aux_l res visited l k = match l with
    | [] -> k res visited
    | c :: r ->
      aux res visited c
        (fun res visited -> aux_l res visited r k)
  in
  let res, visited = aux [] [] proof CCPair.make in
  List.iter Clause.clear_visited res;
  List.iter Clause.clear_visited visited;
  res

(* Iterate on proofs *)
module H = Clause.Tbl

type task =
  | Enter of t
  | Leaving of t

let[@inline] pop_opt s = try Some (Stack.pop s) with Stack.Empty -> None

(* helper for folding over proofs-as-DAGs *)
let rec fold_aux s h f acc =
  begin match pop_opt s with
    | None -> acc
    | Some (Leaving c) ->
      H.add h c true;
      fold_aux s h f (f acc (expand c))
    | Some (Enter c) ->
      if not (H.mem h c) then (
        Stack.push (Leaving c) s;
        let node = expand c in
        begin match node.step with
          | Deduplicate (p1, _) ->
            Stack.push (Enter p1) s
          | Hyper_res {init;steps} ->
            Stack.push (Enter init) s;
            List.iter
              (function
                | Step_resolve {c;_} -> Stack.push (Enter c) s
                | Step_paramod pa ->
                  begin
                    Paramod.Trace.pc_seq pa.pa_trace
                    |> Sequence.map Paramod.PClause.to_clause
                    |> Sequence.iter (fun c -> Stack.push (Enter c) s)
                  end)
              steps;
          | Hypothesis | Assumption | Lemma _ -> ()
        end
      );
      fold_aux s h f acc
  end

let fold f acc p =
  let h = H.create 42 in
  let s = Stack.create () in
  Stack.push (Enter p) s;
  fold_aux s h f acc

let[@inline] iter f p = fold (fun () x -> f x) () p

module Check : sig
  val check : t -> unit
end = struct
  let[@inline] set_of_c (c:clause): Atom.Set.t =
    Sequence.of_array c.c_atoms |> Atom.Set.of_seq

  let pp_a_set out (a:Atom.Set.t) : unit =
    Fmt.fprintf out "(@[<v>%a@])"
      (Util.pp_seq ~sep:" ∨ " Atom.debug) (Atom.Set.to_seq a)

  (* paramodulate term *)
  let perform_paramod (pt:paramod_trace) : term =
    let module T = Paramod.Trace in
    let module PC = Paramod.PClause in
    let tbl = T.Tbl.create 16 in
    (* recursive checking that rewriting makes sense *)
    let rec aux_trace (pt:T.t) : term =
      begin match T.Tbl.get tbl pt with
        | Some t -> t (* checked already *)
        | None ->
          (* rewrite [lhs] using [steps] *)
          let u = List.fold_left aux_step pt.pt_lhs pt.pt_steps in
          (* check we obtain the expected result *)
          if not (Term.equal u pt.pt_rhs) then (
            Util.errorf
              "(@[<hv>proof.check.paramod.mismatch@ :lhs %a@ :into %a@ :expected %a@])"
              Term.debug pt.pt_lhs Term.debug u Term.debug pt.pt_rhs
          );
          u
      end
    (* rewrite [t] using the steps *)
    and aux_step (t:term) (s:Paramod.Step.t) : term = match s with
      | PS_sub {subs} ->
        let map =
          List.fold_left
            (fun m pt ->
               assert (not (Term.Map.mem pt.pt_lhs m));
               let rhs = aux_trace pt in
               Term.Map.add pt.pt_lhs rhs m)
            Term.Map.empty
            subs
        in
        Term.map t ~f:(fun t -> Term.Map.get_or ~default:t t map)
      | PS_paramod {pc} ->
        (* check that [pc.lhs] corresponds to our term *)
        if not (Term.equal t (PC.lhs pc)) then (
          Util.errorf
            "(@[<hv>proof.check.paramod_with.mismatch@ :t %a@ :pc %a@])"
            Term.debug t PC.debug pc
        );
        PC.rhs pc
    in
    aux_trace pt

  (* paramodulate atom *)
  let perform_paramod_atom (pa:paramod_atom) : atom =
    let sign = Atom.is_pos pa.pa_init in
    if not (Term.equal pa.pa_trace.pt_lhs (Atom.term pa.pa_init)) then (
      Util.errorf
        "(@[<hv>proof.check.paramod_atom.mismatch@ \
         :pa_init %a@ :pa-trace-lhs@])"
        Atom.debug pa.pa_init Term.debug pa.pa_trace.pt_lhs
    );
    (* rewrite term *)
    let t = perform_paramod pa.pa_trace in
    (* report sign *)
    if sign then Term.Bool.pa t else Term.Bool.na t

  (* state for one hyper{resolution,paramodulation} step *)
  type state = {
    cur: Atom.Set.t;
  }

  (* rebuild explicitely clauses by hyper-res;
       check they are not tautologies;
       return conclusion *)
  let perform_hyper_step (init:t) (steps:premise_step list) : state =
    List.fold_left
      (fun (st:state) step ->
         begin match step with
           | Step_resolve {pivot;c=c2} ->
             (* perform resolution with [c] over [pivot] *)
             Array.fold_left
               (fun st a ->
                  if Term.equal pivot (Atom.term a) then (
                    if not (Atom.Set.mem (Atom.neg a) st.cur) then (
                      Util.errorf
                        "(@[<hv>proof.check_hyper_res.pivot_not_found@ \
                         :pivot %a@ :c1 %a@ :c2 %a@])"
                        Term.debug pivot pp_a_set st.cur Clause.debug c2
                    );
                    { cur=Atom.Set.remove (Atom.neg a) st.cur; }
                  ) else (
                    { cur=Atom.Set.add a st.cur }
                  ))
               st c2.c_atoms
           | Step_paramod pa ->
             if not (Atom.Set.mem pa.pa_init st.cur) then (
               Util.errorf
                 "(@[<hv>proof.check_paramod.atom_not_present@ \
                  :atom %a@ :cur-clause %a@])"
                 Atom.debug pa.pa_init pp_a_set st.cur
             );
             let st = {
               cur=Atom.Set.remove pa.pa_init st.cur;
             } in
             (* do paramodulation *)
             let new_atom = perform_paramod_atom pa in
             (* add learnt atom *)
             let st = match pa.pa_learn with
               | None ->
                 if not (Atom.is_absurd new_atom) then (
                   Util.errorf
                     "(@[<hv>proof.check_paramod_away.atom_not_false@ \
                      :atom %a@ :rw_into %a@ :by %a@])"
                     Atom.debug pa.pa_init
                     Atom.debug new_atom Paramod.Trace.pp pa.pa_trace
                 );
                 st
               | Some learn ->
                 if not (Atom.equal learn new_atom) then (
                   Util.errorf
                     "(@[<hv>proof.check_paramod.wrong_atom@ \
                      :atom %a@ :expect %a@ :got %a@ :by %a@])"
                     Atom.debug pa.pa_init Atom.debug learn Atom.debug new_atom
                     Paramod.Trace.pp pa.pa_trace
                 );
                 {cur=Atom.Set.add learn st.cur}
             in
             (* also add the guards of the pclauses *)
             let st =
               Paramod.Trace.pc_seq pa.pa_trace
               |> Sequence.flat_map_l Paramod.PClause.guard
               |> Sequence.map Atom.neg
               |> Sequence.fold
                 (fun st a -> {cur=Atom.Set.add a st.cur})
                 st
             in
             st
         end)
      {cur=set_of_c init}
      steps

  let check (p:t) : unit =
    (* compare lists of atoms, ignoring order and duplicates *)
    let check_same_set ~ctx ~expect:c d =
      if not (Atom.Set.equal c d) then (
        Util.errorf
          "(@[<hv>proof.check.distinct_clauses@ :ctx %s@ \
           :c1(expect) %a@ :c2(got) %a@ :c1\\c2 %a@ :c2\\c1 %a@])"
          ctx pp_a_set c pp_a_set d
          pp_a_set (Atom.Set.diff c d)
          pp_a_set (Atom.Set.diff d c)
      );
    in
    let check_same_c ~ctx ~expect:c1 c2 =
      check_same_set ~ctx ~expect:(set_of_c c1) (set_of_c c2)
    in
    iter
      (fun n ->
         let concl = conclusion n in
         let step = step n in
         Log.debugf 15 (fun k->k"(@[<hv>proof.check.step@ :concl %a@ :step %a@])"
             Clause.debug concl debug_step step);
         begin match step with
           | Lemma _ -> () (* TODO: check lemmas *)
           | Hypothesis -> ()
           | Assumption -> ()
           | Deduplicate (c, dups) ->
             let dups' = find_duplicates c in
             if not (Atom.Set.equal (Atom.Set.of_list dups) (Atom.Set.of_list dups')) then (
               Util.errorf
                 "(@[<hv>proof.check.invalid_simplify_step@ :from %a@ :to %a@ :dups1 %a@ :dups2 %a@])"
                 Clause.debug c Clause.debug concl Clause.debug_atoms dups
                 Clause.debug_atoms dups'
             );
             check_same_c ~ctx:"in-dedup" c ~expect:concl
           | Hyper_res {init;steps} ->
             let st = perform_hyper_step init steps in
             check_same_set ~ctx:"in-res" st.cur ~expect:(set_of_c concl);
             (* check it's not a tautology *)
             Atom.Set.iter
               (fun a ->
                  if Atom.Set.mem (Atom.neg a) st.cur then (
                    Util.errorf
                      "(@[<hv>proof.check_hyper_res.clause_is_tautology@ \
                       :clause %a@])"
                      pp_a_set st.cur

                  ))
               st.cur;
             ()
         end)
      p
end

include Check


