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
      (fun acc a ->
         if Atom.marked a then Atom.Set.add a acc else (Atom.mark a; acc))
      Atom.Set.empty c.c_atoms
  in
  Array.iter Atom.unmark c.c_atoms;
  Atom.Set.to_list r

let find_absurd (c:clause) : atom list =
  Array.fold_left
    (fun acc a -> if Atom.is_absurd a then a::acc else acc) [] c.c_atoms

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
  | Simplify of {
      init: t;
      duplicates: atom list;
      absurd: atom list;
    }
  | Hyper_res of {
      init: t;
      steps: premise_step list; (* list of steps to apply to [init] *)
    }

let[@inline] conclusion n = n.conclusion
let[@inline] step n = n.step

let pp_clause_step out = function
  | Step_resolve {c;pivot} ->
    Fmt.fprintf out "(@[res@ %a@ :on %a@])" Clause.debug c Term.debug pivot

let debug_step out (s:step) : unit = match s with
  | Hypothesis -> Fmt.string out "hypothesis"
  | Assumption -> Fmt.string out "assumption"
  | Lemma l -> Fmt.fprintf out "(@[lemma %a@])" Lemma.pp l
  | Simplify s ->
    Fmt.fprintf out "(@[<hv>simplify@ :from %a@ :dups (@[%a@])@ :absurd (@[%a@])@])"
      Clause.debug s.init
      Clause.debug_atoms s.duplicates Clause.debug_atoms s.absurd
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

  (* find pivots for resolving [l] with [init] *)
  let find_pivots (init:clause) (l:clause list) : premise_step list =
    Array.iter Atom.mark init.c_atoms;
    let steps =
      List.map
        (fun c ->
           let pivot =
             match
               Iter.of_array c.c_atoms
               |> Iter.filter
                 (fun a -> Atom.marked (Atom.neg a))
               |> Iter.to_list
             with
               | [a] -> a
               | [] ->
                 Util.errorf "(@[proof.expand.pivot_missing@ %a@])"
                   Clause.debug c
               | pivots ->
                 Util.errorf "(@[proof.expand.multiple_pivots@ %a@ :pivots %a@])"
                   Clause.debug c Clause.debug_atoms pivots
           in
           Array.iter Atom.mark c.c_atoms; (* add atoms to result *)
           Atom.unmark pivot;
           Atom.unmark (Atom.neg pivot);
           Step_resolve {pivot=Atom.term pivot;c})
        l
    in
    (* cleanup *)
    Array.iter Atom.unmark init.c_atoms;
    List.iter (fun c -> Array.iter Atom.unmark c.c_atoms) l;
    steps

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
        let absurd = find_absurd c in
        mk_node conclusion (Simplify {init=c; duplicates; absurd})
      | P_raw_steps [] ->
        Util.errorf "proof: resolution error (no premise)@ %a@ :premise %a"
          Clause.debug conclusion Premise.pp conclusion.c_premise
      | P_raw_steps [_] ->
        Util.errorf "proof: resolution error (wrong hyperres)@ %a@ :premise %a"
          Clause.debug conclusion Premise.pp conclusion.c_premise
      | P_raw_steps ((c::r) as l) ->
        Log.debugf 30 (fun k->k"(@[<hv>proof.expanding.raw@ %a@])"
            (Util.pp_list Clause.debug ) l);
        (* find pivots for hyper-resolution *)
        let steps = find_pivots c r in
        (* update premise to memoize proof *)
        conclusion.c_premise <- Premise.steps c steps;
        let step = Hyper_res {init=c; steps} in
        mk_node conclusion step
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
                   c :: acc
                 ))
              []
              c.c_atoms
          in
          let premise = Premise.raw_steps (c :: premise) in
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
             assert (Atom.is_false a || Atom.can_eval_to_false a);
             recompute_update_proof_of_atom a Value.false_ :: acc)
          [] conflict.c_atoms
      in
      let premise = Premise.raw_steps (conflict :: premise) in
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
  | Simplify _ | Hyper_res _ -> false

let[@inline] parents_steps l : t list =
  List.map
    (function Step_resolve {c;_} -> c)
    l

let[@inline] parents_raw_steps l : t list = l

let parents = function
  | Hypothesis
  | Assumption
  | Lemma _ -> []
  | Simplify {init=p;_} -> [p]
  | Hyper_res {init;steps} ->
    init :: parents_steps steps

let expl = function
  | Hypothesis -> "hypothesis"
  | Assumption -> "assumption"
  | Lemma _ -> "lemma"
  | Simplify _ -> "simplify"
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
          | Simplify {init=p1;_} ->
            Stack.push (Enter p1) s
          | Hyper_res {init;steps} ->
            Stack.push (Enter init) s;
            List.iter
              (function
                | Step_resolve {c;_} -> Stack.push (Enter c) s)
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
  val check_step : t -> unit
  val check : t -> unit
end = struct
  let[@inline] set_of_c (c:clause): Atom.Set.t =
    Iter.of_array c.c_atoms |> Atom.Set.of_seq

  let pp_a_set out (a:Atom.Set.t) : unit =
    Fmt.fprintf out "(@[<v>%a@])"
      (Util.pp_seq ~sep:" ∨ " Atom.debug) (Atom.Set.to_seq a)

  (* state for one hyper{resolution,paramodulation} step *)
  type state = {
    killed: Term.Set.t;
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
                  let t = Atom.term a in
                  if Term.Set.mem t st.killed then st
                  else if Term.equal pivot t then (
                    if not (Atom.Set.mem (Atom.neg a) st.cur) then (
                      Util.errorf
                        "(@[<hv>proof.check_hyper_res.pivot_not_found@ \
                         :pivot %a@ :c1 %a@ :c2 %a@])"
                        Term.debug pivot pp_a_set st.cur Clause.debug c2
                    );
                    { cur=Atom.Set.remove (Atom.neg a) st.cur; killed=Term.Set.add t st.killed }
                  ) else (
                    { st with cur=Atom.Set.add a st.cur }
                  ))
               st c2.c_atoms
         end)
      {cur=set_of_c init; killed=Term.Set.empty}
      steps

  let check_node (n:node) : unit =
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
    let concl = conclusion n in
    let step = step n in
    Log.debugf 15 (fun k->k"(@[<hv>proof.check.step@ :concl %a@ :step %a@])"
        Clause.debug concl debug_step step);
    begin match step with
      | Lemma _ -> () (* TODO: check lemmas *)
      | Hypothesis -> ()
      | Assumption -> ()
      | Simplify s ->
        let dups' = find_duplicates s.init in
        if not (Atom.Set.equal
              (Atom.Set.of_list s.duplicates) (Atom.Set.of_list dups')) then (
          Util.errorf
            "(@[<hv>proof.check.invalid_simplify_step@ :from %a@ :to %a@ :dups1 %a@ :dups2 %a@])"
            Clause.debug s.init Clause.debug concl Clause.debug_atoms s.duplicates
            Clause.debug_atoms dups'
        );
        begin match CCList.find_pred (fun a -> not (Atom.is_absurd a)) s.absurd with
          | None -> ()
          | Some a ->
            Util.errorf
              "(@[<hv>proof.check.invalid_simplify_step@ :in %a@ :not-absurd %a@])"
              Clause.debug s.init Atom.debug a
        end;
        (* remove absurd literals, and check equality modulo duplicates *)
        let c = set_of_c s.init in
        let c = Atom.Set.diff c (Atom.Set.of_list s.absurd) in
        check_same_set ~ctx:"in-dedup" c ~expect:(set_of_c concl)
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
    end

  let check_step (p:t) : unit = check_node @@ expand p

  let check (p:t) : unit =
    iter check_node p
end

include Check


