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

type sorted_atom_list = atom list

type resolve_res = {
  resolve_atoms: sorted_atom_list;
  resolve_pivots: atom list; (* what were the pivot(s) atom(s) *)
}

(* Compute resolution of 2 clauses, which have been merged into a
   sorted list. Since atoms have an ordering where [a] and [¬a] are
   next to each other, it's easy to detect the presence of both in the merge.

   precondition: l is sorted *)
let resolve (l:sorted_atom_list) : resolve_res =
  (* pivots: atoms on which resolution was done
     concl: remaining atoms for the conclusion *)
  let rec aux pivots concl = function
    | [] -> pivots, concl
    | [a] -> pivots, a :: concl
    | a :: b :: r ->
      if Atom.equal a b then (
        aux pivots concl (b::r) (* remove dup *)
      ) else if Atom.equal (Atom.neg a) b then (
        aux (Atom.abs a :: pivots) concl r (* resolve *)
      ) else (
        aux pivots (a :: concl) (b :: r) (* add to conclusion *)
      )
  in
  let pivots, new_clause = aux [] [] l in
  { resolve_pivots=pivots;
    resolve_atoms=List.rev new_clause;
  }

(* turn a clause into a sorted list of atoms *)
let clause_to_list (c:clause) : sorted_atom_list =
  let cl = List.sort Atom.compare (Array.to_list c.c_atoms) in
  cl

let[@inline] merge_clauses
      (l1:sorted_atom_list) (l2:sorted_atom_list): sorted_atom_list =
  List.merge Atom.compare l1 l2

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

(* update proof of atom [a] with additional information at level 0 *)
let rec recompute_update_proof_of_atom (a:atom) : clause =
  assert (Atom.level a >= 0);
  begin match Atom.reason a with
    | Some (Bcp c) ->
      Log.debugf 10
        (fun k -> k "(@[proof.analyzing@ :atom %a@ :bcp %a@])"
            Atom.debug a Clause.debug c);
      if Array.length c.c_atoms = 1 then (
        Log.debugf 15 (fun k -> k "(@[proof.analyze.old_reason@ %a@])" Atom.debug a);
        c
      ) else (
        assert (Atom.is_false a);
        let premise =
          Array.fold_left
            (fun acc b ->
               if Atom.equal (Atom.neg a) b then acc
               else recompute_update_proof_of_atom b :: acc)
            []
            c.c_atoms
        in
        let premise = Premise.hyper_res (c :: premise) in
        let c' = Clause.make [Atom.neg a] premise in
        (* update reason *)
        begin match a.a_term.t_value with
          | TA_none -> assert false
          | TA_assign{value;_} ->
            a.a_term.t_value <- TA_assign{value;reason=Bcp c'}
        end;
        Log.debugf 15
          (fun k -> k "(@[proof.analyze.new_reason@ %a@ %a@])" Atom.debug a Clause.debug c');
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
        (fun acc a -> recompute_update_proof_of_atom a :: acc)
        [] conflict.c_atoms
    in
    let premise = Premise.hyper_res (conflict :: premise) in
    let res = Clause.make [] premise in
    Log.debugf 2 (fun k -> k "(@[@{<Green>proof.proof_found@}@ %a@ :premise %a@])"
        Clause.debug res Premise.pp premise);
    res
  )

let prove_atom a =
  if Atom.is_true a && Atom.level a = 0 then (
    Some (recompute_update_proof_of_atom a)
  ) else (
    None
  )

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
  | Resolution of {
      premise1: t;
      premise2: t;
      pivot: term;
    }

let[@inline] conclusion n = n.conclusion
let[@inline] step n = n.step

let debug_step out (s:step) : unit = match s with
  | Hypothesis -> Fmt.string out "hypothesis"
  | Assumption -> Fmt.string out "assumption"
  | Lemma l -> Fmt.fprintf out "(@[lemma %a@])" Lemma.pp l
  | Deduplicate (c,l) ->
    Fmt.fprintf out "(@[dedup@ :from %a@ :on (@[%a@])@])" Clause.debug c
      Clause.debug_atoms l
  | Resolution {premise1=p1; premise2=p2; pivot} ->
    Fmt.fprintf out "(@[res@ :pivot %a@ :c1 %a@ :c2 %a@])"
      Term.debug pivot Clause.debug p1 Clause.debug p2

type chain_res = {
  cr_pivot : term; (* pivot atom, on which resolution is done *)
  cr_clause: atom list; (* clause obtained by res *)
  cr_premise1 : clause;
  cr_premise2 : clause;
}

(* perform resolution between [c] and the remaining list.
   [cl] is the sorted list version of [c] *)
let rec chain_res (c:clause) (cl:sorted_atom_list) : clause list -> chain_res = function
  | d :: r ->
    Log.debugf 15 (fun k -> k "(@[proof.resolve@ :c1 %a@ :c2 %a@])"
        Clause.debug c Clause.debug d);
    let dl = clause_to_list d in
    let res = resolve (merge_clauses cl dl) in
    begin match res.resolve_pivots with
      | [a] ->
        begin match r with
          | [] ->
            {cr_clause=res.resolve_atoms; cr_pivot=Atom.term a;
             cr_premise1=c; cr_premise2=d}
          | _ ->
            let new_clause =
              Clause.make res.resolve_atoms
                (Premise.resolve (Atom.term a) c d)
            in
            chain_res new_clause res.resolve_atoms r
        end
      | pivots ->
        Util.errorf
          "(@[<hv>proof: resolution error (multiple pivots)@ :pivots (@[%a@])@ :c1 %a@ :c2 %a@])"
          (Util.pp_list Atom.debug) pivots Clause.debug c Clause.debug d
    end
  | _ ->
    Util.errorf "proof: resolution error (bad history)@ %a" Clause.pp c

let[@inline] mk_node conclusion step = {conclusion; step}

let expand (conclusion:clause) : node =
  Log.debugf 15 (fun k -> k "(@[proof.expanding@ %a@])" Clause.debug conclusion);
  begin match conclusion.c_premise with
    | Lemma l -> mk_node conclusion (Lemma l)
    | Hyp -> mk_node conclusion Hypothesis
    | Local -> mk_node conclusion Assumption
    | Resolve {c1;c2;pivot} ->
      let step = Resolution {
          premise1=c1;
          premise2=c2;
          pivot;
        }
      in
      mk_node conclusion step
    | Simplify c ->
      let duplicates = find_duplicates c in
      mk_node conclusion (Deduplicate (c, duplicates))
    | Hyper_res ([] | [_]) ->
      Util.errorf "proof: resolution error (wrong hyperres)@ %a@ :premise %a"
        Clause.debug conclusion Premise.pp conclusion.c_premise
    | Hyper_res ( c :: ([_] as r)) ->
      let res = chain_res c (clause_to_list c) r in
      let step = Resolution {
          premise1=res.cr_premise1;
          premise2=res.cr_premise2;
          pivot=res.cr_pivot;
        } in
      mk_node conclusion step
    | Hyper_res (c :: r) ->
      let res = chain_res c (clause_to_list c) r in
      conclusion.c_premise <-
        Premise.resolve res.cr_pivot res.cr_premise1 res.cr_premise2;
      let step = Resolution {
          premise1=res.cr_premise1;
          premise2=res.cr_premise2;
          pivot=res.cr_pivot;
        } in
      mk_node conclusion step
  end

(* Proof nodes manipulation *)
let is_leaf = function
  | Hypothesis
  | Assumption
  | Lemma _ -> true
  | Deduplicate _
  | Resolution _ -> false

let parents = function
  | Hypothesis
  | Assumption
  | Lemma _ -> []
  | Deduplicate (p, _) -> [p]
  | Resolution {premise1=p1; premise2=p2; _} -> [p1;p2]

let expl = function
  | Hypothesis -> "hypothesis"
  | Assumption -> "assumption"
  | Lemma _ -> "lemma"
  | Deduplicate  _ -> "deduplicate"
  | Resolution _ -> "resolution"

(* Compute unsat-core
   TODO: replace visited bool by a int unique to each call
   of unsat_core, so that the cleanup can be removed ? *)
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
        | Resolve {c1;c2;_} -> aux_l res (c::visited) [c1;c2] k
        | Hyper_res h -> aux_l res (c::visited) h k
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

let pop_opt s = try Some (Stack.pop s) with Stack.Empty -> None

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
          | Resolution {premise1=p1; premise2=p2;_} ->
            Stack.push (Enter p2) s;
            Stack.push (Enter p1) s
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

let c_to_set c = Sequence.of_list c |> Atom.Set.of_seq |> Atom.Set.to_list

let check p =
  (* compare lists of atoms, ignoring order and duplicates *)
  let check_same_l ~ctx c d =
    let l1 = c_to_set c in
    let l2 = c_to_set d in
    if not (CCList.equal Atom.equal l1 l2) then (
      Util.errorf
        "(@[proof.check.distinct_clauses@ :ctx %s@ :c1 %a@ :c2 %a@])"
        ctx Clause.debug_atoms c Clause.debug_atoms d
    );
  in
  let check_same_c ~ctx c1 c2 =
    check_same_l ~ctx (Array.to_list c1.c_atoms) (Array.to_list c2.c_atoms)
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
           if not (CCList.equal Atom.equal dups dups) then (
             Util.errorf
               "(@[<hv>proof.check.invalid_simplify_step@ :from %a@ :to %a@ :dups1 %a@ :dups2 %a@])"
               Clause.debug c Clause.debug concl Clause.debug_atoms dups
               Clause.debug_atoms dups'
           );
           check_same_c ~ctx:"in dedup" c concl
         | Resolution {premise1=p1; premise2=p2; pivot} ->
           let l =
             merge_clauses (clause_to_list p1) (clause_to_list p2)
             |> List.filter (fun a -> not (Atom.term a |> Term.equal pivot))
           in
           check_same_l ~ctx:"in res" l (clause_to_list concl)
       end)
    p


