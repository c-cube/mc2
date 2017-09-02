(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

open Solver_types

exception Insuficient_hyps
exception Resolution_error of string

(* Log levels *)
let error = 1
let warn = 3
let info = 10
let debug = 80

let merge = List.merge Atom.compare

let _c = ref 0
let fresh_pcl_name () = incr _c; "R" ^ (string_of_int !_c)

(* Compute resolution of 2 clauses *)
let resolve l =
  let rec aux resolved acc = function
    | [] -> resolved, acc
    | [a] -> resolved, a :: acc
    | a :: b :: r ->
      if Atom.equal a b then
        aux resolved (a :: acc) r
      else if Atom.equal (Atom.neg a) b then
        aux (Atom.abs a :: resolved) acc r
      else
        aux resolved (a :: acc) (b :: r)
  in
  let resolved, new_clause = aux [] [] l in
  resolved, List.rev new_clause

(* Compute the set of doublons of a clause *)
let find_doublons c = List.sort Atom.compare (Array.to_list (c.c_atoms))

(* TODO: comment *)
(* conflict analysis *)
let analyze (cl:atom list) : atom list list * atom list =
  let rec aux duplicates free = function
    | [] -> duplicates, free
    | [ x ] -> duplicates, x :: free
    | x :: ((y :: r) as l) ->
      if Atom.equal x y then
        count duplicates (x :: free) x [y] r
      else
        aux duplicates (x :: free) l
  and count duplicates free x acc = function
    | (y :: r) when Atom.equal x y ->
      count duplicates free x (y :: acc) r
    | l ->
      aux (acc :: duplicates) free l
  in
  let doublons, acc = aux [] [] cl in
  doublons, List.rev acc

let to_list c =
  let cl = find_doublons c in
  let doublons, l = analyze cl in
  let conflicts, _ = resolve l in
  if doublons <> [] then
    Log.debug warn "Input clause has redundancies";
  if conflicts <> [] then
    Log.debug warn "Input clause is a tautology";
  cl

(*
let pp_cl fmt l =
  let rec aux fmt = function
    | [] -> ()
    | a :: r ->
      Format.fprintf fmt "%a@,%a" pp_atom a aux r
  in
  Format.fprintf fmt "@[<v>%a@]" aux l
*)

(* Comparison of clauses *)
let cmp_cl c d =
  let rec aux = function
    | [], [] -> 0
    | a :: r, a' :: r' ->
      begin match Atom.compare a a' with
        | 0 -> aux (r, r')
        | x -> x
      end
    | _ :: _ , [] -> -1
    | [], _ :: _ -> 1
  in
  aux (c, d)

let prove conclusion =
  assert (conclusion.c_premise <> History []);
  conclusion

let rec set_atom_proof a =
  let aux acc b =
    if Atom.equal (Atom.neg a) b then acc
    else set_atom_proof b :: acc
  in
  assert (Atom.level a >= 0);
  begin match Atom.reason a with
    | Some Bcp c ->
      Log.debugf debug
        (fun k -> k "Analysing: @[%a@ %a@]" Atom.pp a Clause.pp c);
      if Array.length c.c_atoms = 1 then (
        Log.debugf debug (fun k -> k "Old reason: @[%a@]" Atom.pp a);
        c
      ) else (
        assert (Atom.is_false a);
        let r = History (c :: (Array.fold_left aux [] c.c_atoms)) in
        let c' = Clause.make [Atom.neg a] r in
        a.a_term.t_reason <- Some (Bcp c');
        Log.debugf debug
          (fun k -> k "New reason: @[%a@ %a@]" Atom.pp a Clause.pp c');
        c'
      )
    | _ ->
      Log.debugf error (fun k -> k "Error while proving atom %a" Atom.pp a);
      raise (Resolution_error "Cannot prove atom")
  end

let prove_unsat (conflict:clause) : clause =
  if Array.length conflict.c_atoms = 0 then conflict
  else (
    Log.debugf info (fun k -> k "Proving unsat from: @[%a@]" Clause.pp conflict);
    let l = Array.fold_left (fun acc a -> set_atom_proof a :: acc) [] conflict.c_atoms in
    let res = Clause.make [] (History (conflict :: l)) in
    Log.debugf info (fun k -> k "Proof found: @[%a@]" Clause.pp res);
    res
  )

let prove_atom a =
  if (Atom.is_true a && Atom.level a = 0) then
    Some (set_atom_proof a)
  else
    None

(* Interface exposed *)
type proof = clause
and proof_node = {
  conclusion : clause;
  step : step;
}
and step =
  | Hypothesis
  | Assumption
  | Lemma of lemma
  | Duplicate of proof * atom list
  | Resolution of proof * proof * atom

let rec chain_res (c, cl) = function
  | d :: r ->
    Log.debugf debug
      (fun k -> k "Resolving clauses : @[%a@\n%a@]"
          Clause.pp c Clause.pp d);
    let dl = to_list d in
    begin match resolve (merge cl dl) with
      | [a], l ->
        begin match r with
          | [] -> l, c, d, a
          | _ ->
            let new_clause = Clause.make l (History [c; d]) in
            chain_res (new_clause, l) r
        end
      | _ ->
        Log.debugf error
          (fun k -> k "While resolving clauses:@[<hov>%a@\n%a@]"
              Clause.pp c Clause.pp d);
        raise (Resolution_error "Clause mismatch")
    end
  | _ ->
    raise (Resolution_error "Bad history")

let expand conclusion : proof_node =
  Log.debugf debug (fun k -> k "Expanding : @[%a@]" Clause.pp conclusion);
  begin match conclusion.c_premise with
    | Lemma l ->
      {conclusion; step = Lemma l; }
    | Hyp ->
      { conclusion; step = Hypothesis; }
    | Local ->
      { conclusion; step = Assumption; }
    | History [] ->
      Log.debugf error
        (fun k -> k "Empty history for clause: %a" Clause.pp conclusion);
      raise (Resolution_error "Empty history")
    | History [ c ] ->
      let duplicates, res = analyze (find_doublons c) in
      assert (cmp_cl res (find_doublons conclusion) = 0);
      { conclusion; step = Duplicate (c, List.concat duplicates) }
    | History ( c :: ([_] as r)) ->
      let (l, c', d', a) = chain_res (c, to_list c) r in
      assert (cmp_cl l (to_list conclusion) = 0);
      { conclusion; step = Resolution (c', d', a); }
    | History ( c :: r ) ->
      let (l, c', d', a) = chain_res (c, to_list c) r in
      conclusion.c_premise <- History [c'; d'];
      assert (cmp_cl l (to_list conclusion) = 0);
      { conclusion; step = Resolution (c', d', a); }
  end

(* Proof nodes manipulation *)
let is_leaf = function
  | Hypothesis
  | Assumption
  | Lemma _ -> true
  | Duplicate _
  | Resolution _ -> false

let parents = function
  | Hypothesis
  | Assumption
  | Lemma _ -> []
  | Duplicate (p, _) -> [p]
  | Resolution (p, p', _) -> [p; p']

let expl = function
  | Hypothesis -> "hypothesis"
  | Assumption -> "assumption"
  | Lemma _ -> "lemma"
  | Duplicate _ -> "duplicate"
  | Resolution _ -> "resolution"

(* Compute unsat-core
   TODO: replace visited bool by a int unique to each call
   of unsat_core, so that the cleanup can be removed ? *)
let unsat_core proof =
  let rec aux res acc = function
    | [] -> res, acc
    | c :: r ->
      if not (Clause.visited c) then (
        Clause.mark_visited c;
        match c.c_premise with
          | Hyp | Local | Lemma _ -> aux (c :: res) acc r
          | History h ->
            let l =
              List.fold_left
                (fun acc c ->
                   if not (Clause.visited c) then c :: acc else acc)
                r h
            in
            aux res (c :: acc) l
      ) else (
        aux res acc r
      )
  in
  let res, tmp = aux [] [] [proof] in
  List.iter Clause.clear_visited res;
  List.iter Clause.clear_visited tmp;
  res

(* Iterate on proofs *)
module H = CCHashtbl.Make(struct
    type t = clause
    let hash cl =
      Array.fold_left (fun i a -> Hashtbl.hash (a.a_id, i)) 0 cl.c_atoms
    let equal = (==)
  end)

type task =
  | Enter of proof
  | Leaving of proof

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
          | Duplicate (p1, _) ->
            Stack.push (Enter p1) s
          | Resolution (p1, p2, _) ->
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

let check p = fold (fun () _ -> ()) () p


