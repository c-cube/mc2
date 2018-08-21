(**************************************************************************)
(*                                                                        *)
(*                          Alt-Ergo Zero                                 *)
(*                                                                        *)
(*                  Sylvain Conchon and_ Alain Mebsout                     *)
(*                      Universite Paris-Sud 11                           *)
(*                                                                        *)
(*  Copyright 2011. This file is distributed under the terms of the       *)
(*  Apache Software License version 2.0                                   *)
(*                                                                        *)
(**************************************************************************)

module type Arg = Tseitin_intf.Arg

module type S = Tseitin_intf.S

module Make (F : Tseitin_intf.Arg) = struct
  type combinator = And | Or | Imply | Not

  type atom = F.t
  type id = int

  (* main formula type *)
  type t = {
    id: id;
    view: view;
  }

  and view =
    | True
    | Lit of atom
    | Comb of combinator * t list

  let[@inline] view t = t.view

  let rec pp out f = match f.view with
    | True -> Format.fprintf out "true"
    | Lit a -> F.pp out a
    | Comb (Not, [f]) ->
      Format.fprintf out "(@[<hv1>not %a@])" pp f
    | Comb (And, l) -> Format.fprintf out "(@[<hv>and %a@])" (Util.pp_list pp) l
    | Comb (Or, l) ->  Format.fprintf out "(@[<hv>or %a@])" (Util.pp_list pp) l
    | Comb (Imply, [f1; f2]) ->
      Format.fprintf out "(@[<hv1>=>@ %a@ %a)" pp f1 pp f2
    | _ -> assert false

  let mk_ =
    let n = ref 0 in
    fun view -> incr n; {view; id= !n}

  let[@inline] make comb l = mk_ (Comb (comb, l))
  let[@inline] atom p = mk_ (Lit p)
  let true_ = mk_ True
  let false_ = mk_ @@ Comb(Not, [true_])

  let flatten comb l =
    List.fold_left
      (fun acc f -> match f.view with
         | Comb (c,l) when c = comb -> List.rev_append l acc
         | _ -> f :: acc)
      [] l

  (* unordered filter *)
  let rev_filter f l =
    let rec aux acc = function
      | [] -> acc
      | a :: tl ->
        aux (if f a then a::acc else acc) tl
    in aux [] l

  let[@inline] is_true = function {view=True;_} -> true | _ -> false
  let[@inline] is_false = function {view=Comb(Not, [{view=True;_}]);_} -> true | _ -> false

  let remove_true l = rev_filter (fun x -> not (is_true x)) l
  let remove_false l = rev_filter (fun x -> not (is_false x)) l

  let and_ l =
    let l' = remove_true @@ flatten And l in
    if List.exists is_false l' then (
      false_
    ) else (
      match l' with
        | [] -> true_
        | [a] -> a
        | _ -> make And l'
    )

  let or_ l =
    let l' = remove_false @@ flatten Or l in
    if List.exists is_true l' then (
      true_
    ) else (
      match l' with
        | [] -> false_
        | [a] -> a
        | _ -> make Or l'
    )

  let rec not_ f = match f.view with
    | Comb (Not, [g]) -> g
    | Comb (Not, _) -> assert false
    | Lit a -> atom (F.neg a)
    | Comb (And, l) -> or_ @@ List.rev_map not_ l
    | Comb (Or, l) -> and_ @@ List.rev_map not_ l
    | Comb (Imply, [a;b]) -> and_ [not_ a; b]
    | _ -> make Not [f]

  let imply f1 f2 = make Imply [f1; f2]
  let equiv f1 f2 = and_ [imply f1 f2; imply f2 f1]
  let xor f1 f2 = or_ [ and_ [ not_ f1; f2 ]; and_ [ f1; not_ f2 ] ]

  let rec imply_l a b = match a with
    | [] -> b
    | [x] -> imply x b
    | x :: a' -> imply x (imply_l a' b)

  let[@inline] equal a b = a.id = b.id
  let[@inline] hash a = CCHash.int a.id

  (* table of formulas *)
  module Tbl = CCHashtbl.Make(struct
      type nonrec t = t
      let equal = equal
      let hash = hash
    end)

  type cnf_res =
    | R_atom of atom
    | R_and of atom list
    | R_or of atom list
    | R_true
    | R_false

  type state = {
    fresh: unit -> atom;
    tbl_and: cnf_res Tbl.t; (* caching *)
    mutable acc_or : (atom * atom list) list;
    mutable acc_and : (atom * atom list) list;
    mutable proxies : atom list;
  }

  (* build a clause by flattening (if sub-formulas have the
     same combinator) and_ proxy-ing sub-formulas that have the
     opposite operator. *)
  let cnf_under_and (st:state) (f:t) : atom list option =
    let rec aux f : cnf_res = match f.view with
      | Lit a -> R_atom a
      | True -> R_true
      | Comb (Not, [{view=True;_}]) -> R_false
      | Comb (Not, [{view=Lit a;_}]) -> R_atom (F.neg a)
      | Comb ((And | Or | Imply), _) ->
        begin try Tbl.find st.tbl_and f
          with Not_found ->
            let res = aux_noncached f.view in
            Tbl.add st.tbl_and f res;
            res
        end
      | _ ->
        Log.debugf 1(fun k->k"(@[cnf.bad-formula@ %a@])" pp f);
        assert false
    and aux_noncached f : cnf_res =
      match f with
      | Comb (And, l) ->
        List.fold_left
          (fun acc f ->
             match acc, aux f with
             | R_false, _ | _, R_false -> R_false
             | R_and acc, R_true -> R_and acc
             | R_and acc, R_atom a -> R_and (a::acc)
             | R_and acc, R_and l -> R_and (List.rev_append l acc)
             | R_and acc, R_or l ->
               let proxy = st.fresh() in
               st.acc_or <- (proxy, l) :: st.acc_or;
               R_and (proxy :: acc)
             | _ -> assert false)
          (R_and []) l
      | Comb (Or, l) ->
        List.fold_left
          (fun acc f ->
             match acc, aux f with
             | R_true, _ | _, R_true -> R_true
             | R_or acc, R_false -> R_or acc
             | R_or acc, R_atom a -> R_or (a::acc)
             | R_or acc, R_or l -> R_or (List.rev_append l acc)
             | R_or acc, R_and l ->
               let proxy = st.fresh() in
               st.acc_and <- (proxy, l) :: st.acc_and;
               R_or (proxy :: acc)
             | _ -> assert false)
          (R_or []) l
      | Comb (Imply, [a;b]) ->
        aux_noncached @@ Comb (Or, [not_ a; b])
      | _ -> assert false
    in
    match aux f with
    | R_atom a -> Some [a]
    | R_or l -> Some l
    | R_false -> Some [] (* empty clause *)
    | R_true -> None (* trivial clause *)
    | _ -> assert false

  let cnf ?simplify:_ ~fresh (f:t) : atom list list =
    let st = {
      fresh;
      tbl_and = Tbl.create 16;
      acc_or=[];
      acc_and=[];
      proxies=[];
    } in
    let acc = match f.view with
      | True -> []
      | Comb (Not, [{view=True;_}]) -> [[]]
      | Comb (And, l) -> CCList.filter_map (cnf_under_and st) l
      | _ -> CCOpt.to_list @@ cnf_under_and st f
    in
    (* encode clauses that make proxies in !acc_and equivalent to
       their clause *)
    let acc =
      List.fold_left
        (fun acc (p,l) ->
           st.proxies <- p :: st.proxies;
           let np = F.neg p in
           (* build clause [cl = l1 & l2 & ... & ln => p] where [l = [l1;l2;..]]
              also add clauses [p => l1], [p => l2], etc. *)
           let cl, acc =
             List.fold_left
               (fun (cl,acc) a -> (F.neg a :: cl), [np; a] :: acc)
               ([p],acc) l in
           cl :: acc)
        acc st.acc_and
    in
    (* encore clauses that make proxies in !acc_or equivalent to
       their clause *)
    let acc =
      List.fold_left
        (fun acc (p,l) ->
           st.proxies <- p :: st.proxies;
           (* add clause [p => l1 | l2 | ... | ln], and_ add clauses
              [l1 => p], [l2 => p], etc. *)
           let acc =
             List.fold_left (fun acc a -> [p; F.neg a]::acc) acc l in
           (F.neg p :: l) :: acc)
        acc st.acc_or
    in
    acc
end
