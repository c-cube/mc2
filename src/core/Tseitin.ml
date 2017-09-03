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

  (* main formula type *)
  type t =
    | True
    | Lit of atom
    | Comb of combinator * t list

  let rec pp fmt phi = match phi with
    | True -> Format.fprintf fmt "true"
    | Lit a -> F.pp fmt a
    | Comb (Not, [f]) ->
      Format.fprintf fmt "(@[<hv1>not %a@])" pp f
    | Comb (And, l) -> Format.fprintf fmt "(@[<hv>and %a@])" (Util.pp_list pp) l
    | Comb (Or, l) ->  Format.fprintf fmt "(@[<hv>or %a@])" (Util.pp_list pp) l
    | Comb (Imply, [f1; f2]) ->
      Format.fprintf fmt "(@[<hv1>=>@ %a@ %a)" pp f1 pp f2
    | _ -> assert false

  let[@inline] make comb l = Comb (comb, l)
  let[@inline] atom p = Lit p
  let true_ = True
  let false_ = Comb(Not, [True])

  let rec flatten comb acc = function
    | [] -> acc
    | (Comb (c, l)) :: r when c = comb ->
      flatten comb (List.rev_append l acc) r
    | a :: r ->
      flatten comb (a :: acc) r

  (* unordered filter map *)
  let rec rev_filter_map f acc = function
    | [] -> acc
    | a :: r ->
      begin match f a with
        | None -> rev_filter_map f acc r
        | Some b -> rev_filter_map f (b :: acc) r
      end

  let remove_true l =
    let aux = function
      | True -> None
      | f -> Some f
    in
    rev_filter_map aux [] l

  let remove_false l =
    let aux = function
      | Comb(Not, [True]) -> None
      | f -> Some f
    in
    rev_filter_map aux [] l

  let[@inline] not_ f = make Not [f]

  let is_true = function True -> true | _ -> false
  let is_false = function (Comb(Not, [True])) -> true | _ -> false

  let and_ l =
    let l' = remove_true (flatten And [] l) in
    if List.exists is_false l' then (
      false_
    ) else match l' with
      | [] -> true_
      | [a] -> a
      | _ -> make And l'

  let or_ l =
    let l' = remove_false (flatten Or [] l) in
    if List.exists is_true l' then (
      true_
    ) else match l' with
      | [] -> false_
      | [a] -> a
      | _ -> Comb (Or, l')

  let imply f1 f2 = make Imply [f1; f2]
  let equiv f1 f2 = and_ [imply f1 f2; imply f2 f1]
  let xor f1 f2 = or_ [ and_ [ not_ f1; f2 ]; and_ [ f1; not_ f2 ] ]

  (* simplify formula *)
  let[@inline] (%%) f g x = f (g x)

  (* simplify *)
  let rec sform f k = match f with
    | True | Comb (Not, [True]) -> k f
    | Comb (Not, [Lit a]) -> k (Lit (F.neg a))
    | Comb (Not, [Comb (Not, [f])]) -> sform f k
    | Comb (Not, [Comb (Or, l)]) -> sform_list_not [] l (k %% and_)
    | Comb (Not, [Comb (And, l)]) -> sform_list_not [] l (k %% or_)
    | Comb (And, l) -> sform_list [] l (k %% and_)
    | Comb (Or, l) -> sform_list [] l (k %% or_)
    | Comb (Imply, [f1; f2]) ->
      sform (not_ f1) (fun f1' -> sform f2 (fun f2' -> k (or_ [f1'; f2'])))
    | Comb (Not, [Comb (Imply, [f1; f2])]) ->
      sform f1 (fun f1' -> sform (not_ f2) (fun f2' -> k (and_ [f1';f2'])))
    | Comb ((Imply | Not), _) -> assert false
    | Lit _ -> k f
  and sform_list acc l k = match l with
    | [] -> k acc
    | f :: tail ->
      sform f (fun f' -> sform_list (f'::acc) tail k)
  and sform_list_not acc l k = match l with
    | [] -> k acc
    | f :: tail ->
      sform (not_ f) (fun f' -> sform_list_not (f'::acc) tail k)

  let[@inline] ( @@ ) l1 l2 = List.rev_append l1 l2

  type state = {
    fresh: unit -> atom;
    mutable acc_or : (atom * atom list) list;
    mutable acc_and : (atom * atom list) list;
    mutable proxies : atom list;
  }

  (* build a clause by flattening (if sub-formulas have the
     same combinator) and_ proxy-ing sub-formulas that have the
     opposite operator. *)
  let cnf_under_and (st:state) (f:t) : combinator option * atom list =
    let rec aux f = match f with
      | Lit a -> None, [a]
      | Comb (Not, [Lit a]) -> None, [F.neg a]
      | Comb (And, l) ->
        List.fold_left
          (fun (_, acc) f ->
             match aux f with
               | _, [] -> assert false
               | _, [a] -> Some And, a :: acc
               | Some And, l ->
                 Some And, l @@ acc
               (* let proxy = mk_proxy () in *)
               (* acc_and := (proxy, l) :: !acc_and; *)
               (* proxy :: acc *)
               | Some Or, l ->
                 let proxy = st.fresh() in
                 st.acc_or <- (proxy, l) :: st.acc_or;
                 Some And, proxy :: acc
               | None, l -> Some And, l @@ acc
               | _ -> assert false)
          (None, []) l
      | Comb (Or, l) ->
        List.fold_left
          (fun (_, acc) f ->
             match aux f with
               | _, [] -> assert false
               | _, [a] -> Some Or, a :: acc
               | Some Or, l ->
                 Some Or, l @@ acc
               (* let proxy = mk_proxy () in *)
               (* acc_or := (proxy, l) :: !acc_or; *)
               (* proxy :: acc *)
               | Some And, l ->
                 let proxy = st.fresh() in
                 st.acc_and <- (proxy, l) :: st.acc_and;
                 Some Or, proxy :: acc
               | None, l -> Some Or, l @@ acc
               | _ -> assert false)
          (None, []) l
      | _ -> assert false
    in
    aux f

  let cnf ?(simplify=true) ~fresh (f:t) : atom list list =
    let st = {
      fresh;
      acc_or=[];
      acc_and=[];
      proxies=[];
    } in
    let f = if simplify then sform f CCFun.id else f in
    let acc = match f with
      | True -> []
      | Comb(Not, [True]) -> [[]]
      | Comb (And, l) -> List.rev_map (fun f -> snd(cnf_under_and st f)) l
      | _ -> [snd (cnf_under_and st f)]
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
           let acc = List.fold_left (fun acc a -> [p; F.neg a]::acc)
               acc l in
           (F.neg p :: l) :: acc)
        acc st.acc_or
    in
    acc
end
