
(** {1 Uninterpreted Functions and Types} *)

open Mc2_core
open Solver_types

module Fmt = CCFormat

let name = "unin_sort"
let k_decl_sort = Service.Key.make "unin_sort.decl"
let k_make = Service.Key.make "unin_sort.make"
let k_eq = Service.Key.make "unin_sort.eq"

(* reason why [t != v] or [t = v] for some value v *)
type reason = {
  other: term;
  atom: atom; (* t≠other or t=other *)
  lvl: level;
}

(* list of unit constraints for a term. Each constraint maps
   a value to a list of reasons why the term cannot be this value *)
type constraint_list =
  | C_none
  | C_diseq of {
      tbl: reason list Value.Tbl.t;
    } (** Term is none of these values *)
  | C_eq of {
      value: value;
      mutable l: reason list;
      diseq_tbl: reason list Value.Tbl.t lazy_t;
    } (** Term equal value *)

(* current knowledge for a value of an uninterpreted type *)
type decide_state +=
  | DS of {
      mutable c_list : constraint_list;
      (* list of constraints on the term.
         invariant: all the [C_singleton] cases come first *)
    }

(* uninterpreted types *)
type ty_view +=
  | Unin of {
      id: ID.t;
      args: Type.t list;
    }

(* equality between uninterpreted types *)
type term_view +=
  | Eq of term * term

(* extend values with unintepreted sorts *)
type value_view +=
  | V_unin of int

type lemma_view +=
  | Transitivity
  | Equality

let tc_lemma =
  let tcl_pp out = function
    | Transitivity -> Fmt.string out "transitivity_eq"
    | Equality -> Fmt.string out "eq"
    | _ -> assert false
  in
  { tcl_pp }

let c_list_as_seq (tbl:reason list Value.Tbl.t) : (value * reason) Sequence.t =
  Value.Tbl.to_seq tbl
  |> Sequence.flat_map
    (fun (v,l) ->
       Sequence.of_list l
       |> Sequence.map (fun t -> v,t))

let pp_v_reason_eq out (v,rn): unit =
  Fmt.fprintf out "(@[eq:v %a@ :lvl %d@ :other %a@ :eqn %a@])"
    Value.pp v rn.lvl Term.debug rn.other Atom.debug rn.atom

let pp_v_reason_neq out (v,rn): unit =
  Fmt.fprintf out "(@[diff :v %a@ :lvl %d@ :other %a@ :diseqn %a@])"
    Value.pp v rn.lvl Term.debug rn.other Atom.debug rn.atom

let pp_c_list out (c_l:constraint_list) = match c_l with
  | C_none -> Fmt.string out "ø"
  | C_eq {value;l;_} ->
    let l = Sequence.of_list l |> Sequence.map (CCPair.make value) in
    Fmt.fprintf out "{@[<hv>%a@]}" (Util.pp_seq pp_v_reason_eq) l
  | C_diseq {tbl} ->
    Fmt.fprintf out "{@[<hv>%a@]}"
      (Util.pp_seq pp_v_reason_neq) (c_list_as_seq tbl)

(* values for uninterpreted sorts *)
module V = struct
  let[@inline] get_v = function V_unin i -> i | _ -> assert false
  let[@inline] get (v:value): int = get_v (Value.view v)
  let[@inline] tcv_pp out v = Fmt.fprintf out "$v_%d" (get_v v)
  let[@inline] tcv_hash v = CCHash.int (get_v v)
  let[@inline] tcv_equal v1 v2 = match v1, v2 with
    | V_unin i, V_unin j -> i=j
    | _ -> false

  let tc_value = { tcv_pp; tcv_equal; tcv_hash; }

  let[@inline] mk (i:int) : value = Value.make tc_value (V_unin i)
end

let build ~propagate p_id (Plugin.S_cons (_, true_, Plugin.S_nil)) : Plugin.t =
  (* equality literals *)
  let module Term_alloc = Term.Term_allocator(struct
      let initial_size = 64
      let p_id = p_id
      let equal a b = match a, b with
        | Eq (a1,b1), Eq (a2,b2) -> Term.equal a1 a2 && Term.equal b1 b2
        | _ -> false
      let hash = function
        | Eq (a,b) -> CCHash.combine3 10 (Term.hash a) (Term.hash b)
        | _ -> assert false
    end)
  in
  (* uninterpreted types *)
  let module Ty_alloc = Type.Alloc(struct
      let initial_size = 16
      let hash = function
        | Unin {id;args;_} ->
          CCHash.combine3 10 (ID.hash id) (CCHash.list Type.hash args)
        | _ -> assert false
      let equal a b = match a, b with
        | Unin {id=f1;args=l1;_}, Unin {id=f2;args=l2;_} ->
          ID.equal f1 f2 && CCList.equal Type.equal l1 l2
        | _ -> false
    end)
  in
  let module P : Plugin.S = struct
    let id = p_id
    let name = name

    let check_if_sat _ = Sat
    let gc_all = Term_alloc.gc_all
    let iter_terms = Term_alloc.iter_terms

    (* uninterpreted sorts, with arity *)
    let tbl_ : int ID.Tbl.t = ID.Tbl.create 16

    (* declare a new (parametric) uninterpreted type *)
    let decl_sort id (arity:int) : unit =
      Log.debugf 3
        (fun k->k "(@[unin_sort.@{<yellow>declare-sort@} %a@ :arity %d@])" ID.pp id arity);
      if ID.Tbl.mem tbl_ id then (
        Util.errorf "sort %a already declared" ID.pp id;
      );
      ID.Tbl.add tbl_ id arity

    let[@inline] is_unin_sort (ty:Type.t) : bool = match ty with
      | Ty {view=Unin _; _} -> true
      | _ -> false

    let pp out = function
      | Eq(a,b) -> Fmt.fprintf out "(@[<hv>=@ %a@ %a@])" Term.pp a Term.pp b
      | _ -> assert false

    let subterms v yield = match v with
      | Eq(a,b) -> yield a; yield b
      | _ -> assert false

    (* evaluate equality *)
    let eval (t:term) : eval_res = match Term.view t with
      | Eq (a, b) when Term.equal a b -> Eval_into (Value.true_, [])
      | Eq (a, b) ->
        begin match Term.value a, Term.value b with
          | Some va, Some vb ->
            Eval_into (Value.equal va vb |> Value.of_bool, [a,va;b,vb])
          | _ -> Eval_unknown
        end
      | _ -> assert false

    type conflict_opt =
      | Conflict_none
      | Conflict_eq_eq of {other:term; eqn:atom} (* atom is equal to both values *)
      | Conflict_eq_neq of {other:term; diseqn:atom} (* atom is equal and disequal to value. arg=Diseq *)
      | Conflict_neq_eq of {other:term; eqn:atom} (* atom is equal and disequal to value. arg=Eq *)

    (* find a conflicting constraints in [l] for [t=v] *)
    let find_conflict_eq_ (v:value) (l:constraint_list) : conflict_opt =
      begin match l with
        | C_none -> Conflict_none
        | C_diseq {tbl} ->
          begin match Value.Tbl.find tbl v with
            | [] -> assert false
            | {atom;other;_} :: _ ->
              assert (Atom.is_neg atom);
              Conflict_eq_neq {diseqn=atom;other}
            | exception Not_found -> Conflict_none
          end
        | C_eq {l=[];_} -> assert false
        | C_eq {value=v2;l={other;atom;_}::_;_} ->
          if Value.equal v v2 then (
            Conflict_none
          ) else (
            assert (Atom.is_pos atom);
            Conflict_eq_eq {eqn=atom;other}
          )
      end

    (* find a conflicting constraints in [l] for [t≠v] *)
    let find_conflict_diseq_ (v:value) (l:constraint_list) : conflict_opt =
      begin match l with
        | C_eq {l=[];_} -> assert false
        | C_eq {value;l={atom;other;_}::_;_} ->
          if Value.equal v value
          then Conflict_neq_eq {eqn=atom;other}
          else Conflict_none
        | C_none | C_diseq _ -> Conflict_none (* no conflict between diseq *)
      end

    (* propagate [t := v because eqn] *)
    let add_singleton acts t v ~eqn ~other : unit =
      begin match Term.var t with
        | Var_semantic {v_decide_state=DS ds; _} ->
          Log.debugf 15
            (fun k->k
                "(@[<hv>%s.add_singleton@ :to %a@ :val %a@ :other %a@ :eqn %a@ :c_list %a@])"
                name Term.debug t Value.pp v Term.debug other Atom.debug eqn pp_c_list ds.c_list);
          (* first, check if SAT *)
          begin match find_conflict_eq_ v ds.c_list with
            | Conflict_neq_eq _ -> assert false
            | Conflict_eq_eq {eqn=eqn';other=other'} ->
              (* conflict! two distinct "singleton" *)
              let eq_deduce = Term.Bool.mk_eq other other' in
              let conflict =
                [ eq_deduce;
                  Atom.neg eqn;
                  Atom.neg eqn';
                ]
              and lemma = Lemma.make Transitivity tc_lemma in
              Actions.raise_conflict acts conflict lemma
            | Conflict_eq_neq {other=other';diseqn} ->
              (* conflict! one singleton, one diff, same value *)
              let neq_side = Term.Bool.mk_neq other other' in
              let conflict =
                [ Atom.neg diseqn;
                  Atom.neg eqn;
                  neq_side;
                ]
              and lemma = Lemma.make Transitivity tc_lemma in
              Actions.raise_conflict acts conflict lemma
            | Conflict_none -> ()
          end;
          (* just add constraint *)
          let lvl = max (Atom.level eqn) (Term.level other) in
          Actions.on_backtrack acts lvl (fun () -> Actions.mark_dirty acts t);
          let r = {other;atom=eqn;lvl} in
          begin match ds.c_list with
            | C_none ->
              ds.c_list <- C_eq {value=v;l=[r];diseq_tbl=lazy (Value.Tbl.create 5)};
            | C_eq eq -> eq.l <- r :: eq.l
            | C_diseq {tbl} ->
              ds.c_list <- C_eq {value=v;l=[r];diseq_tbl=Lazy.from_val tbl};
          end;
          Log.debugf 30
            (fun k->k
                "(@[<hv>%s.add_singleton.done@ :to %a@ :c_list %a@])"
                name Term.debug t pp_c_list ds.c_list);
          (* also, propagate, if not assigned yet ! *)
          if propagate && not (Term.has_some_value t) then (
            let lemma = Lemma.make Equality tc_lemma in
            Actions.propagate_val_lemma acts t v ~rw_into:other [eqn] lemma;
          )
        | _ -> assert false
      end

    (* add constraint [t != v because diseqn] *)
    let add_diff acts t v ~diseqn ~other : unit =
      begin match Term.var t with
        | Var_semantic {v_decide_state=DS ds; _} ->
          Log.debugf 15
            (fun k->k "(@[<hv>%s.add_diff@ :to %a@ :val %a@ :other %a@ :diseqn %a@ :c_list %a@])"
                name Term.debug t Value.pp v Term.debug other Atom.debug diseqn pp_c_list ds.c_list);
          (* first, check if SAT *)
          begin match find_conflict_diseq_ v ds.c_list with
            | Conflict_eq_eq _
            | Conflict_eq_neq _ -> assert false
            | Conflict_neq_eq {eqn;other=other'} ->
              (* conflict! one singleton, one diff, same value *)
              let eq_side = Term.Bool.mk_neq other other' in
              let conflict =
                [ diseqn;
                  Atom.neg eqn;
                  eq_side;
                ]
              and lemma = Lemma.make Transitivity tc_lemma in
              Actions.raise_conflict acts conflict lemma
            | Conflict_none -> ()
          end;
          (* just add constraint *)
          let lvl = max (Atom.level diseqn) (Term.level other) in
          Actions.on_backtrack acts lvl (fun () -> Actions.mark_dirty acts t);
          (* add constraint *)
          let tbl = match ds.c_list with
            | C_eq _ -> assert false
            | C_diseq {tbl} -> tbl
            | C_none ->
              let tbl = Value.Tbl.create 6 in
              ds.c_list <- C_diseq {tbl};
              tbl
          in
          let l = Value.Tbl.get_or ~default:[] tbl v in
          Value.Tbl.replace tbl v ({other;atom=diseqn;lvl} :: l);
        | _ -> assert false
      end

    (* check if term now evaluates, or if it becomes a unit constraint *)
    let update_watches acts (eqn:term) ~watch:_ = match Term.view eqn with
      | Eq (a,b) ->
        begin match Term.value eqn, Term.value a, Term.value b with
          | Some V_true, Some value, None ->
            add_singleton acts b value ~eqn:(Term.Bool.pa eqn) ~other:a
          | Some V_true, None, Some value ->
            add_singleton acts a value ~eqn:(Term.Bool.pa eqn) ~other:b
          | Some V_false, Some value, None ->
            add_diff acts b value ~diseqn:(Term.Bool.na eqn) ~other:a
          | Some V_false, None, Some value ->
            add_diff acts a value ~diseqn:(Term.Bool.na eqn) ~other:b
          | _, Some _, Some _ ->
            (* semantic propagation *)
            begin match eval eqn with
              | Eval_unknown -> assert false
              | Eval_into (v, subs) ->
                let b = Value.as_bool_exn v in
                Actions.propagate_bool_eval acts eqn b ~subs
            end
          | _ -> ()
        end;
        Watch_keep
      | _ -> assert false

    (* [a=b] watches [a,b, a=b] *)
    let init _ (t:term) = match Term.view t with
      | Eq (a,b) ->
        Term.add_watch a t;
        Term.add_watch b t;
        Term.add_watch t t;
      | _ -> assert false

    let tc_term : tc_term =
      Term.tc_mk ~pp ~subterms ~update_watches ~init ~eval ()

    (* make an equality literal *)
    let mk_eq (t:term) (u:term): term =
      if not (is_unin_sort (Term.ty t)) then (
        Util.errorf
          "unin_sort.eq:@ expected term of an uninterpreted sort,@ got %a"
          Term.debug t
      );
      if not (Type.equal (Term.ty t) (Term.ty u)) then (
        Util.errorf
          "unin_sort.eq:@ terms should have same type,@ got %a@ and %a"
          Term.debug t Term.debug u
      );
      if Term.equal t u then true_ (* auto-simplify *)
      else (
        let view = if Term.id t < Term.id u then Eq (t,u) else Eq (u,t) in
        Term_alloc.make view Type.bool tc_term
      )

    let map t f = match Term.view t with
      | Eq (a,b) ->
        let a' = f a in
        let b' = f b in
        if a==a' && b==b' then t else mk_eq a' b'
      | _ -> assert false

    let () =
      tc_term.tct_map <- map

    (* find a value that is authorized by the list of constraints *)
    let[@inline] find_value (l:constraint_list): value = match l with
      | C_none -> V.mk 0
      | C_eq {value;_} -> value
      | C_diseq {tbl} ->
        (* is [i] forbidden by [l]? *)
        let[@inline] forbidden v = Value.Tbl.mem tbl v in
        let v =
          Sequence.(0 -- max_int)
          |> Sequence.map (fun i -> V.mk i)
          |> Sequence.filter (fun v -> not (forbidden v))
          |> Sequence.head_exn
        in
        v

    (* how to make a decision for terms of uninterpreted type *)
    let decide (acts:actions) (t:term) : value =
      begin match Term.var t with
        | Var_semantic {v_decide_state=DS{c_list}; _} ->
          let v = find_value c_list in
          Log.debugf 5
            (fun k->k "(@[<hv>%s.@{<yellow>decide@}@ :term %a@ :val %a@ :lvl %d@ :c_list %a@])"
                name Term.debug t Value.pp v (Actions.level acts) pp_c_list c_list);
          v
        | _ -> assert false
      end

    let pp_ty out = function
      | Unin {id;args=[];_} -> ID.pp out id
      | Unin {id;args;_} ->
        Format.fprintf out "(@[%a@ %a@])" ID.pp id (Util.pp_list Type.pp) args
      | _ -> assert false

    (* new state: empty list of constraints *)
    let[@inline] mk_state () = DS {c_list=C_none}

    let[@inline] filter_r_list level : reason list -> reason list =
      CCList.filter (fun {lvl;_} -> lvl <= level)

    (* filter constraints of level bigger than [lvl] *)
    let rec filter_lvl_ lvl (l:constraint_list) : constraint_list =
      begin match l with
        | C_none -> C_none
        | C_eq {value;l;diseq_tbl} ->
          let l = filter_r_list lvl l in
          if CCList.is_empty l then (
            (* no equality anymore, fallback to diseq *)
            if Lazy.is_val diseq_tbl then
              filter_lvl_ lvl (C_diseq {tbl=Lazy.force diseq_tbl})
            else C_none
          ) else C_eq {value;l;diseq_tbl}
        | C_diseq {tbl} ->
          Value.Tbl.iter
            (fun v l ->
               let l = filter_r_list lvl l in
               if CCList.is_empty l then Value.Tbl.remove tbl v
               else Value.Tbl.replace tbl v l)
            tbl;
          if Value.Tbl.length tbl = 0 then C_none else C_diseq{tbl}
      end

    (* refresh the state of terms whose type is uninterpreted *)
    let refresh_state (lvl:level) (t:term) : unit =
      begin match t.t_var with
        | Var_semantic {v_decide_state=DS ds; _} ->
          ds.c_list <- filter_lvl_ lvl ds.c_list;
          Log.debugf 15 (fun k->k"(@[%s.refresh_state :lvl %d@ %a@ :clist %a@])"
              name lvl Term.debug t pp_c_list ds.c_list);
        | _ -> assert false
      end

    let tc_ty : tc_ty =
      Type.tc_mk ~refresh_state ~pp:pp_ty ~decide ~mk_state ~eq:mk_eq ()

    (* make a concrete instance of the type *)
    let make_sort (id:ID.t) (args:Type.t list) : Type.t =
      begin match ID.Tbl.get tbl_ id with
        | Some ar when ar=List.length args ->
          Ty_alloc.make (Unin {id;args}) tc_ty
        | Some ar ->
          Util.errorf "wrong arity for sort %a:@ need %d args,@ got (@[%a@])"
            ID.pp id ar (Util.pp_list Type.pp) args
        | None ->
          Util.errorf "no uninterpreted sort for %a" ID.pp id
      end

    let provided_services =
      [ Service.Any (k_decl_sort, decl_sort);
        Service.Any (k_make, make_sort);
        Service.Any (k_eq, mk_eq)
      ]
  end
  in
  (module P : Plugin.S)

let plugin ~propagate =
  Plugin.Factory.make
    ~priority:5
    ~name
    ~requires:Plugin.(K_cons (Builtins.k_true, K_nil))
    ~build:(build ~propagate)
    ()

