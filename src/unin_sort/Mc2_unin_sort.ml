
(** {1 Uninterpreted Functions and Types} *)

open Mc2_core
open Solver_types

module Fmt = CCFormat

let name = "unin_sort"
let k_decl_sort = Service.Key.make "unin_sort.decl"
let k_make = Service.Key.make "unin_sort.make"
let k_eq = Service.Key.make "unin_sort.eq"

module Int_map = CCMap.Make(CCInt)

(* list of unit constraints for a term *)
type constraint_list =
  | C_nil
  | C_singleton of {
      v:value;
      other: term;
      eqn: term; (* t=other *)
      lvl: level;
      tail: constraint_list;
    } (** = this value *)
  | C_diff of {
      v:value;
      other: term;
      diseqn: term; (* t≠other *)
      lvl: level;
      tail: constraint_list;
    } (** ≠ this value *)

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

(* TODO: remove these complicated lemmas? *)

type lemma_view += Transitivity

let tc_lemma =
  let tcl_pp out = function
    | Transitivity -> Fmt.string out "transitivity_eq"
    | _ -> assert false
  in
  { tcl_pp }

let pp_c_list out =
  let first=ref true in
  let rec aux out = function
    | C_nil -> ()
    | C_singleton {v;eqn;other;tail;lvl} ->
      if !first then first:=false else Fmt.fprintf out "@ ";
      Fmt.fprintf out "(@[singleton :v %a@ :lvl %d@ :other %a@ :eqn %a@])%a"
        Value.pp v lvl Term.debug other Term.debug eqn aux tail
    | C_diff {v;diseqn;lvl;other;tail} ->
      if !first then first:=false else Fmt.fprintf out "@ ";
      Fmt.fprintf out "(@[diff :v %a@ :lvl %d@ :other %a@ :diseqn %a@])%a"
        Value.pp v lvl Term.debug other Term.debug diseqn aux tail
  in
  Fmt.fprintf out "{@[<hv>%a@]}" aux

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

let build p_id (Plugin.S_cons (_, true_, Plugin.S_nil)) : Plugin.t =
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
        (fun k->k "(@[unin_sort.declare-sort %a@ :arity %d@])" ID.pp id arity);
      if ID.Tbl.mem tbl_ id then (
        Util.errorf "sort %a already declared" ID.pp id;
      );
      ID.Tbl.add tbl_ id arity

    let[@inline] is_unin_sort (ty:Type.t) : bool = match ty with
      | Ty {view=Unin _; _} -> true
      | _ -> false

    let pp out = function
      | Eq(a,b) -> Fmt.fprintf out "(@[<hv>= %a %a@])" Term.pp a Term.pp b
      | _ -> assert false

    let subterms v yield = match v with
      | Eq(a,b) -> yield a; yield b
      | _ -> assert false

    (* evaluate equality *)
    let eval_bool (t:term) : eval_bool_res = match Term.view t with
      | Eq (a, b) when Term.equal a b -> Eval_bool (true, [])
      | Eq (a, b) ->
        begin match Term.value a, Term.value b with
          | TA_assign {value=va;_}, TA_assign {value=vb;_} ->
            Eval_bool (Value.equal va vb, [a;b])
          | _ -> Eval_unknown
        end
      | _ -> assert false

    type conflict_opt =
      | Conflict_none
      | Conflict_eq_eq of {other:term; eqn:term} (* term is equal to both values *)
      | Conflict_eq_neq of {other:term; diseqn:term} (* term is equal and disequal to value. arg=Diseq *)
      | Conflict_neq_eq of {other:term; eqn:term} (* term is equal and disequal to value. arg=Eq *)

    (* find a conflicting constraints in [l] for [t=v] *)
    let rec find_conflict_eq_ (v:value) (l:constraint_list) : conflict_opt =
      begin match l with
        | C_nil -> Conflict_none
        | C_singleton {v=v';eqn;other;tail;_} ->
          if Value.equal v v' then find_conflict_eq_ v tail
          else Conflict_eq_eq {other; eqn}
        | C_diff {v=v';diseqn;other;tail;_} ->
          if Value.equal v v' then Conflict_eq_neq {diseqn;other}
          else find_conflict_eq_ v tail
      end

    (* find a conflicting constraints in [l] for [t≠v] *)
    let rec find_conflict_diseq_ (v:value) (l:constraint_list) : conflict_opt =
      begin match l with
        | C_singleton {v=v';eqn;other;tail;_} ->
          if Value.equal v v'
          then Conflict_neq_eq {eqn;other}
          else find_conflict_diseq_ v tail
        | C_diff _ | C_nil -> Conflict_none (* no conflict between diseq *)
      end

    (* add constraint [t := v because eqn] *)
    let add_singleton acts t v ~eqn ~other : unit =
      begin match Term.var t with
        | Var_semantic {v_decide_state=DS ds; _} ->
          Log.debugf 5
            (fun k->k
                "(@[<hv>%s.add_singleton@ :to %a@ :val %a@ :other %a@ :eqn %a@ :c_list %a@])"
                name Term.debug t Value.pp v Term.debug other Term.debug eqn pp_c_list ds.c_list);
          (* first, check if SAT *)
          begin match find_conflict_eq_ v ds.c_list with
            | Conflict_neq_eq _ -> assert false
            | Conflict_eq_eq {eqn=eqn';other=other'} ->
              (* conflict! two distinct "singleton" *)
              let neq = Term.mk_eq other other' in
              let conflict =
                [ Term.Bool.pa neq;
                  Term.Bool.na eqn;
                  Term.Bool.na eqn'
                ]
              and lemma = Lemma.make Transitivity tc_lemma in
              Actions.raise_conflict acts conflict lemma
            | Conflict_eq_neq {other=other';diseqn} ->
              (* conflict! one singleton, one diff, same value *)
              let eq_side = Term.mk_eq other other' in
              let conflict =
                [ Term.Bool.pa diseqn;
                  Term.Bool.na eqn;
                  Term.Bool.na eq_side;
                ]
              and lemma = Lemma.make Transitivity tc_lemma in
              Actions.raise_conflict acts conflict lemma
            | Conflict_none -> ()
          end;
          (* just add constraint *)
          Actions.mark_dirty_on_backtrack acts t;
          let lvl = max (Term.level eqn) (Term.level other) in
          ds.c_list <- C_singleton {v;other;eqn;tail=ds.c_list;lvl};
        | _ -> assert false
      end

    (* add constraint [t != v because diseqn] *)
    let add_diff acts t v ~diseqn ~other : unit =
      begin match Term.var t with
        | Var_semantic {v_decide_state=DS ds; _} ->
          Log.debugf 5
            (fun k->k "(@[<hv>%s.add_diff@ :to %a@ :val %a@ :other %a@ :diseqn %a@ :c_list %a@])"
                name Term.debug t Value.pp v Term.debug other Term.debug diseqn pp_c_list ds.c_list);
          (* first, check if SAT *)
          begin match find_conflict_diseq_ v ds.c_list with
            | Conflict_eq_eq _
            | Conflict_eq_neq _ -> assert false
            | Conflict_neq_eq {eqn;other=other'} ->
              (* conflict! one singleton, one diff, same value *)
              let eq_side = Term.mk_eq other other' in
              let conflict =
                [ Term.Bool.pa diseqn;
                  Term.Bool.na eqn;
                  Term.Bool.na eq_side;
                ]
              and lemma = Lemma.make Transitivity tc_lemma in
              Actions.raise_conflict acts conflict lemma
            | Conflict_none -> ()
          end;
          (* just add constraint *)
          let lvl = max (Term.level diseqn) (Term.level other) in
          let rec add_diff_ l = match l with
            | C_nil | C_diff _ -> C_diff {v;diseqn;other;tail=l;lvl}
            | C_singleton ({tail;_} as r) ->
              C_singleton {r with tail=add_diff_ tail}
          in
          Actions.mark_dirty_on_backtrack acts t;
          ds.c_list <- add_diff_ ds.c_list;
        | _ -> assert false
      end

    (* check if term now evaluates, or if it becomes a unit constraint *)
    let update_watches acts (eqn:term) ~watch:_ = match Term.view eqn with
      | Eq (a,b) ->
        begin match Term.value eqn, Term.value a, Term.value b with
          | TA_assign{value=V_true;_}, TA_assign{value;_}, TA_none ->
            (* TODO: propagate *)
            add_singleton acts b value ~eqn ~other:a
          | TA_assign{value=V_true;_}, TA_none, TA_assign{value;_} ->
            (* TODO: propagate *)
            add_singleton acts a value ~eqn ~other:b
          | TA_assign{value=V_false;_}, TA_assign{value;_}, TA_none ->
            add_diff acts b value ~diseqn:eqn ~other:a
          | TA_assign{value=V_false;_}, TA_none, TA_assign{value;_} ->
            add_diff acts a value ~diseqn:eqn ~other:b
          | _, TA_assign _, TA_assign _ ->
            (* semantic propagation *)
            (* FIXME: if term already assigned to *wrong* value, trigger
               conflict somehow? *)
            begin match eval_bool eqn with
              | Eval_unknown -> assert false
              | Eval_bool (b, subs) ->
                Actions.propagate_bool acts eqn b ~subs
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
      Term.tc_mk ~pp ~subterms ~update_watches ~init ~eval_bool ()

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

    (* find a value that is authorized by the list of constraints *)
    let[@inline] find_value (l:constraint_list): value = match l with
      | C_singleton {v;_} -> v
      | C_nil -> V.mk 0
      | _ ->
        (* is [i] forbidden by [l]? *)
        let rec forbidden i l = match l with
          | C_nil -> false
          | C_singleton _ -> assert false
          | C_diff {v;tail;_} -> V.get v=i || forbidden i tail
        in
        let i =
          Sequence.(0 -- max_int)
          |> Sequence.filter (fun i -> not (forbidden i l))
          |> Sequence.head_exn
        in
        V.mk i

    (* how to make a decision for terms of uninterpreted type *)
    let decide (acts:actions) (t:term) : value =
      begin match Term.var t with
        | Var_semantic {v_decide_state=DS{c_list}; _} ->
          let v = find_value c_list in
          Log.debugf 5
            (fun k->k "(@[<hv>%s.decide@ :term %a@ :val %a@ :lvl %d@ :c_list %a@])"
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
    let[@inline] mk_state () = DS {c_list=C_nil}

    (* filter constraints of level bigger than [lvl] *)
    let rec filter_lvl_ lvl (l:constraint_list) : constraint_list =
      begin match l with
        | C_nil -> C_nil
        | C_singleton ({lvl=l';tail;_} as r) ->
          let tail = filter_lvl_ lvl tail in
          if l' > lvl then tail else C_singleton {r with tail}
        | C_diff ({lvl=l';tail;_} as r) ->
          let tail = filter_lvl_ lvl tail in
          if l' > lvl then tail else C_diff {r with tail}
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

let plugin =
  Plugin.Factory.make
    ~priority:5
    ~name
    ~requires:Plugin.(K_cons (Builtins.k_true, K_nil))
    ~build
    ()

