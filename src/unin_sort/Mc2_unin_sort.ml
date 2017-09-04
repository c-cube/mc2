
(** {1 Uninterpreted Functions and Types} *)

open Mc2_core
open Solver_types

module Fmt = CCFormat

[@@@warning "-38"] (* FIXME remove *)

let name = "unin_sort"
let k_decl_sort = Service.Key.make "unin_sort.decl"
let k_make = Service.Key.make "unin_sort.make"
let k_eq = Service.Key.make "unin_sort.eq"

module Int_map = CCMap.Make(CCInt)

(* current knowledge for a value of an uninterpreted type *)
type decide_state +=
  | Forbid of {
      mutable values: reason Int_map.t; (* list of (value,expl) that are forbidden *)
    } (** Term cannot be equal to any of these values *)
  | Singleton of {
      value: value;
      reason: reason;
    } (** Term must be equal to this value *)

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

(* values for uninterpreted sorts *)
module V = struct
  let tcv_pp out = function
    | V_unin i -> Fmt.fprintf out "$v_%d" i
    | _ -> assert false

  let tcv_hash = function V_unin i -> CCHash.int i | _ -> assert false

  let tcv_equal v1 v2 = match v1, v2 with
    | V_unin i, V_unin j -> i=j
    | _ -> false

  let tc_value = {
    tcv_pp; tcv_equal; tcv_hash;
  }

  let[@inline] mk (i:int) : value = Value.make tc_value (V_unin i)
end

let build p_id (Plugin.S_cons (_, true_, Plugin.S_nil)) : Plugin.t =
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

      let tcty_pp out = function
        | Unin {id;args=[];_} -> ID.pp out id
        | Unin {id;args;_} ->
          Format.fprintf out "(@[%a@ %a@])" ID.pp id (Util.pp_list Type.pp) args
        | _ -> assert false

      (* how to make a decision *)
      let tcty_decide (_acts:actions) (t:term) : value =
        Log.debugf 5 (fun k->k "(@[%s: decide@ :term %a@])" name Term.pp t);
        begin match Term.var t with
          | Var_semantic {v_decide_state=Singleton {value;_}; _} ->
            value (* only one possibility *)
          | Var_semantic {v_decide_state=Forbid {values}; _} ->
            (* find the first integer not in [values] *)
            let i =
              Sequence.(0 -- max_int)
              |> Sequence.filter (fun i -> not (Int_map.mem i values))
              |> Sequence.head_exn
            in
            V.mk i
          | _ -> assert false
        end

      let[@inline] tcty_mk_state () = Forbid {values=Int_map.empty}

      let tc : tc_ty = { tcty_pp; tcty_decide; tcty_mk_state; }
    end)
  in
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
        (fun k->k "(@[declare-sort %a@ :arity %d@])" ID.pp id arity);
      if ID.Tbl.mem tbl_ id then (
        Util.errorf "sort %a already declared" ID.pp id;
      );
      ID.Tbl.add tbl_ id arity

    let[@inline] is_unin_sort (ty:Type.t) : bool = match ty with
      | Ty {view=Unin _; _} -> true
      | _ -> false

    (* make a concrete instance of the type *)
    let make (id:ID.t) (args:Type.t list) : Type.t =
      begin match ID.Tbl.get tbl_ id with
        | Some ar when ar=List.length args ->
          Ty_alloc.make (Unin {id;args})
        | Some ar ->
          Util.errorf "wrong arity for sort %a:@ need %d args,@ got (@[%a@])"
            ID.pp id ar (Util.pp_list Type.pp) args
        | None ->
          Util.errorf "no uninterpreted sort for %a" ID.pp id
      end

    let tct_simplify t = t
    let tct_pp out = function
      | Eq(a,b) -> Fmt.fprintf out "(@[<hv>= %a %a@])" Term.pp a Term.pp b
      | _ -> assert false

    let tct_subterms v yield = match v with
      | Eq(a,b) -> yield a; yield b
      | _ -> assert false

    (* evaluate equality *)
    let tct_eval_bool (t:term) : eval_bool_res = match Term.view t with
      | Eq (a, b) when Term.equal a b -> Eval_bool (true, [])
      | Eq (a, b) ->
        begin match Term.Semantic.value a, Term.Semantic.value b with
          | V_assign {value=va;_}, V_assign {value=vb;_} ->
            Eval_bool (Value.equal va vb, [a;b])
          | _ -> Eval_unknown
        end
      | _ -> assert false

    let tct_assign _ (t:term) = match Term.view t with
      | Eq (_a,_b) ->
        assert false (* TODO: check if a=va, b=vb, (a=b)=(va=vb) *)
      | _ -> assert false

    let tct_update_watches _ (t:term) = match Term.view t with
      | Eq (_a,_b) ->
        assert false (* TODO: see if we can watch another term, else use Singleton *)
      | _ -> assert false

    let tc_term = {
      tct_pp;
      tct_update_watches;
      tct_subterms;
      tct_assign;
      tct_eval_bool;
      tct_simplify;
    }

    (* equality literal *)
    let mk_eq (t:term) (u:term): term =
      if not (is_unin_sort (Term.ty t)) then (
        Util.errorf
          "unin_sort.eq:@ expected term of an uninterpreted sort,@ got %a"
          Term.pp t
      );
      if not (Type.equal (Term.ty t) (Term.ty u)) then (
        Util.errorf
          "unin_sort.eq:@ terms should have same type,@ got %a@ and %a"
          Term.pp t Term.pp u
      );
      if Term.equal t u then true_ (* auto-simplify *)
      else (
        let view = if Term.id t < Term.id u then Eq (t,u) else Eq (u,t) in
        Term_alloc.make view (Term.ty t) tc_term
      )

    let provided_services =
      [ Service.Any (k_decl_sort, decl_sort);
        Service.Any (k_make, make);
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

