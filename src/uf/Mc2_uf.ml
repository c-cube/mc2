
(** {1 Uninterpreted Functions and Constants} *)

open Mc2_core
open Solver_types

module Fmt = CCFormat

let name = "uf"
let k_const = Service.Key.make "uf.const"
let k_app = Service.Key.make "uf.app"
let k_decl = Service.Key.make "uf.decl"

type term_view +=
  | Const of {
      id: ID.t;
      ty: Type.t
    }
  | App of {
      id: ID.t;
      ty: Type.t;
      args: term array;
    }

let build p_id Plugin.S_nil : Plugin.t =
  let module P : Plugin.S = struct
    let id = p_id
    let name = name

    (* term allocator *)
    module T_alloc = Term.Term_allocator(struct
        let p_id = p_id
        let initial_size=256
        let[@inline] equal v1 v2 = match v1, v2 with
          | Const {id=f1;_}, Const {id=f2;_} -> ID.equal f1 f2
          | App {id=f1;args=a1;_}, App {id=f2;args=a2;_} ->
            ID.equal f1 f2 && CCArray.equal Term.equal a1 a2
          | Const _, _
          | App _, _ -> false
          | _ -> assert false
        let[@inline] hash = function
          | Const {id;ty} -> CCHash.combine3 10 (ID.hash id) (Type.hash ty)
          | App {id;ty;args} ->
            CCHash.combine4 20 (ID.hash id) (Type.hash ty) (CCHash.array Term.hash args)
          | _ -> assert false
      end)

    let tct_pp out = function
      | Const {id;_} -> ID.pp out id
      | App {id;args;_} ->
        Fmt.fprintf out "(@[%a@ %a@])" ID.pp id (Util.pp_array Term.pp) args
      | _ -> assert false

    let tct_simplify t = t
    let tct_eval_bool _ = Eval_unknown

    let[@inline] tct_subterms v yield = match v with
      | Const _ -> ()
      | App {args; _} -> Array.iter yield args
      | _ -> assert false

    (* TODO: 1-watch on [arg_1,…,arg_n, f(args) *)
    let tct_update_watches _ _ = ()

    (* TODO: check in big table if signature contradictory *)
    let tct_assign _ _ = Sat

    let tc : tc_term = {
      tct_pp;
      tct_update_watches;
      tct_subterms;
      tct_assign;
      tct_simplify;
      tct_eval_bool;
    }

    let check_if_sat _ = Sat
    let gc_all = T_alloc.gc_all
    let iter_terms = T_alloc.iter_terms

    let ty_decls_ : (Type.t list * Type.t) ID.Tbl.t = ID.Tbl.create 64

    let decl id ty_args ty_ret =
      if ID.Tbl.mem ty_decls_ id then (
        Util.errorf "%s: symbol `%a` already declared" name ID.pp id;
      );
      ID.Tbl.add ty_decls_ id (ty_args, ty_ret)

    (* constant builder *)
    let[@inline] const id ty : term = T_alloc.make (Const {id;ty}) ty tc

    (* application builder *)
    let[@inline] app id ty l : term = match l with
      | [] -> const id ty
      | _ ->
        (* proper application *)
        let args = Array.of_list l in
        T_alloc.make (App {id;ty;args}) ty tc

    let provided_services =
      [ Service.Any (k_app, app);
        Service.Any (k_const, const);
      ]
  end
  in
  (module P : Plugin.S)

let plugin =
  Plugin.Factory.make
    ~priority:10
    ~name
    ~requires:Plugin.K_nil
    ~build
    ()

