
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

    let pp out = function
      | Const {id;_} -> ID.pp_name out id
      | App {id;args;_} ->
        Fmt.fprintf out "(@[%a@ %a@])" ID.pp_name id (Util.pp_array Term.pp) args
      | _ -> assert false

    let eval_bool _ = Eval_unknown

    let[@inline] subterms v yield = match v with
      | Const _ -> ()
      | App {args; _} -> Array.iter yield args
      | _ -> assert false

    (* TODO: 1-watch on [arg_1,…,arg_n, f(args) *)
    let update_watches _ _ ~watch:_ = Watch_keep

    (* TODO: 1-watch on [arg_1,…,arg_n, f(args) *)
    let init_watches _ _ = ()

    let tc : tc_term =
      Term.tc_mk ~pp ~update_watches ~init_watches ~subterms
        ~eval_bool ()

    let check_if_sat _ = Sat
    let gc_all = T_alloc.gc_all
    let iter_terms = T_alloc.iter_terms

    let ty_decls_ : (Type.t list * Type.t) ID.Tbl.t = ID.Tbl.create 64

    let decl id ty_args ty_ret =
      Log.debugf 5
        (fun k->k "(@[uf.decl %a@ (@[%a@])@ %a@])"
            ID.pp id (Util.pp_list Type.pp) ty_args Type.pp ty_ret);
      if ID.Tbl.mem ty_decls_ id then (
        Util.errorf "%s: symbol `%a` already declared" name ID.pp id;
      );
      ID.Tbl.add ty_decls_ id (ty_args, ty_ret)

    (* compute type of [f l] *)
    let app_ty (f:ID.t) (l:term list) : Type.t =
      begin match ID.Tbl.get ty_decls_ f with
        | Some (args,_) when List.length args <> List.length l->
          Util.errorf "uf: type mismatch:@ `%a` needs %d arguments@ :got (@[%a@])"
            ID.pp f (List.length args) (Util.pp_list Term.pp) l
        | Some (ty_args,ty_ret) ->
          List.iter2
            (fun ty_arg arg ->
               if not (Type.equal ty_arg (Term.ty arg)) then (
                 Util.errorf
                   "uf: type mismatch:@ cannot apply `%a`@ :to (@[%a@])@ \
                   expected %a,@ got %a"
                   ID.pp f (Util.pp_list Term.pp) l Type.pp ty_arg Term.pp arg;
               ))
            ty_args l;
          ty_ret
        | None ->
          Util.errorf "uf: unknown function symbol `%a`" ID.pp f
      end

    (* constant builder *)
    let[@inline] const id : term =
      let ty = app_ty id [] in
      T_alloc.make (Const {id;ty}) ty tc

    (* application builder *)
    let[@inline] app id l : term = match l with
      | [] -> const id
      | _ ->
        (* proper application *)
        let ty = app_ty id l in
        let args = Array.of_list l in
        T_alloc.make (App {id;ty;args}) ty tc

    let provided_services =
      [ Service.Any (k_app, app);
        Service.Any (k_const, const);
        Service.Any (k_decl, decl);
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

