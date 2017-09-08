
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
      mutable watches: Term.Watch1.t; (* 1-watch on [arg_1,…,arg_n,f(args)] *)
    }

type lemma_view +=
  | Congruence

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
          | App {id;ty;args;_} ->
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

    let lemma_congruence =
      let tcl_pp out = function
        | Congruence -> Fmt.string out "congruence"
        | _ -> assert false
      in
      let tc = { tcl_pp; } in
      Lemma.make Congruence tc

    (* [t] and [u] are two terms with equal arguments but distinct values,
       build [t1=u1 ∧ … ∧ tn=un => t=u] *)
    let mk_conflict_clause (t:term) (u:term) : atom list =
      begin match Term.view t, Term.view u with
        | App {id=f1; args=a1; _}, App {id=f2; args=a2; _} ->
          assert (ID.equal f1 f2);
          assert (Array.length a1 = Array.length a2);
          let conclusion = Term.mk_eq t u |> Term.Bool.pa
          and body =
            CCList.init (Array.length a1)
              (fun i -> Term.mk_eq a1.(i) a2.(i) |> Term.Bool.na)
          in
          conclusion :: body
        | _ -> assert false
      end

    (* signature: a function applied to values *)
    type signature = {
      sig_head: ID.t;
      sig_args: value array
    }

    module Sig_tbl = CCHashtbl.Make(struct
        type t = signature
        let equal a b =
          ID.equal a.sig_head b.sig_head &&
          CCArray.equal Value.equal a.sig_args b.sig_args
        let hash a =
          CCHash.combine2
            (ID.hash a.sig_head)
            (CCHash.array Value.hash a.sig_args)
      end)

    (* maps a signature to a value *)
    type tbl_entry = {
      e_sig: signature;
      mutable e_value: value;
      mutable e_reasons: term list;
      (* terms [f(t1…tn) --> v] with [t_i --> sig[i]] *)
    }

    (* big signature table *)
    let tbl_ : tbl_entry Sig_tbl.t = Sig_tbl.create 512

    (* check that [t], which should have fully assigned arguments,
       is consistent with the signature table *)
    let check_sig (acts:Actions.t) (t:term): unit =
      let v = Term.value_exn t in
      begin match Term.view t with
        | App {id;args;_} ->
          assert (Array.for_all Term.has_value args);
          let s = { sig_head=id; sig_args=Array.map Term.value_exn args } in
          let entry = match Sig_tbl.get tbl_ s with
            | None ->
              (* add new entry *)
              let entry = {
                e_sig=s;
                e_value=v;
                e_reasons=[]
              } in
              Sig_tbl.add tbl_ s entry;
              entry
            | Some entry ->
              if Value.equal v entry.e_value then (
                entry
              ) else (
                (* conflict *)
                let u = match entry.e_reasons with
                  | [] -> assert false
                  | u :: _ -> u
                in
                let c = mk_conflict_clause t u in
                Actions.raise_conflict acts c lemma_congruence
              )
          in
          entry.e_reasons <- t :: entry.e_reasons;
          (* on backtracking, remove [t] from reasons, and possibly remove
             the whole entry *)
          Actions.on_backtrack acts (Term.level t)
            (fun () ->
               entry.e_reasons <- CCList.remove ~eq:Term.equal ~x:t entry.e_reasons;
               if entry.e_reasons = [] then (
                 Sig_tbl.remove tbl_ s;
               ));
        | _ -> assert false
      end

    let init_watches acts t = match Term.view t with
      | Const _ -> ()
      | App ({args;_} as r) ->
        (* watch all arguments, plus term itself *)
        let watches =
          Term.Watch1.make_a
            (CCArray.init (Array.length args+1)
               (fun i-> if i=0 then t else args.(i-1)))
        in
        r.watches <- watches;
        Term.Watch1.init watches t ~on_all_set:(fun () -> check_sig acts t)
      | _ -> assert false

    let update_watches acts t ~watch = match Term.view t with
      | Const _ -> assert false (* no watches *)
      | App {watches;_} ->
        Term.Watch1.update watches t ~watch
          ~on_all_set:(fun () -> check_sig acts t)
      | _ -> assert false

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
        let watches = Term.Watch1.dummy in
        T_alloc.make (App {id;ty;args;watches}) ty tc

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

