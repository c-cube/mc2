
(** {1 Uninterpreted Functions and Constants} *)

open Mc2_core

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
  let tc = Term.TC.lazy_make () in
  let module P : Plugin.S = struct
    let id = p_id
    let name = name

    (* term allocator *)
    module T_alloc = Term.Term_allocator(struct
        let tc = tc
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
      | Const {id;_} -> ID.Smtlib.pp out id
      | App {id;args;_} ->
        Fmt.fprintf out "(@[%a@ %a@])" ID.Smtlib.pp id (Util.pp_array Term.pp) args
      | _ -> assert false

    let[@inline] subterms v yield = match v with
      | Const _ -> ()
      | App {args; _} -> Array.iter yield args
      | _ -> assert false

    (* build [{ a1.(i)≠a2.(i) | i}], removing trivial ones *)
    let mk_neq_ a1 a2 : atom list =
      Iter.(0 -- (Array.length a1-1))
      |> Iter.flat_map
        (fun i ->
           let t = a1.(i) and u = a2.(i) in
           if Term.equal t u then Iter.empty
           else if Type.is_bool (Term.ty t) then (
             (* instead of a1.(i)≠a2.(i), assume w.l.o.g a1.(i)=true=a2.(i),
                then output  ¬a1.(i), ¬a2.(i) *)
             if Term.Bool.is_true a1.(i)
             then Iter.doubleton (Term.Bool.na a1.(i)) (Term.Bool.na a2.(i))
             else Iter.doubleton (Term.Bool.pa a1.(i)) (Term.Bool.pa a2.(i))
           ) else Iter.return (Term.Bool.mk_neq t u))
      |> Iter.to_rev_list

    (* [t] and [u] are two terms with equal arguments but distinct values,
       build [t1=u1 ∧ … ∧ tn=un => t=u] *)
    let mk_conflict_clause_semantic (t:term) (u:term) : atom list =
      begin match Term.view t, Term.view u with
        | App {id=f1; args=a1; _}, App {id=f2; args=a2; _} ->
          assert (ID.equal f1 f2);
          assert (Array.length a1 = Array.length a2);
          let conclusion = Term.Bool.mk_eq t u
          and body = mk_neq_ a1 a2 in
          conclusion :: body
        | _ -> assert false
      end

    (* [t] and [u] are two boolean terms with equal arguments but
       distinct values (assume [t=true] [u=false] w.l.o.g.)
       build [t1=u1 ∧ … ∧ tn=u ∧ t => u] *)
    let mk_conflict_clause_bool (t:term) (u:term) : atom list =
      let t, u = if Term.Bool.is_true t then t, u else u, t in
      assert (Term.Bool.is_false u);
      begin match Term.view t, Term.view u with
        | App {id=f1; args=a1; _}, App {id=f2; args=a2; _} ->
          assert (ID.equal f1 f2);
          assert (Array.length a1 = Array.length a2);
          let conclusion = Term.Bool.pa u
          and body1 = Term.Bool.na t
          and body2 = mk_neq_ a1 a2 in
          conclusion :: body1 :: body2
        | _ -> assert false
      end

    (* signature: a function applied to values *)
    type signature = {
      sig_head: ID.t;
      sig_args: value array
    }

    let pp_sig out {sig_head=id; sig_args=a} =
      Fmt.fprintf out "(@[%a@ %a@])" ID.Smtlib.pp id (Util.pp_array Value.pp) a

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

    type e_reason = {
      e_level: level;
      e_term: term;
    }

    (* maps a signature to a value *)
    type tbl_entry = {
      e_sig: signature;
      mutable e_value: value;
      mutable e_reason: e_reason;
      (* terms [f(t1…tn) --> v] with [t_i --> sig[i]] *)
    }

    let pp_reason out {e_level=lvl;e_term=t} =
      Fmt.fprintf out "%a[at %d]" Term.debug t lvl

    (* big signature table *)
    let tbl_ : tbl_entry Sig_tbl.t = Sig_tbl.create 512

    exception E_arg_not_assigned

    (* check that [t], which should have fully assigned arguments,
       is consistent with the signature table *)
    let check_sig (acts:Actions.t) (t:term) : unit =
      try
        match Term.value t, Term.view t with
        | None, _ -> ()
        | Some v, App {id;args;_} ->
          let get_val t = match Term.value t with
            | None -> raise_notrace E_arg_not_assigned
            | Some v -> v
          in
          let sig_args = Array.map get_val args in
          let sigtr = { sig_head=id; sig_args } in
          Log.debugf 15
            (fun k->k "(@[uf.check_sig@ :sig %a@ :term %a@])" pp_sig sigtr Term.debug t);
          begin match Sig_tbl.get tbl_ sigtr with
            | None ->
              let lev_back = Term.max_level (Term.level t) (Term.level_semantic t) in
              let reason = {e_level=lev_back; e_term=t} in
              (* add new entry *)
              let entry = {
                e_sig=sigtr;
                e_value=v;
                e_reason=reason;
              } in
              Sig_tbl.add tbl_ sigtr entry;
              assert (lev_back>=0);
              (* on backtracking, remove [t] from reasons, and possibly remove
                 the whole entry *)
              Actions.on_backtrack acts
                (fun () ->
                   Log.debugf 15
                     (fun k->k "(@[<hv>uf.remove_entry@ :sig %a@ :lev %d@ :yields (@[%a@])@])"
                         pp_sig sigtr lev_back pp_reason entry.e_reason);
                   Sig_tbl.remove tbl_ sigtr)
            | Some entry ->
              if Value.equal v entry.e_value then (
                () (* compatible *)
              ) else (
                (* conflict *)
                (*Format.printf "tbl: %a@ entry %a@."
                    (Sig_tbl.print pp_sig pp_entry) tbl_ pp_entry entry;*)
                let u = entry.e_reason.e_term in
                Log.debugf 5
                  (fun k->k
                      "(@[<hv>uf.congruence_conflict@ :sig %a@ :t %a@ :u %a@ \
                       :t.args %a@ :u.args %a@])"
                      pp_sig sigtr Term.debug t Term.debug u
                      (Fmt.Dump.list Term.debug) (Term.subterms t)
                      (Fmt.Dump.list Term.debug) (Term.subterms u));
                if Type.is_bool (Term.ty t) then (
                  let c = mk_conflict_clause_bool t u in
                  Actions.raise_conflict acts c
                ) else (
                  let c = mk_conflict_clause_semantic t u in
                  Actions.raise_conflict acts c
                )
              )
          end
        | _ -> assert false
      with E_arg_not_assigned ->
        ()

    let init acts t = match Term.view t with
      | Const _ -> ()
      | App {args;_} ->
        let watcher acts _ =
          check_sig acts t;
          Watch_keep
        in
        (* watch all arguments, plus term itself *)
        Term.add_watch t ~watcher;
        Array.iter (Term.add_watch ~watcher) args;
      | _ -> assert false

    let check_if_sat _ = Sat
    let gc_all = T_alloc.gc_all
    let iter_terms = T_alloc.iter_terms

    let ty_decls_ : (Type.t list * Type.t) ID.Tbl.t = ID.Tbl.create 64

    let decl id ty_args ty_ret =
      Log.debugf 5
        (fun k->k "(@[uf.decl %a@ (@[%a@])@ %a@])"
            ID.pp id (Util.pp_list Type.pp) ty_args Type.pp ty_ret);
      if ID.Tbl.mem ty_decls_ id then (
        Error.errorf "%s: symbol `%a` already declared" name ID.pp id;
      );
      ID.Tbl.add ty_decls_ id (ty_args, ty_ret)

    (* compute type of [f l] *)
    let app_ty (f:ID.t) (l:term list) : Type.t =
      begin match ID.Tbl.get ty_decls_ f with
        | Some (args,_) when List.length args <> List.length l->
          Error.errorf "uf: type mismatch:@ `%a` needs %d arguments@ :got (@[%a@])"
            ID.pp f (List.length args) (Util.pp_list Term.pp) l
        | Some (ty_args,ty_ret) ->
          List.iter2
            (fun ty_arg arg ->
               if not (Type.equal ty_arg (Term.ty arg)) then (
                 Error.errorf
                   "uf: type mismatch:@ cannot apply `%a`@ :to (@[%a@])@ \
                    expected %a,@ got %a"
                   ID.pp f (Util.pp_list Term.pp) l Type.pp ty_arg Term.pp arg;
               ))
            ty_args l;
          ty_ret
        | None ->
          Error.errorf "uf: unknown function symbol `%a`" ID.pp f
      end

    (* constant builder *)
    let[@inline] const id : term =
      let ty = app_ty id [] in
      T_alloc.make (Const {id;ty}) ty

    (* application builder *)
    let[@inline] app id l : term = match l with
      | [] -> const id
      | _ ->
        (* proper application *)
        let ty = app_ty id l in
        let args = Array.of_list l in
        T_alloc.make (App {id;ty;args}) ty

    let () =
      Term.TC.lazy_complete tc ~pp ~init ~subterms

    let provided_services =
      [ Service.Any (k_app, app);
        Service.Any (k_const, const);
        Service.Any (k_decl, decl);
      ]
  end
  in
  (module P : Plugin.S)

let plugin = Plugin.Factory.make ~priority:10 ~name ~requires:Plugin.K_nil ~build ()

