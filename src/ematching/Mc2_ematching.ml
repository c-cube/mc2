
(** {1 E-matching} *)

open Mc2_core
open Solver_types

let name = "ematching"

type pattern_view = ..

type var = {
  v_id : ID.t;
  v_ty : Type.t;
}

let var_cmp v1 v2 = ID.compare v1.v_id v2.v_id

module Var_map = CCMap.Make(struct
    type t = var
    let compare = var_cmp
  end)

type pattern =
  | P_var of var
  | P_app of {
      id: ID.t;
      ty: Type.t;
      args: pattern array;
    }
  | P_term of term
  | P_value of value
  | P_custom of {
      view: pattern_view;
      ty: Type.t;
      tc: tc_pattern;
    }

and match_fun = subst -> pattern -> term -> subst Sequence.t

and tc_pattern = {
  tcp_pp : pattern_view Fmt.printer;
  tct_match : match_fun -> subst -> pattern_view -> term -> subst Sequence.t;
}

and subst = term Var_map.t
(* maps variables to terms *)

module Var = struct
  type t = var

  let[@inline] id v = v.v_id
  let[@inline] ty v = v.v_ty
  let compare = var_cmp
  let[@inline] equal a b = compare a b = 0
  let[@inline] hash v = ID.hash v.v_id

  let[@inline] make v_id v_ty : t = {v_id; v_ty}

  let fresh =
    let n = ref 0 in
    fun ty -> make (ID.makef "x_%d" (CCRef.get_then_incr n)) ty

  let pp out v = ID.pp out (id v)
end

module Subst = struct
  type t = subst

  let empty = Var_map.empty
  let[@inline] mem s v = Var_map.mem v s
  let[@inline] add s v t = Var_map.add v t s
  let[@inline] get s v = Var_map.get v s
  let to_list = Var_map.to_list

  let pp out (s:t) =
    let pp_b out (v,t) = Fmt.fprintf out "(@[%a@ -> %a@])" Var.pp v Term.pp t in
    Fmt.fprintf out "{@[%a@]}" (Util.pp_seq ~sep:"," pp_b) (Var_map.to_seq s)
end

(** {2 Patterns} *)
module Pattern = struct
  type t = pattern
  type view = pattern_view
  type tc = tc_pattern

  let[@inline] var v : t = P_var v
  let[@inline] app_a id ty args : t = P_app {id;ty;args}
  let[@inline] app_l id ty args = app_a id ty (Array.of_list args)
  let[@inline] const c ty : t = app_a c ty [| |]
  let[@inline] of_term t : t = P_term t
  let[@inline] of_value v : t = P_value v

  let[@inline] make view ty tc : t = P_custom {view;ty;tc}

  let[@inline] ty (t:t) : ty = match t with
    | P_app {ty;_} -> ty
    | P_var v -> Var.ty v
    | P_term t -> Term.ty t
    | P_value v -> Value.ty v
    | P_custom {ty;_} -> ty

  let[@inline] is_top = function
    | P_app _ -> true
    | P_var _ | P_term _ | P_value _ | P_custom _ -> false

  let rec pp out (p:t) : unit =
    begin match p with
      | P_value v -> Value.pp out v
      | P_term t -> Term.pp out t
      | P_var v -> Var.pp out v
      | P_app {id;args;_} ->
        if Array.length args=0 then ID.pp_name out id
        else (
          Fmt.fprintf out "(@[%a@ %a@])" ID.pp_name id  (Util.pp_array pp) args
        )
      | P_custom {view;tc;_} -> tc.tcp_pp out view
    end
end

type id_instance = {
  ii_term: term; (* [id t1…tn] *)
  ii_args: term array; (* [t1…tn], the arguments of the ID *)
}

let k_iter_value_symbol = Service.Key.makef "%s.iter_value_sym" name
let k_iter_symbol = Service.Key.makef "%s.iter_sym" name
let k_e_match = Service.Key.makef "%s.match" name
let k_e_match_with = Service.Key.makef "%s.match_with" name

type state = {
  iter_symbol: ID.t -> id_instance Sequence.t;
  iter_value_symbol : Value.t -> ID.t -> id_instance Sequence.t;
}

let[@inline] same_val (t:term) (u:term) : bool =
  Value.equal (Term.value_exn t) (Term.value_exn u)

(* main E-matching of [p] against [t] *)
let rec e_match_ st subst (p:pattern) (t:term) yield : unit =
  assert (Type.equal (Pattern.ty p) (Term.ty t));
  begin match p with
    | P_var x ->
      begin match Subst.get subst x with
        | None -> yield (Subst.add subst x t) (* bind *)
        | Some u ->
          if same_val t u then yield subst;
      end
    | P_app {id;args=p_args;_} ->
      (* iterate over terms that start with [id] and have the same
         value as [t] *)
      st.iter_value_symbol (Term.value_exn t) id
        (fun ii ->
           assert (Array.length ii.ii_args = Array.length p_args);
           e_match_a_ st subst p_args ii.ii_args 0 yield)

    | P_term u -> if same_val t u then yield subst;
    | P_value v ->
      if Value.equal v (Term.value_exn t) then yield subst
    | P_custom {view;tc;_} ->
      (* delegate to custom TC *)
      tc.tct_match (e_match_ st) subst view t yield
  end

(* match array [p_a] with array [t_a] *)
and e_match_a_ st subst (p_a:pattern array) (t_a:term array) i yield =
  if i = Array.length p_a then (
    assert (i = Array.length t_a);
    yield subst
  ) else (
    (* match i-th pair before recursing *)
    e_match_ st subst p_a.(i) t_a.(i)
      (fun subst ->
         e_match_a_ st subst p_a t_a (i+1) yield)
  )

let[@inline] e_match_with st p t = e_match_ st Subst.empty p t

let e_match (st:state) (p:pattern) (yield:subst -> unit) : unit =
  begin match p with
    | P_app {id;args=p_args;_} ->
      st.iter_symbol id
        (fun ii ->
           assert (Array.length ii.ii_args = Array.length p_args);
           e_match_a_ st Subst.empty p_args ii.ii_args 0 yield)
    | _ ->
      assert (not (Pattern.is_top p));
      Util.errorf "e_match: need a top-pattern,@ not `%a`" Pattern.pp p
  end

let build
    (p_id:plugin_id)
    Plugin.(S_cons (_,iter_symbol,S_cons (_,iter_value_symbol,S_nil)))
  : Plugin.t =
  let module P = struct
    let id = p_id
    let name = name
    let st : state = {iter_symbol; iter_value_symbol}
    let provided_services = [
      Service.Any (k_e_match, e_match st);
      Service.Any (k_e_match_with, e_match_with st);
    ]

    let check_if_sat _ = Sat
    let gc_all _ = 0
    let iter_terms _=()
  end in
  (module P)

let plugin =
  Plugin.Factory.make ~priority:20 ~name ~build
    ~requires:Plugin.(K_cons (k_iter_symbol,K_cons (k_iter_value_symbol,K_nil)))
    ()
