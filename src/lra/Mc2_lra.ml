
(** {1 Linear Rational Arithmetic} *)

(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LRA *)

(* TODO:
   define relu with terms instead of LE.t
   might be possible to test the atomic LE.t AND
   retrieve the terms in mk_relu with LE.as_singleton
*)

open Mc2_core
open Solver_types

module LE = Linexp
open LE.Infix

let name = "lra"

type num = Q.t

type ty_view +=
  | Ty_rat

type value_view +=
  | V_rat of num

(** Boolean operator for predicates *)
type op =
  | Eq0
  | Leq0
  | Lt0

(* a single constraint on a Q-sorted variables *)
type constr =
  | C_leq
  | C_lt
  | C_geq
  | C_gt
  | C_eq
  | C_neq

type reason =
  | Atom of atom
  | ReLU_prop_apply_3
  | ReLU_prop_apply_4_or_5

let debug_reason out (a:reason) = match a with
  | Atom a -> Atom.debug out a
  | _ -> Format.fprintf out "relu_propagation"

let atomic_reason (r:reason) : atom = match r with
  | Atom a -> a
  | _ -> Util.errorf "This ReLU analysis case is not handled yet."

type bound =
  | B_some of {strict:bool; num: num; expr: LE.t; reason:reason}
  | B_none (* no bound *)

type eq_cstr =
  | EC_eq of {num:num; reason:atom; expr: LE.t}
  | EC_neq of {l: (num * LE.t * atom) list} (* forbidden values *)
  | EC_none

(* state for a single Q-sorted variable *)
type decide_state +=
  | State of {
      mutable last_val: num; (* phase saving *)
      mutable low: bound;
      mutable up: bound;
      mutable eq: eq_cstr;
    }

type term_view +=
  | Const of num
  | Pred of {
      op: op;
      expr: LE.t;
      mutable watches: Term.Watch2.t; (* can sometimes propagate *)
    } (** Arithmetic constraint *)
  | ReLU of {x: LE.t; y: LE.t; mutable watches: Term.Watch2.t;}


type lemma_view +=
  | Lemma_lra
  | Lemma_relu

let k_rat = Service.Key.makef "%s.rat" name
let k_make_const = Service.Key.makef "%s.make_const" name
let k_make_pred = Service.Key.makef "%s.make_pred" name
let k_make_relu = Service.Key.makef "%s.make_relu" name

let[@inline] equal_op a b =
  begin match a, b with
    | Eq0, Eq0
    | Leq0, Leq0
    | Lt0, Lt0 -> true
    | Eq0, _ | Leq0, _ | Lt0, _ -> false
  end

let[@inline] hash_op a = match a with
  | Eq0 -> 0
  | Leq0 -> 1
  | Lt0 -> 2

(* evaluate a linexp into a number *)
let[@inline] eval_le (e:LE.t) : (num * term list) option =
  LE.eval e
    ~f:(fun t -> match Term.value t with
        | Some (V_value {view=V_rat n;_}) -> Some n
        | _ -> None)

let tc_value =
  let tcv_pp out = function
    | V_rat q -> Q.pp_print out q
    | _ -> assert false
  and tcv_equal a b = match a, b with
    | V_rat a, V_rat b -> Q.equal a b
    | _ -> false
  and tcv_hash = function
    | V_rat r -> LE.hash_q r
    | _ -> assert false
  in
  {tcv_pp; tcv_hash; tcv_equal}

let[@inline] mk_val (n:num) : value = Value.make tc_value (V_rat n)

(* evaluate the linear expression
   precondition: all terms in it are assigned *)
let[@inline] eval_le_num_exn (e:LE.t) : num = match eval_le e with
  | Some (n,_) -> n
  | None -> assert false

let pp_ty out = function Ty_rat -> Fmt.fprintf out "@<1>ℚ" | _ -> assert false

let mk_state _ : decide_state =
  State {
    last_val=Q.zero;
    up=B_none;
    low=B_none;
    eq=EC_none;
  }

let pp_constr out (e:constr) = match e with
  | C_leq -> Fmt.string out "≤"
  | C_lt -> Fmt.string out "<"
  | C_geq -> Fmt.string out "≥"
  | C_gt -> Fmt.string out ">"
  | C_eq -> Fmt.string out "="
  | C_neq -> Fmt.string out "≠"

let pp_bound out = function
  | B_none -> Fmt.string out "ø"
  | B_some {strict;num;reason;expr} ->
    let strict_str = if strict then "[strict]" else "" in
    Fmt.fprintf out "(@[%a%s@ :expr %a@ :reason %a@])"
      Q.pp_print num strict_str LE.pp expr debug_reason reason

let pp_eq out = function
  | EC_none -> Fmt.string out "ø"
  | EC_eq {num;reason;expr} ->
    Fmt.fprintf out "(@[= %a@ :expr %a@ :reason %a@])"
      Q.pp_print num LE.pp expr Atom.debug reason
  | EC_neq {l} ->
    let pp_tuple out (n,e,a) =
      Fmt.fprintf out "(@[%a@ :expr %a@ :reason %a@])"
        Q.pp_print n LE.pp e Atom.debug a
    in
    Fmt.fprintf out "(@[<hv>!=@ %a@])"
      (Util.pp_list pp_tuple) l

let pp_state out = function
  | State s ->
    Fmt.fprintf out "(@[<hv>:low %a@ :up %a@ :eq %a@])"
      pp_bound s.low pp_bound s.up pp_eq s.eq
  | _ -> assert false

let[@inline] subterms (t:term_view) : term Sequence.t = match t with
  | Const _ -> Sequence.empty
  | Pred {expr=e;_} -> LE.terms e
  | ReLU {x=e1;y=e2;_} -> Sequence.append (LE.terms e1) (LE.terms e2)
  | _ -> assert false

let pp_op out = function
  | Eq0 -> Fmt.string out "= 0"
  | Leq0 -> Fmt.string out "≤ 0"
  | Lt0 -> Fmt.string out "< 0"

let pp_term out = function
  | Const n -> Q.pp_print out n
  | Pred {op;expr;_} ->
    Fmt.fprintf out "(@[%a@ %a@])" LE.pp_no_paren expr pp_op op
  | ReLU {x;y;_} ->
    Fmt.fprintf out "(ReLU %a %a)" LE.pp_no_paren x LE.pp_no_paren y
  | _ -> assert false

(* evaluate [op n] where [n] is a constant *)
let[@inline] eval_bool_const op n : bool =
  begin match Q.sign n, op with
    | 0, Eq0 -> true
    | n, Leq0 when n<=0 -> true
    | n, Lt0 when n<0 -> true
    | _ -> false
  end

let eval_relu (n:Q.t) : Q.t =
  if Q.compare n Q.zero < 0
  then Q.zero
  else n

(* evaluate an arithmetic boolean expression *)
let eval (t:term) = match Term.view t with
  | Const n -> Eval_into (mk_val n, [])
  | Pred {op;expr=e;_} ->
    begin match eval_le e with
      | None -> Eval_unknown
      | Some (n,l) -> Eval_into (Value.of_bool @@ eval_bool_const op n, l)
    end
  | ReLU {x;y;_} ->
    begin match eval_le x, eval_le y with
      | Some (nx,lx), Some (ny,ly) ->
        Eval_into (Value.of_bool (Q.equal ny @@ eval_relu nx), lx @ ly)
      | None, Some _ -> Eval_unknown
      | Some _, None -> Eval_unknown
      | None, None -> Eval_unknown
    end

  | _ -> assert false

let tc_lemma : tc_lemma = {
  tcl_pp=(fun out l -> match l with
      | Lemma_lra -> Fmt.string out "lra"
      | Lemma_relu -> Fmt.string out "relu"
      | _ -> assert false
    );
}

let lemma_lra = Lemma.make Lemma_lra tc_lemma
let lemma_relu = Lemma.make Lemma_relu tc_lemma

(* build plugin *)
let build
    p_id
    (Plugin.S_cons (_,true_, Plugin.S_cons (_,false_,Plugin.S_nil)))
  : Plugin.t =
  let tc_t = Term.TC.lazy_make() in
  let tc_ty = Type.TC.lazy_make() in
  let module T = Term.Term_allocator(struct
      let tc = tc_t
      let initial_size = 64
      let p_id = p_id
      let equal a b = match a, b with
        | Const n1, Const n2 -> Q.equal n1 n2
        | Pred p1, Pred p2 -> p1.op = p2.op && LE.equal p1.expr p2.expr
        | ReLU r1, ReLU r2 -> (LE.equal r1.x r2.x) && LE.equal r1.y r2.y
        | _ -> false
      let hash = function
        | Const n -> LE.hash_q n
        | Pred {op;expr;_} -> CCHash.combine3 10 (hash_op op) (LE.hash expr)
        | ReLU {x;y;_} -> CCHash.combine3 11 (LE.hash x) (LE.hash y)
        | _ -> assert false
    end)
  in
  let module P = struct
    let id = p_id
    let name = name

    let gc_all = T.gc_all
    let iter_terms = T.iter_terms
    let check_if_sat _ = Sat

    let ty_rat = lazy (
      let tc = Type.TC.lazy_get tc_ty in
      Type.make_static Ty_rat tc
    )

    (* build a predicate on a linear expression *)
    let mk_pred (op:op) (e:LE.t) : term =
      begin match LE.as_const e with
        | Some n ->
          (* directly evaluate *)
          if eval_bool_const op n then true_ else false_
        | None ->
          let e = LE.simplify e in
          let view = Pred {op; expr=e; watches=Term.Watch2.dummy} in
          T.make view Type.bool
      end

    let mk_const (n:num) : term = T.make (Const n) (Lazy.force ty_rat)

    let mk_relu (x:LE.t) (y:LE.t): term =
      begin match LE.as_const x, LE.as_const y with
        | Some nx, _ ->
          let ans = eval_relu nx in
          mk_pred Eq0 (LE.diff y @@ LE.const ans)
        | None, Some ny ->
          if ny > Q.zero
          then mk_pred Eq0 (LE.diff x @@ LE.const ny)
          else mk_pred Lt0 x
        | None, None ->
          (* ensure x and y are singletons *)
          (* STRANGE: it seems new terms are automatically created *)
          (* so the condition is ALWAYS verified, even in *)
          (* (assert (relu x (+ 1 y))) for example *)
          let x = LE.singleton1 (LE.singleton_term x) and y = LE.singleton1 (LE.singleton_term y) in
          let view = ReLU {x=x; y=y; watches=Term.Watch2.dummy} in
          Log.debugf 20 (fun k->k "mk_relu %a" pp_term view);
          T.make view Type.bool
      end

    (* raise a conflict that deduces [expr_up_bound - Hexpr_low_bound op 0] (which must
       eval to [false]) from [reasons] *)
    let raise_conflict acts
        ~sign ~op ~pivot ~expr_up_bound ~expr_low_bound ~reasons () : 'a =
      let expr = LE.diff expr_low_bound expr_up_bound in
      assert (not (LE.mem_term pivot expr));
      let concl = mk_pred op expr in
      let concl = if sign then Term.Bool.pa concl else Term.Bool.na concl in
      let c = concl :: List.map Atom.neg reasons in
      Log.debugf 30
        (fun k->k
            "(@[<hv>lra.raise_conflict@ :pivot %a@ :expr %a %a@ \
             :e_up_b %a@ :e_low_b %a@ \
             :reasons (@[<v>%a@])@ :clause %a@])"
            Term.debug pivot LE.pp expr pp_op op LE.pp expr_up_bound LE.pp expr_low_bound
            (Util.pp_list Atom.debug) reasons Clause.debug_atoms c);
      Actions.raise_conflict acts c lemma_lra

    (* [make op e t ~reason b] turns this unit constraint over [t]
       (which is true or false according to [b]) into a proper
       unit constraint *)
    let constr_of_unit (op:op) (e:LE.t) (t:term) (b:bool) : constr * LE.t * num =
      let coeff = LE.find_term_exn t e in
      let is_pos = Q.sign coeff >= 0 in
      (* [e' = - e / coeff] *)
      let e' = LE.mult (Q.div Q.minus_one coeff) (LE.remove_term t e) in
      let num = eval_le_num_exn e' in
      (* assuming [b=true] and [is_pos],
         we have that reason is the same in the current model as [op(t + num)] *)
      begin match op, b, is_pos with
        | Eq0, true, _ -> C_eq
        | Eq0, false, _ -> C_neq
        | Leq0, true, true -> C_leq
        | Leq0, true, false -> C_geq
        | Leq0, false, true -> C_gt
        | Leq0, false, false -> C_lt
        | Lt0, true, true -> C_lt
        | Lt0, true, false -> C_gt
        | Lt0, false, true -> C_geq
        | Lt0, false, false -> C_leq
      end, e', num

    (* check that there isn't a conflict of the shape [a <= t <= a, t != a] *)
    let check_tight_bound acts t : unit = match Term.decide_state_exn t with
      | State s ->
        begin match s.low, s.up, s.eq with
          | B_some low, B_some up, EC_neq {l} when
              Q.equal low.num up.num &&
              List.exists (fun (n,_,_) -> Q.equal low.num n) l
            ->
            assert (not low.strict);
            assert (not up.strict);
            let reason_neq =
              CCList.find_map
                (fun (n,_,r) -> if Q.equal low.num n then Some r else None)
                l |> CCOpt.get_exn
            in
            (* conflict should be:
               [low <= t & t <= up & low=up => t = neq]. *)
            raise_conflict acts
              ~sign:false ~op:Eq0 ~pivot:t
              ~expr_up_bound:up.expr ~expr_low_bound:low.expr
              ~reasons:[atomic_reason up.reason; atomic_reason low.reason; reason_neq] ()
          | _ -> ()
        end
      | _ -> assert false

    (* add upper bound *)
    let add_up acts ~strict t num ~expr ~(reason:reason) : unit = match Term.decide_state_exn t with
      | State s ->
        (* check consistency *)
        begin match s.eq, s.low with
          | EC_eq eq, _ when
              (strict && Q.compare eq.num num >= 0) ||
              (not strict && Q.compare eq.num num > 0) ->
            raise_conflict acts
              ~sign:true ~op:(if strict then Lt0 else Leq0) ~pivot:t
              ~expr_up_bound:expr ~expr_low_bound:eq.expr ~reasons:[atomic_reason reason; eq.reason] ()
          | _, B_some b when
              ((strict || b.strict) && Q.compare b.num num >= 0) ||
              (Q.compare b.num num > 0) ->
            raise_conflict acts
              ~sign:true ~op:(if strict || b.strict then Lt0 else Leq0) ~pivot:t
              ~expr_up_bound:expr ~expr_low_bound:b.expr ~reasons:[atomic_reason reason; atomic_reason b.reason] ()
          | _ -> ()
        end;
        (* update *)
        let old_b = s.up in
        Actions.on_backtrack acts (fun () -> s.up <- old_b);
        begin match s.up with
          | B_none ->
            s.up <- B_some {strict;num;reason;expr};
            check_tight_bound acts t;
          | B_some b ->
            (* only replace if more tight *)
            if Q.compare b.num num > 0 ||
               (strict && not b.strict && Q.equal b.num num) then (
              s.up <- B_some {strict;num;reason;expr};
              check_tight_bound acts t;
            )
        end;
      | _ -> assert false

    (* add lower bound *)
    let add_low acts ~strict t num ~expr ~(reason:reason) : unit = match Term.decide_state_exn t with
      | State s ->
        (* check consistency *)
        begin match s.eq, s.up with
          | EC_eq eq, _ when
              (strict && Q.compare eq.num num <= 0) ||
              (not strict && Q.compare eq.num num < 0) ->
            raise_conflict acts
              ~sign:true ~op:(if strict then Lt0 else Leq0) ~pivot:t
              ~expr_low_bound:expr ~expr_up_bound:eq.expr ~reasons:[atomic_reason  reason; eq.reason] ()
          | _, B_some b when
              ((strict || b.strict) && Q.compare b.num num <= 0) ||
              (Q.compare b.num num < 0) ->
            raise_conflict acts
              ~sign:true ~op:(if strict || b.strict then Lt0 else Leq0) ~pivot:t
              ~expr_low_bound:expr ~expr_up_bound:b.expr ~reasons:[atomic_reason reason; atomic_reason b.reason] ()
          | _ -> ()
        end;
        (* update state *)
        let old_b = s.low in
        Actions.on_backtrack acts (fun () -> s.low <- old_b);
        begin match s.low with
          | B_none ->
            s.low <- B_some {strict;num;reason;expr};
            check_tight_bound acts t;
          | B_some b ->
            (* only replace if more tight *)
            if Q.compare b.num num < 0 ||
               (strict && not b.strict && Q.equal b.num num) then (
              s.low <- B_some {strict;num;reason;expr};
              check_tight_bound acts t;
            )
        end
      | _ -> assert false

    (* add exact bound *)
    let add_eq acts t num ~expr ~reason : unit = match Term.decide_state_exn t with
      | State s ->
        (* check compatibility with bounds *)
        begin match s.low, s.up with
          | B_some b, _ when
              (b.strict && Q.compare b.num num >= 0) ||
              (not b.strict && Q.compare b.num num > 0) ->
            raise_conflict acts ~op:(if b.strict then Lt0 else Leq0)
              ~sign:true ~pivot:t ~expr_up_bound:expr ~expr_low_bound:b.expr
              ~reasons:[reason; atomic_reason b.reason] ()
          | _, B_some b when
              (b.strict && Q.compare b.num num <= 0) ||
              (not b.strict && Q.compare b.num num < 0) ->
            raise_conflict acts ~op:(if b.strict then Lt0 else Leq0)
              ~sign:true ~pivot:t ~expr_low_bound:expr ~expr_up_bound:b.expr
              ~reasons:[reason; atomic_reason b.reason] ()
          | _ -> ()
        end;
        (* check other equality constraints, and update *)
        let old_b = s.eq in
        Actions.on_backtrack acts (fun () -> s.eq <- old_b);
        begin match s.eq with
          | EC_none -> s.eq <- EC_eq {num;reason;expr}
          | EC_neq {l;_} ->
            (* check if compatible *)
            List.iter
              (fun (n2, expr2, reason_neq) ->
                 if Q.equal num n2 then (
                   (* conflict *)
                   assert (Atom.is_true reason_neq);
                   raise_conflict acts ~pivot:t ~op:Eq0 ~sign:false
                     ~expr_up_bound:expr ~expr_low_bound:expr2 ~reasons:[reason_neq; reason] ()
                 ))
              l;
            (* erase *)
            s.eq <- EC_eq {num;reason;expr}
          | EC_eq eq ->
            if Q.equal eq.num num then (
              () (* do nothing *)
            ) else (
              (* conflict *)
              raise_conflict acts ~sign:true
                ~pivot:t ~expr_up_bound:expr ~expr_low_bound:eq.expr ~op:Eq0
                ~reasons:[reason; eq.reason] ()
            )
        end
      | _ -> assert false

    (* add forbidden value *)
    let add_neq acts t num ~expr ~reason : unit = match Term.decide_state_exn t with
      | State s ->
        let old_b = s.eq in
        Actions.on_backtrack acts (fun () -> s.eq <- old_b);
        begin match s.eq with
          | EC_none ->
            s.eq <- EC_neq {l=[num,expr,reason]};
            check_tight_bound acts t;
          | EC_neq neq ->
            (* just add constraint, if not redundant *)
            if not (List.exists (fun (n,_,_) -> Q.equal n num) neq.l) then (
              s.eq <- EC_neq {l=(num,expr,reason) :: neq.l};
              check_tight_bound acts t;
            )
          | EC_eq eq ->
            (* check if compatible *)
            if Q.equal eq.num num then (
              (* conflict *)
              raise_conflict acts
                ~pivot:t ~sign:false ~op:Eq0
                ~expr_up_bound:expr ~expr_low_bound:eq.expr
                ~reasons:[eq.reason;reason] ()
            )
        end
      | _ -> assert false

    (* add a unit constraint to [t]. The constraint is [reason],
       which is valued to [b] *)
    let add_unit_constr acts op expr (t:term) ~(reason:atom) (b:bool) : unit =
      assert (t != Atom.term reason);
      let constr, expr, num = constr_of_unit op expr t b in
      (* look into existing constraints *)
      Log.debugf 10
        (fun k->k"(@[<hv>lra.add_unit_constr@ :term %a@ :constr @[%a %a@] \
                  @ :reason %a@ :expr %a@ :cur-state %a@])"
            Term.debug t pp_constr constr Q.pp_print num Atom.debug reason
            LE.pp expr pp_state (Term.decide_state_exn t));
      (* update, depending on the kind of constraint [reason] is *)
      begin match constr with
        | C_leq -> add_up acts ~strict:false t num ~expr ~reason:(Atom reason)
        | C_lt -> add_up acts ~strict:true t num ~expr ~reason:(Atom reason)
        | C_geq -> add_low acts ~strict:false t num ~expr ~reason:(Atom reason)
        | C_gt -> add_low acts ~strict:true t num ~expr ~reason:(Atom reason)
        | C_eq -> add_eq acts t num ~expr ~reason
        | C_neq -> add_neq acts t num ~expr ~reason
      end

    (* [t] should evaluate or propagate. Add constraint to its state or
            propagate *)
    let check_consistent _acts (t:term) : unit = match Term.view t with
      | Const _ -> ()
      | Pred _ ->
        (* check consistency *)
        begin match eval t, Term.value t with
          | Eval_into (V_true,_), Some V_true
          | Eval_into (V_false,_), Some V_false -> ()
          | Eval_into (V_false,subs), Some V_true
          | Eval_into (V_true,subs), Some V_false ->
            Util.errorf "inconsistency in lra: %a@ :subs (@[%a@])"
              Term.debug t (Util.pp_list Term.debug) subs
          | Eval_unknown, _ ->
            Util.errorf "inconsistency in lra: %a@ does-not-eval"
              Term.debug t
          | Eval_into _, _ -> assert false (* non boolean! *)
        end
      | _ -> assert false

    (* [u] is [t] or one of its subterms. All the other watches are up-to-date,
       so we can add a constraint or even propagate [t] *)
    let check_or_propagate acts (t:term) ~(u:term) : unit = match Term.view t with
      | Const _ -> ()
      | Pred p ->
        begin match Term.value t with
          | None ->
            (* term not assigned, means all subterms are. We can evaluate *)
            assert (t == u);
            assert (LE.terms p.expr |> Sequence.for_all Term.has_some_value);
            begin match eval_le p.expr with
              | None -> assert false
              | Some (n,subs) ->
                let v = eval_bool_const p.op n in
                Actions.propagate_bool_eval acts t v ~subs
            end
          | Some V_true ->
            assert (t != u);
            add_unit_constr acts p.op p.expr u ~reason:(Term.Bool.pa t) true
          | Some V_false ->
            assert (t != u);
            add_unit_constr acts p.op p.expr u ~reason:(Term.Bool.na t) false
          | Some _ -> assert false
        end
      | ReLU r ->
        begin match Term.value t with
          | None -> Util.errorf "All the ReLU are supposed true"
          | Some V_true ->
            assert (t != u);
            let x = LE.singleton_term r.x and y = LE.singleton_term r.y in
            if (y == u) then
              (* propagate y from x *)
              let vx = eval_le_num_exn r.x in
              if vx <= Q.zero then
                add_up acts ~strict:false y Q.zero ~expr:LE.zero ~reason:(ReLU_prop_apply_3)
              else
                add_up acts ~strict:false y vx ~expr:r.x ~reason:(ReLU_prop_apply_3)
            else
              (* propagate x from y *)
              let vy = eval_le_num_exn r.y in
              assert (vy >= Q.zero);
              if vy > Q.zero then add_low acts ~strict:false x vy ~expr:r.y ~reason:(ReLU_prop_apply_4_or_5)
          (* let add_up acts ~strict t num ~expr ~reason *)
          | Some V_false -> Util.errorf "All the ReLU are supposed true"
          | _ -> assert false
        end

      | _ -> assert false

    let init acts t : unit = match Term.view t with
      | Const _ -> ()
      | Pred p ->
        let watches = Term.Watch2.make (t :: LE.terms_l p.expr) in
        p.watches <- watches;
        Term.Watch2.init p.watches t
          ~on_unit:(fun u -> check_or_propagate acts t ~u)
          ~on_all_set:(fun () -> check_consistent acts t)
      | ReLU r ->

        (* 0 ≤ y *)
        let ineq = mk_pred Leq0 (LE.neg r.y) in
        let c = Clause.make [Term.Bool.na t; Term.Bool.pa ineq] (Lemma lemma_lra)
        in Actions.push_clause acts c;

        (* x ≤ y *)
        let ineq = mk_pred Leq0 (LE.diff r.x r.y) in
        let c = Clause.make [Term.Bool.na t; Term.Bool.pa ineq] (Lemma lemma_lra)
        in Actions.push_clause acts c;

        (* watches = [t ; x ; y] *)
        let watches = Term.Watch2.make (t :: LE.terms_l r.x @ LE.terms_l r.y) in
        r.watches <- watches;
        Term.Watch2.init r.watches t
          ~on_unit:(fun u -> check_or_propagate acts t ~u)
          ~on_all_set:(fun () -> ())
      (* ~on_unit:(fun u -> propagate_relu acts t ~u) *)
      (* ~on_all_set:(fun () -> check_consistent acts t) *)
      | _ -> assert false

    let update_watches acts t ~watch : watch_res = match Term.view t with
      | Pred p ->
        Term.Watch2.update p.watches t ~watch
          ~on_unit:(fun u -> check_or_propagate acts t ~u)
          ~on_all_set:(fun () -> check_consistent acts t)
      | ReLU p ->
        Term.Watch2.update p.watches t ~watch
          ~on_unit:(fun u -> check_or_propagate acts t ~u)
          ~on_all_set:(fun () -> ())
      (* ~on_unit:(fun u -> propagate_relu acts t ~u) *)
      (* ~on_all_set:(fun () -> check_consistent acts t) *)
      | Const _ -> assert false
      | _ -> assert false

    let mk_eq t u = mk_pred Eq0 (LE.singleton1 t -.. LE.singleton1 u)

    (* can [t] be equal to [v] consistently with unit constraints? *)
    let can_be_eq (t:term) (n:num) : bool = match Term.decide_state_exn t with
      | State r ->
        begin match r.eq with
          | EC_none -> true
          | EC_eq {num;_} -> Q.equal num n
          | EC_neq {l} ->
            List.for_all (fun (num,_,_) -> not (Q.equal num n)) l
        end
        &&
        begin match r.low with
          | B_none -> true
          | B_some {num;strict;_} ->
            (strict && Q.compare num n < 0) ||
            (not strict && Q.compare num n <= 0)
        end
        &&
        begin match r.up with
          | B_none -> true
          | B_some {num;strict;_} ->
            (strict && Q.compare num n > 0) ||
            (not strict && Q.compare num n >= 0)
        end
      | _ -> assert false

    (* find a feasible value for [t] *)
    let find_val (t:term) : num =
      let sufficiently_large ~n forbid =
        List.fold_left Q.max n forbid |> Q.add Q.one
      and sufficiently_small ~n forbid =
        List.fold_left Q.min n forbid |> Q.add Q.minus_one
      in
      (* find an element of [)a,b(] that doesn't belong in [forbid] *)
      let rec find_between a b forbid =
        (* (a+b)/2 *)
        let mid = Q.div_2exp (Q.add a b) 1 in
        if CCList.mem ~eq:Q.equal mid forbid
        then find_between a mid forbid
        else mid
      in
      begin match Term.decide_state_exn t with
        | State r ->
          begin match r.eq with
            | EC_eq {num;_} -> num
            | _ ->
              let forbid = match r.eq with
                | EC_eq _ -> assert false
                | EC_neq {l;_} -> List.map (fun (n,_,_) -> n) l
                | EC_none -> []
              in
              begin match r.low, r.up with
                | B_none, B_none -> sufficiently_large ~n:Q.zero forbid
                | B_some {num;_}, B_none -> sufficiently_large ~n:num forbid
                | B_none, B_some {num;_} -> sufficiently_small ~n:num forbid
                | B_some low, B_some up when Q.equal low.num up.num ->
                  (* tight bounds, [n ≤ t ≤ n] *)
                  assert (not low.strict && not up.strict);
                  assert (not (CCList.mem ~eq:Q.equal low.num forbid));
                  low.num
                | B_some low, B_some up ->
                  assert (Q.compare low.num up.num < 0);
                  find_between low.num up.num forbid
              end
          end
        | _ -> assert false
      end

    (* decision, according to current constraints *)
    let decide _ (t:term) : value = match t.t_var with
      | Var_semantic {v_decide_state=State r as st; _} ->
        let n =
          if can_be_eq t r.last_val then r.last_val
          else find_val t
        in
        Log.debugf 30
          (fun k->k"(@[<hv>lra.decide@ %a := %a@ :state %a@])"
              Term.debug t Q.pp_print n pp_state st);
        assert (can_be_eq t n);
        r.last_val <- n; (* save *)
        mk_val n
      | _ -> assert false

    let () =
      Term.TC.lazy_complete tc_t
        ~init ~update_watches ~subterms ~eval ~pp:pp_term;
      Type.TC.lazy_complete tc_ty
        ~pp:pp_ty ~decide ~eq:mk_eq ~mk_state;
      ()

    let provided_services = [
      Service.Any (k_rat, Lazy.force ty_rat);
      Service.Any (k_make_const, mk_const);
      Service.Any (k_make_pred, mk_pred);
      Service.Any (k_make_relu, mk_relu);
    ]
  end in
  (module P)

let plugin : Plugin.Factory.t =
  Plugin.Factory.make ~priority:12 ~name ~build
    ~requires:Plugin.(K_cons (Builtins.k_true, K_cons (Builtins.k_false,K_nil)))
    ()
