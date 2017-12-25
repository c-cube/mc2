
(** {1 Linear Rational Arithmetic} *)

(* Reference:
   http://smtlib.cs.uiowa.edu/logics-all.shtml#QF_LRA *)

(* TODO:
   define relu with terms instead of LE.t
   might be possible to test the atomic LE.t AND
   retrieve the terms in mk_relu
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

type bound =
  | B_some of {strict:bool; num: num; expr: LE.t; reasons:atom list}
  | B_none (* no bound *)

type eq_cstr =
  | EC_eq of {num:num; reasons:atom list; expr: LE.t}
  | EC_neq of {l: (num * LE.t * (atom list)) list} (* forbidden values *)
  | EC_none

(* state for a single Q-sorted variable *)
type decide_state +=
  | State of {
      mutable last_val: num; (* phase saving *)
      mutable last_decision_lvl: level;
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
  (* maybe use Watch2 to have an update function that can further propagate *)

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


let lmax list = 
  List.fold_left  
    (fun max x -> Pervasives.max max (Some x))
    None
    list

let term_decision_lvl (t:term) = 
  match Term.decide_state_exn t with
  | State s -> s.last_decision_lvl
  | _ -> assert false

(* maximum decision level of a linexp *)
let last_decision_lvl (e:LE.t) : level =
  let lmax l = 
    List.fold_left (fun max x -> Pervasives.max max x) (-1) l
  in
  List.map term_decision_lvl @@ LE.terms_l e |> lmax


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
    last_decision_lvl= -1;
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
  | B_some {strict;num;reasons;expr} ->
    let strict_str = if strict then "[strict]" else "" in
    Fmt.fprintf out "(@[%a%s@ :expr %a@ :reasons %a@])"
      Q.pp_print num strict_str LE.pp expr (Util.pp_list Atom.debug) reasons

let pp_eq out = function
  | EC_none -> Fmt.string out "ø"
  | EC_eq {num;reasons;expr} ->
    Fmt.fprintf out "(@[= %a@ :expr %a@ :reasons %a@])"
      Q.pp_print num LE.pp expr (Util.pp_list Atom.debug) reasons
  | EC_neq {l} ->
    let pp_tuple out (n,e,a) =
      Fmt.fprintf out "(@[%a@ :expr %a@ :reasons %a@])"
        Q.pp_print n LE.pp e (Util.pp_list Atom.debug) a
    in
    Fmt.fprintf out "(@[<hv>!=@ %a@])"
      (Util.pp_list pp_tuple) l

let pp_state out = function
  | State s ->
    Fmt.fprintf out "(@[<hv>:low %a@ :up %a@ :eq %a@ :last_val %a@ :last_decision_lvl %d@])"
      pp_bound s.low pp_bound s.up pp_eq s.eq Q.pp_print s.last_val s.last_decision_lvl
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
        Log.debugf 30
          (fun k->k "eval relu %a, %a" Q.pp_print ny Q.pp_print @@ eval_relu nx);
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

    let simplify (e:LE.t) : LE.t =
      (* simplify: if e is [n·x op 0], then rewrite into [sign(n)·x op 0] *)
      match LE.as_singleton e with
      | None -> e
      | Some (n,t) ->
        let n = if Q.sign n >= 0 then Q.one else Q.minus_one in
        LE.singleton n t

    (* build a predicate on a linear expression *)
    let mk_pred (op:op) (e:LE.t) : term =
      begin match LE.as_const e with
        | Some n ->
          (* directly evaluate *)
          if eval_bool_const op n then true_ else false_
        | None ->
          let e = simplify e
          in
          let view = Pred {op; expr=e; watches=Term.Watch2.dummy} in
          T.make view Type.bool
      end

    let mk_const (n:num) : term = T.make (Const n) (Lazy.force ty_rat)

    let mk_relu (x:LE.t) (y:LE.t): term =
      (* TODO: ensure they are equal to singletons *)
      begin match LE.as_const x with
        | Some nx ->
          let ans = eval_relu nx
          in mk_pred Eq0 (LE.diff y @@ LE.const ans)
        | None ->
          begin match LE.as_const y with
            | Some ny ->
              if ny > Q.zero
              then mk_pred Eq0 (LE.diff x @@ LE.const ny)
              else mk_pred Lt0 x
            | None ->
              let x = simplify x and y = simplify y
              in
              let view = ReLU {x=x; y=y; watches=Term.Watch2.dummy} in
              Log.debugf 1
                (fun k->k "mk_relu %a" pp_term view);
              T.make view Type.bool
          end
      end           


    (* raise a conflict that deduces [expr_up_bound - expr_low_bound op 0] (which must
       eval to [false]) from [reasons] *)
    let raise_conflict acts
        ~sign ~op ~pivot ~expr_up_bound ~expr_low_bound ~(reasons:atom list) () : 'a =
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
            let reasons_neq : atom list =
              CCList.find_map
                (fun (n,_,r) -> if Q.equal low.num n then Some r else None)
                l |> CCOpt.get_exn
            in
            (* conflict should be:
               [low <= t & t <= up & low=up => t = neq]. *)
            let reasons : atom list = reasons_neq @ up.reasons@low.reasons in
            raise_conflict acts
              ~sign:false ~op:Eq0 ~pivot:t
              ~expr_up_bound:up.expr ~expr_low_bound:low.expr
              ~reasons:reasons ()
          | _ -> ()
        end
      | _ -> assert false

    (* add upper bound *)
    let add_up acts ~strict t num ~expr ~reasons : unit = match Term.decide_state_exn t with
      | State s ->
        (* check consistency *)
        begin match s.eq, s.low with
          | EC_eq eq, _ when
              (strict && Q.compare eq.num num >= 0) ||
              (not strict && Q.compare eq.num num > 0) ->
            raise_conflict acts
              ~sign:true ~op:(if strict then Lt0 else Leq0) ~pivot:t
              ~expr_up_bound:expr ~expr_low_bound:eq.expr ~reasons:(eq.reasons @ reasons) ()
          | _, B_some b when
              ((strict || b.strict) && Q.compare b.num num >= 0) ||
              (Q.compare b.num num > 0) ->
            raise_conflict acts
              ~sign:true ~op:(if strict || b.strict then Lt0 else Leq0) ~pivot:t
              ~expr_up_bound:expr ~expr_low_bound:b.expr ~reasons:(b.reasons @ reasons) ()
          | _ -> ()
        end;
        (* update *)
        let old_b = s.up in
        Actions.on_backtrack acts (fun () -> s.up <- old_b);
        begin match s.up with
          | B_none ->
            s.up <- B_some {strict;num;reasons;expr};
            check_tight_bound acts t;
          | B_some b ->
            (* only replace if more tight *)
            if Q.compare b.num num > 0 ||
               (strict && not b.strict && Q.equal b.num num) then (
              s.up <- B_some {strict;num;reasons;expr};
              check_tight_bound acts t;
            )
        end;
      | _ -> assert false

    (* add lower bound *)
    let add_low acts ~strict t num ~expr ~reasons : unit = match Term.decide_state_exn t with
      | State s ->
        (* check consistency *)
        begin match s.eq, s.up with
          | EC_eq eq, _ when
              (strict && Q.compare eq.num num <= 0) ||
              (not strict && Q.compare eq.num num < 0) ->
            raise_conflict acts
              ~sign:true ~op:(if strict then Lt0 else Leq0) ~pivot:t
              ~expr_low_bound:expr ~expr_up_bound:eq.expr ~reasons:(eq.reasons @ reasons) ()
          | _, B_some b when
              ((strict || b.strict) && Q.compare b.num num <= 0) ||
              (Q.compare b.num num < 0) ->
            raise_conflict acts
              ~sign:true ~op:(if strict || b.strict then Lt0 else Leq0) ~pivot:t
              ~expr_low_bound:expr ~expr_up_bound:b.expr ~reasons:(b.reasons @ reasons) ()
          | _ -> ()
        end;
        (* update state *)
        let old_b = s.low in
        Actions.on_backtrack acts (fun () -> s.low <- old_b);
        begin match s.low with
          | B_none ->
            s.low <- B_some {strict;num;reasons;expr};
            check_tight_bound acts t;
          | B_some b ->
            (* only replace if more tight *)
            if Q.compare b.num num < 0 ||
               (strict && not b.strict && Q.equal b.num num) then (
              s.low <- B_some {strict;num;reasons;expr};
              check_tight_bound acts t;
            )
        end
      | _ -> assert false

    (* add exact bound *)
    let add_eq acts t num ~expr ~reasons : unit = match Term.decide_state_exn t with
      | State s ->
        (* check compatibility with bounds *)
        begin match s.low, s.up with
          | B_some b, _ when
              (b.strict && Q.compare b.num num >= 0) ||
              (not b.strict && Q.compare b.num num > 0) ->
            raise_conflict acts ~op:(if b.strict then Lt0 else Leq0)
              ~sign:true ~pivot:t ~expr_up_bound:expr ~expr_low_bound:b.expr
              ~reasons:(b.reasons @ reasons) ()
          | _, B_some b when
              (b.strict && Q.compare b.num num <= 0) ||
              (not b.strict && Q.compare b.num num < 0) ->
            raise_conflict acts ~op:(if b.strict then Lt0 else Leq0)
              ~sign:true ~pivot:t ~expr_low_bound:expr ~expr_up_bound:b.expr
              ~reasons:(b.reasons @ reasons) ()
          | _ -> ()
        end;
        (* check other equality constraints, and update *)
        let old_b = s.eq in
        Actions.on_backtrack acts (fun () -> s.eq <- old_b);
        begin match s.eq with
          | EC_none -> s.eq <- EC_eq {num;reasons;expr}
          | EC_neq {l;_} ->
            (* check if compatible *)
            List.iter
              (fun (n2, expr2, reasons_neq) ->
                 if Q.equal num n2 then (
                   (* conflict *)
                   assert (not (List.mem false @@ List.map Atom.is_true reasons_neq));
                   raise_conflict acts ~pivot:t ~op:Eq0 ~sign:false
                     ~expr_up_bound:expr ~expr_low_bound:expr2 ~reasons:(reasons_neq @ reasons) ()
                 ))
              l;
            (* erase *)
            s.eq <- EC_eq {num;reasons;expr}
          | EC_eq eq ->
            if Q.equal eq.num num then (
              () (* do nothing *)
            ) else (
              (* conflict *)
              raise_conflict acts ~sign:true
                ~pivot:t ~expr_up_bound:expr ~expr_low_bound:eq.expr ~op:Eq0
                ~reasons:(eq.reasons @ reasons) ()
            )
        end
      | _ -> assert false

    (* add forbidden value *)
    let add_neq acts t num ~expr ~reasons : unit = match Term.decide_state_exn t with
      | State s ->
        let old_b = s.eq in
        Actions.on_backtrack acts (fun () -> s.eq <- old_b);
        begin match s.eq with
          | EC_none ->
            s.eq <- EC_neq {l=[num,expr,reasons]};
            check_tight_bound acts t;
          | EC_neq neq ->
            (* just add constraint, if not redundant *)
            if not (List.exists (fun (n,_,_) -> Q.equal n num) neq.l) then (
              s.eq <- EC_neq {l=(num,expr,reasons) :: neq.l};
              check_tight_bound acts t;
            )
          | EC_eq eq ->
            (* check if compatible *)
            if Q.equal eq.num num then (
              (* conflict *)
              raise_conflict acts
                ~pivot:t ~sign:false ~op:Eq0
                ~expr_up_bound:expr ~expr_low_bound:eq.expr
                ~reasons:(eq.reasons @ reasons) ()
            )
        end
      | _ -> assert false

    (* add a unit constraint to [t]. The constraint is [reason],
       which is valued to [b] *)
    let add_unit_constr acts op expr (t:term) ~(reasons:atom list) (b:bool) : unit =
      (* assert (t != Atom.term reason); *)
      let constr, expr, num = constr_of_unit op expr t b in
      (* look into existing constraints *)
      Log.debugf 10
        (fun k->k"(@[<hv>lra.add_unit_constr@ :term %a@ :constr @[%a %a@] \
                  @ :reasons %a@ :expr %a@ :cur-state %a@])"
            Term.debug t pp_constr constr Q.pp_print num (Util.pp_list Atom.debug) reasons
            LE.pp expr pp_state (Term.decide_state_exn t));
      (* update, depending on the kind of constraint [reason] is *)
      begin match constr with
        | C_leq -> add_up acts ~strict:false t num ~expr ~reasons
        | C_lt -> add_up acts ~strict:true t num ~expr ~reasons
        | C_geq -> add_low acts ~strict:false t num ~expr ~reasons
        | C_gt -> add_low acts ~strict:true t num ~expr ~reasons
        | C_eq -> add_eq acts t num ~expr ~reasons
        | C_neq -> add_neq acts t num ~expr ~reasons
      end

    (* [t] should evaluate or propagate. Add constraint to its state or
            propagate *)
    let check_consistent acts (t:term) : unit = match Term.view t with
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
      | ReLU r ->
        Log.debugf 1
          (fun k->k "relu-check_consistent %a" pp_term (Term.view t));
        (* here we suppose
           - the relu is always true (could be checked or ensured in the input files)
           - r.x is composed solely of x, r.y solely of y (could be checked)
        *)
        let x = List.hd (LE.terms_l r.x) and y = List.hd (LE.terms_l r.y) in

        let vx = eval_le_num_exn r.x and vy = eval_le_num_exn r.y in

        Log.debugf 1
          (fun k->k "x evals to %a, y evals to %a, lvl_x=%d, lvl_y=%d"
              Q.pp_print vx Q.pp_print vy (last_decision_lvl r.x) (last_decision_lvl r.y));
        Log.debugf 1
          (fun k->k "x is %a"
              (Util.pp_list Term.debug) (LE.terms_l r.x));
        Log.debugf 1
          (fun k->k "y is %a"
              (Util.pp_list Term.debug) (LE.terms_l r.y));

        if Q.equal vy (eval_relu vx) then
          ()
        else
          begin
            Log.debugf 0
              (fun k->k "ABEHZBEHBZHEBHZBEHBHZE");
            let conflict =
              (* TODO: maybe it is possible to retrieve the level with Term.level *)
              match Term.decide_state_exn x, Term.decide_state_exn y with
              | State{last_val=x_val; last_decision_lvl=x_lvl; up=x_up; low=x_low; eq=x_eq},
                State{last_val=y_val; last_decision_lvl=y_lvl; up=y_up; low=y_low; eq=y_eq} ->
                Log.debugf 0
                  (fun k->k "y_low %a"
                      pp_bound y_low);
                Log.debugf 0
                  (fun k->k "x_up %a"
                      pp_bound x_up);
                if y_lvl > x_lvl then
                  match y_low with
                  | B_some{strict; num; expr=y_l; reasons} ->
                    let op = 
                      if strict then
                        Lt0
                      else
                        Leq0
                    in
                    [
                      Term.Bool.na (mk_pred op (y_l -.. r.y));
                      Term.Bool.pa (mk_pred op y_l);
                      Term.Bool.pa (mk_pred op (y_l -.. r.x));
                    ]
                  | B_none -> []
                else if x_lvl > y_lvl then
                  match x_up with
                  | B_some{strict; num; expr=x_u; reasons} -> 
                    let op = 
                      if strict then
                        Lt0
                      else
                        Leq0
                    in
                    [
                      Term.Bool.na (mk_pred op (r.x -.. x_u));
                      Term.Bool.na (mk_pred op (LE.neg r.x));
                      Term.Bool.pa (mk_pred op (r.y -.. x_u))
                    ]
                  | B_none -> []
                else assert false;
              | _, _ -> assert false;
            in

            Log.debugf 30
              (fun k->k
                  "(@[<hv>lra.raise_conflict.ReLU@ :clause %a@])"
                  Clause.debug_atoms conflict);
            Actions.raise_conflict acts conflict lemma_relu;
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
            add_unit_constr acts p.op p.expr u ~reasons:[Term.Bool.pa t] true
          | Some V_false ->
            assert (t != u);
            add_unit_constr acts p.op p.expr u ~reasons:[Term.Bool.na t] false
          | Some _ -> assert false
        end
      (* | ReLU r -> Log.debugf 1
          (fun k->k "test-check_or_propagate %a %a" pp_term (Term.view t) Term.debug u);
          begin match Term.value t with
            | None ->
              (* term not assigned, means all subterms are. We can evaluate *)
              assert (t == u);
              assert (LE.terms r.expr |> Sequence.for_all Term.has_some_value);
              begin match eval_le r.expr with
                | None -> assert false
                | Some (n,subs) ->
                  Log.debugf 1
                            (fun k->k "test-check_or_propagate1" );
              end
            | Some V_value {view=V_rat num;_} ->
                             assert (t != u);
                             Log.debugf 1
                             (fun k->k "test-check_or_propagate2 %a evals to %a" pp_term t.t_view Q.pp_print num);
                             | Some _ -> assert false
                             end *)
      | _ -> assert false


    let propagate_relu acts (t:term) ~(u:term) : unit =
      (* TODO: verify t is true *)
      let r = Term.view t in
      Log.debugf 1 (fun k->k "t is %a " pp_term r);
      match r with
      | ReLU r ->
        let x = List.hd (LE.terms_l r.x) and y = List.hd (LE.terms_l r.y) in
        Log.debugf 1 (fun k->k "propagate_relu %a %a" LE.pp r.x LE.pp r.y);
        Log.debugf 1 (fun k->k "propagate_relu %a %a %a %a" Term.debug t Term.debug u Term.debug x Term.debug y);

        (* HERE IS THE SOLUTION *)
        (* When adding the constraint we deduce from relu,
           if it clashes with previously known contraints, then we can deduce something
           We have to rewrite the add_eq / add_up functions that are only suitable for
           constraints derived from inequalities!!!
        *)
        if (Term.equal x u) then
          (* we want to predict x from y if y > 0 or else add a constraint on x *)
          begin
            (* TODO
            e /\ {0/x}e ) => {y/x}e
            *)
            Log.debugf 1 (fun k->k "u is x %a %a" LE.pp r.x Term.debug x);
            Log.debugf 1 (fun k->k "y is %a " Term.debug y);
            let vy = eval_le_num_exn r.y in 
            if vy > Q.zero then
              let reason = Term.Bool.pa (mk_pred Lt0 (LE.neg r.y))
              in
              add_low acts ~strict:false x vy ~expr:r.y ~reasons:[reason; Term.Bool.pa t];
              (* add_eq acts x vy ~expr:r.y ~reasons:[reason; Term.Bool.pa t];*)
            else
              let reason = Term.Bool.na (mk_pred Lt0 (LE.neg r.y))
              in
              add_up acts ~strict:false x Q.zero ~expr:LE.zero ~reasons:[reason; Term.Bool.pa t];
          end
        else if (Term.equal y u) then
          (* we want to predict y from x *)
          let vx = eval_le_num_exn r.x in 
          let vy = eval_relu vx in
          let expr_y, reason_y =
            (* vx < Q.zero works better *)
            (if vx <= Q.zero then
               LE.zero, Term.Bool.pa (mk_pred Leq0 r.x)
             else
               r.x, Term.Bool.na (mk_pred Leq0 r.x)) in
          (* here we should add the upper bound on y and test for the clash with the lower bound
             and analyse *)
          (* add_up acts ~strict:false y vy ~expr:expr_y ~reasons:[reason_y; Term.Bool.pa t]; *)
          (* add_eq acts y vy ~expr:expr_y ~reasons:[reason_y; Term.Bool.pa t]; *)
          (* add_up acts ~strict t num ~expr ~reasons *)
          begin

            Log.debugf 1 (fun k->k "u is y %a %a" LE.pp r.y LE.pp expr_y);

            match Term.decide_state_exn y with
            | State s -> 
              begin match s.eq, s.low with
                | EC_eq eq, _ (* when
                    (strict && Q.compare eq.num num >= 0) ||
                    (not strict && Q.compare eq.num num > 0)  *) ->
                  assert false
                (* TODO *)
                (* raise_conflict acts
                   ~sign:true ~op:(if strict then Lt0 else Leq0) ~pivot:t
                   ~expr_up_bound:expr ~expr_low_bound:eq.expr ~reasons:(eq.reasons @ reasons) () *)
                | _, B_some b when
                    (b.strict && Q.compare b.num vy >= 0) ||
                    (Q.compare b.num vy > 0) ->
                  let op = if b.strict then Lt0 else Leq0 in
                  let c = [
                    Term.Bool.na (mk_pred op (b.expr -.. r.y));
                    Term.Bool.pa (mk_pred op b.expr);
                    Term.Bool.pa (mk_pred op (b.expr -.. r.x));
                  ] in 
                  Log.debugf 30
                    (fun k->k
                        "(@[<hv>relu.raise_conflict@ :pivot %a@\
                         :clause %a@])"
                        Term.debug y
                        Clause.debug_atoms c);
                  Actions.raise_conflict acts c lemma_relu
                (* raise_conflict acts
                   ~sign:true ~op:(if strict || b.strict then Lt0 else Leq0) ~pivot:t
                   ~expr_up_bound:expr ~expr_low_bound:b.expr ~reasons:(b.reasons @ reasons) () *)
                (* let raise_conflict acts
                    ~sign ~op ~pivot ~expr_up_bound ~expr_low_bound ~(reasons:atom list) () : 'a =
                   let expr = LE.diff expr_low_bound expr_up_bound in
                   assert (not (LE.mem_term pivot expr));
                   let concl = mk_pred op expr in
                   let concl = if sign then Term.Bool.pa concl else Term.Bool.na concl in
                   let c = concl :: List.map Atom.neg reasons in
                   Actions.raise_conflict acts c lemma_lra *)

                | _ -> ()
              end;
              (* update *)
              let old_b = s.up in
              Actions.on_backtrack acts (fun () -> s.up <- old_b);
              begin match s.up with
                | B_none ->
                  s.up <- B_some {strict=false;num=vy;reasons=[reason_y];expr=expr_y};
                  check_tight_bound acts y;
                | B_some b ->
                  (* only replace if more tight *)
                  if Q.compare b.num vy > 0 then (
                    s.up <- B_some {strict=false;num=vy;reasons=[reason_y];expr=expr_y};
                    check_tight_bound acts y;
                  )
              end;
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
        Log.debugf 1
          (fun k->k "test-init-relu %a" pp_term (Term.view t));

        (* 0 ≤ y *)
        let c = Clause.make [Term.Bool.pa (mk_pred Leq0 (LE.mult Q.minus_one r.y))] (Lemma lemma_lra)
        in Actions.push_clause acts c;

        (* x ≤ y *)
        let c = Clause.make [Term.Bool.pa (mk_pred Leq0 (LE.diff r.x r.y))] (Lemma lemma_lra)
        in Actions.push_clause acts c;          

        (* Normally watches = [t ; x ; y] *)
        let watches = Term.Watch2.make (t :: LE.terms_l r.x @ LE.terms_l r.y) in
        r.watches <- watches;
        Term.Watch2.init r.watches t
          ~on_unit:(fun u -> propagate_relu acts t ~u)
          ~on_all_set:(fun () -> check_consistent acts t)
      | _ -> assert false

    let update_watches acts t ~watch : watch_res = match Term.view t with
      | Pred p ->
        Term.Watch2.update p.watches t ~watch
          ~on_unit:(fun u -> check_or_propagate acts t ~u)
          ~on_all_set:(fun () -> check_consistent acts t)
      | ReLU p ->
        Term.Watch2.update p.watches t ~watch
          ~on_unit:(fun u -> propagate_relu acts t ~u)
          ~on_all_set:(fun () -> check_consistent acts t)
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
    let decide acts (t:term) : value = match t.t_var with
      | Var_semantic {v_decide_state=State r as st; _} ->
        let n =
          if can_be_eq t r.last_val then r.last_val
          else find_val t
        in
        Log.debugf 30
          (fun k->k"(@[<hv>lra.decide@ %a := %a@ :state %a@ :lvl %d@])"
              Term.debug t Q.pp_print n pp_state st (Actions.level acts));
        assert (can_be_eq t n);
        r.last_val <- n; (* save *)
        r.last_decision_lvl <- Actions.level acts;
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
