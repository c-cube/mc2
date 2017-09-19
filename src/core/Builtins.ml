
open Solver_types
module Fmt = CCFormat

let name = "builtins"
let k_true = Service.Key.makef "%s.true" name
let k_false = Service.Key.makef "%s.false" name

type term_view += True | False

type lemma_view += L_tautology

let[@inline] is_builtin (t:term) = match Term.view t with
  | True | False -> true
  | _ -> false

let tcl =
  let tcl_pp out = function
    | L_tautology -> Fmt.string out "true_is_true"
    | _ -> assert false
  in
  {tcl_pp}

let lemma_trivial : lemma = Lemma.make L_tautology tcl

let build p_id Plugin.S_nil : Plugin.t =
  let module P = struct
    let id = p_id
    let name = name

    let pp out = function
      | True -> Fmt.string out "true"
      | False -> Fmt.string out "false"
      | _ -> assert false

    (* on initialization, add clause [true] *)
    let init acts t = match Term.view t with
      | True ->
        let c_true = Clause.make [Term.Bool.pa t] (Lemma lemma_trivial) in
        Actions.push_clause acts c_true
      | False ->
        let c = Clause.make [Term.Bool.na t] (Lemma lemma_trivial) in
        Actions.push_clause acts c
      | _ -> assert false

    let[@inline] eval_bool (t:term) : eval_bool_res =
      begin match Term.view t with
        | True -> Eval_bool (true,[])
        | False -> Eval_bool (false,[])
        | _ -> assert false
      end

    let tc : tc_term = Term.tc_mk ~eval_bool ~init ~pp ()

    (* the main "true" term *)
    let t_true : term = Term.Unsafe.make_term p_id True Type.bool tc

    let t_false : term = Term.Unsafe.make_term p_id False Type.bool tc

    let iter_terms yield = yield t_true
    let gc_all () = 0
    let check_if_sat _ = Sat

    let provided_services = [
      Service.Any (k_true, t_true);
      Service.Any (k_false, t_false);
    ]
  end in
  (module P)

let plugin =
  Plugin.Factory.make ~priority:0 ~name ~requires:Plugin.K_nil ~build ()

