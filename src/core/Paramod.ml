
open Solver_types

type trace = paramod_trace
type step = paramod_step
type pclause = paramod_clause

let debug_pclause out (c:pclause) : unit =
  Fmt.fprintf out "(@[<hv>@[%a@ := %a@]@ :guard %a@ :premise %a@])"
    Term.debug c.pc_lhs Term.debug c.pc_rhs
    (Util.pp_list Atom.debug) c.pc_guard
    Premise.pp c.pc_premise

let rec pp_trace out (pt:trace) : unit =
  Fmt.fprintf out "(@[<hv>param@ @[<2>%a@ := %a@]@ :steps (@[<hv>%a@])@]"
    Term.debug pt.pt_lhs
    Term.debug pt.pt_rhs
    (Util.pp_list pp_step) pt.pt_steps

and pp_step out (s:step): unit = match s with
  | PS_paramod {pc} ->
    Fmt.fprintf out "(@[param_with@ %a@])" debug_pclause pc
  | PS_sub {subs} ->
    Fmt.fprintf out "(@[<v>param_sub@ %a@])" (Util.pp_list pp_trace) subs

module Step = struct
  type t = step
  let pp = pp_step

  let paramod (pc:pclause) : t = PS_paramod {pc}
  let subs l : t = PS_sub {subs=l}
end

let[@inline] pclause_to_clause (c:pclause) : clause = Lazy.force c.pc_clause

module Trace = struct
  type t = trace
  let pp = pp_trace

  let[@inline] equal a b : bool = a.pt_id = b.pt_id
  let[@inline] compare a b : int = CCInt.compare a.pt_id b.pt_id
  let[@inline] hash a = CCHash.int a.pt_id

  let[@inline] lhs t = t.pt_lhs
  let[@inline] rhs t = t.pt_rhs
  let[@inline] steps t = t.pt_steps

  module As_key = struct
    type t = trace
    let equal = equal
    let hash = hash
  end
  module Tbl = CCHashtbl.Make(As_key)

  (* generative function *)
  let make =
    let n = ref 0 in
    fun pt_lhs pt_rhs pt_steps : t ->
      let pt_id = CCRef.incr_then_get n in
      { pt_lhs; pt_rhs; pt_steps; pt_id }

  (* iterate on clauses, as a DAG *)
  let pc_seq (t:trace) (yield: pclause->unit) : unit =
    let tbl = Tbl.create 16 in
    let rec aux_trace t =
      if not (Tbl.mem tbl t) then (
        Tbl.add tbl t ();
        List.iter aux_step t.pt_steps
      )
    and aux_step = function
      | PS_sub {subs} -> List.iter aux_trace subs
      | PS_paramod {pc} -> yield pc
    in
    aux_trace t

  let clauses (t:t) =
    pc_seq t
    |> Sequence.map pclause_to_clause
    |> Clause.Set.of_seq
end

module PClause = struct
  type t = pclause

  let to_clause_real lhs rhs guard premise : clause =
    let atoms = Term.Bool.mk_eq lhs rhs :: List.map Atom.neg guard in
    Clause.make atoms premise

  let[@inline] make pc_lhs pc_rhs pc_guard pc_premise : t =
    { pc_guard; pc_lhs; pc_rhs; pc_premise;
      pc_clause=lazy (to_clause_real pc_lhs pc_rhs pc_guard pc_premise);
    }

  let[@inline] lhs c = c.pc_lhs
  let[@inline] rhs c = c.pc_rhs
  let[@inline] guard c = c.pc_guard
  let[@inline] premise c = c.pc_premise

  let[@inline] to_clause (c:t) : clause = Lazy.force c.pc_clause

  let pp out (c:t) : unit =
    Fmt.fprintf out "(@[<hv>@[%a@ := %a@]@ <= %a@])"
      Term.pp (lhs c) Term.pp (rhs c) (Util.pp_list Atom.pp) (guard c)

  let debug = debug_pclause
end
