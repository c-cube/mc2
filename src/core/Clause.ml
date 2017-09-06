
open Solver_types

module Fields = Solver_types.Clause_fields

type t = clause

let field_attached = Fields.mk_field() (** Is the clause attached, i.e. does it watch literals. *)
let field_visited = Fields.mk_field() (** Used during propagation and proof generation. *)

let dummy : t = dummy_clause

(* Name generation *)
let fresh_name =
  let n = ref 0 in
  fun () -> incr n; !n

let[@inline] make_arr ?tag c_atoms c_premise : t=
  let c_name = fresh_name() in
  { c_name;
    c_tag = tag;
    c_atoms = c_atoms;
    c_fields = Fields.empty;
    c_activity = 0.;
    c_premise = c_premise;
  }

let make ?tag ali c_premise : t=
  let c_atoms = Array.of_list ali in
  make_arr ?tag c_atoms c_premise

let empty : t = make [] (History [])

let[@inline] visited c = Fields.get field_visited c.c_fields
let[@inline] mark_visited c = c.c_fields <- Fields.set field_visited true c.c_fields
let[@inline] clear_visited c = c.c_fields <- Fields.set field_visited false c.c_fields

let[@inline] attached c = Fields.get field_attached c.c_fields
let[@inline] set_attached c = c.c_fields <- Fields.set field_attached true c.c_fields

let[@inline] get_tag c = c.c_tag
let[@inline] name c = c.c_name
let[@inline] premise c = c.c_premise
let[@inline] activity c = c.c_activity
let[@inline] atoms c = c.c_atoms
let[@inline] gc_mark c = Array.iter (fun a -> Term.gc_mark a.a_term) c.c_atoms

let pp_atoms out v =
  if Array.length v = 0 then
    Format.fprintf out "∅"
  else
    Util.pp_array ~sep:" ∨ " Atom.pp out v

let[@inline] pp_name out c =
  Format.fprintf out "%s%d" (Premise.prefix c.c_premise) c.c_name

let pp out c =
  Format.fprintf out "(@[<hv>%a: %a@])" pp_name c pp_atoms c.c_atoms

let pp_atoms out = Format.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∨ " Atom.pp)
let debug_atoms out = Format.fprintf out "(@[%a@])" (Util.pp_list ~sep:" ∨ " Atom.debug)

let debug out ({c_atoms; c_premise=cp; _} as c) =
  let pp_atoms_vec out = Util.pp_array ~sep:" ∨ " Atom.debug out in
  Format.fprintf out "%a@[<hov>{@[<hv>%a@]}@ cpremise={@[<hov>%a@]}@]"
    pp_name c pp_atoms_vec c_atoms Premise.pp cp

let pp_dimacs fmt { c_atoms; _} =
  let aux fmt a =
    Array.iter
      (fun p ->
         Format.fprintf fmt "%s%d "
           (if Atom.is_pos p then "" else "-")
           (p.a_term.t_id+1))
      a
  in
  Format.fprintf fmt "%a0" aux c_atoms
