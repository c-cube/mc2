
open Solver_types

module Fields = Solver_types.Clause_fields

type t = clause

(** Is the clause attached, i.e. does it watch literals. *)
let field_attached = Fields.mk_field()

(** Used during propagation and proof generation. *)
let field_visited = Fields.mk_field()

let dummy : t =
  { c_name = "";
    c_tag = None;
    c_atoms = [| |];
    c_activity = -1.;
    c_fields=Fields.empty;
    c_premise = History [];
  }

let[@inline] make_arr ?tag c_name c_atoms c_premise : t=
  { c_name;
    c_tag = tag;
    c_atoms = c_atoms;
    c_fields = Fields.empty;
    c_activity = 0.;
    c_premise = c_premise;
  }

let make ?tag c_name ali c_premise : t=
  let c_atoms = Array.of_list ali in
  make_arr ?tag c_name c_atoms c_premise

let empty : t = make "⊥" [] (History [])

let visited c = Fields.get field_visited c.c_fields
let mark_visited c = c.c_fields <- Fields.set field_visited true c.c_fields
let clear_visited c = c.c_fields <- Fields.set field_visited false c.c_fields

(* Name generation *)
let fresh_lname =
  let cpt = ref 0 in
  fun () -> incr cpt; "L" ^ (string_of_int !cpt)

let fresh_hname =
  let cpt = ref 0 in
  fun () -> incr cpt; "H" ^ (string_of_int !cpt)

let fresh_tname =
  let cpt = ref 0 in
  fun () -> incr cpt; "T" ^ (string_of_int !cpt)

let fresh_name =
  let cpt = ref 0 in
  fun () -> incr cpt; "C" ^ (string_of_int !cpt)


let pp_atoms out v =
  if Array.length v = 0 then
    Format.fprintf out "∅"
  else (
    Atom.pp out v.(0);
    if (Array.length v) > 1 then (
      for i = 1 to (Array.length v) - 1 do
        Format.fprintf out " ∨ %a" Atom.pp v.(i)
      done
    )
  )

let print_clause fmt c =
  Format.fprintf fmt "%s : %a" c.c_name pp_atoms c.c_atoms

let pp_atoms_vec out vec = Util.pp_array ~sep:" " Atom.pp out vec

let pp out {c_name; c_atoms; c_premise=cp; _} =
  Format.fprintf out "%s@[<hov>{@[<hov>%a@]}@ cpremise={@[<hov>%a@]}@]"
    c_name pp_atoms_vec c_atoms Premise.pp cp

let pp_dimacs fmt { c_atoms; _} =
  let aux fmt a =
    Array.iter (fun p ->
      Format.fprintf fmt "%s%d "
        (* FIXME: use [Term.as_bvar_exn] here *)
        (if p == p.a_term.pa then "-" else "")
        (p.a_term.t_id+1))
      a
  in
  Format.fprintf fmt "%a0" aux c_atoms

