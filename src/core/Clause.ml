
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
let get_tag c = c.c_tag

(* Name generation *)
let fresh_name_gen prefix =
  let cpt = ref 0 in
  fun () -> incr cpt; prefix ^ (string_of_int !cpt)

let fresh_lname = fresh_name_gen "L"
let fresh_hname = fresh_name_gen "G"
let fresh_tname = fresh_name_gen "T"
let fresh_name = fresh_name_gen "C"

let pp_atoms pp_t out v =
  if Array.length v = 0 then
    Format.fprintf out "∅"
  else (
    Atom.pp pp_t out v.(0);
    if (Array.length v) > 1 then (
      for i = 1 to (Array.length v) - 1 do
        Format.fprintf out " ∨ %a" (Atom.pp pp_t) v.(i)
      done
    )
  )

let debug pp_t out c =
  Format.fprintf out "%s : %a" c.c_name (pp_atoms pp_t) c.c_atoms

let pp_atoms_vec pp_t out vec = Util.pp_array ~sep:" " (Atom.pp pp_t) out vec

let pp pp_t out {c_name; c_atoms; c_premise=cp; _} =
  Format.fprintf out "%s@[<hov>{@[<hov>%a@]}@ cpremise={@[<hov>%a@]}@]"
    c_name (pp_atoms_vec pp_t) c_atoms Premise.pp cp

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
