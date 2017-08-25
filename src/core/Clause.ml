
open Solver_types

type t = clause

let dummy : t =
  { name = "";
    tag = None;
    atoms = [| |];
    activity = -1.;
    attached = false;
    visited = false;
    cpremise = History [] }

let make ?tag name ali premise : t=
  let atoms = Array.of_list ali in
  { name  = name;
    tag = tag;
    atoms = atoms;
    attached = false;
    visited = false;
    activity = 0.;
    cpremise = premise}

let empty : t = make "⊥" [] (History [])

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


let print_atoms fmt v =
  if Array.length v = 0 then
    Format.fprintf fmt "∅"
  else begin
    print_atom fmt v.(0);
    if (Array.length v) > 1 then begin
      for i = 1 to (Array.length v) - 1 do
        Format.fprintf fmt " ∨ %a" print_atom v.(i)
      done
    end
  end

let print_clause fmt c =
  Format.fprintf fmt "%s : %a" c.name print_atoms c.atoms

let pp_atoms_vec out vec =
  Array.iter (fun a -> Format.fprintf out "%a@ " pp_atom a) vec

let pp_clause out {name=name; atoms=arr; cpremise=cp; _} =
  Format.fprintf out "%s@[<hov>{@[<hov>%a@]}@ cpremise={@[<hov>%a@]}@]"
    name pp_atoms_vec arr pp_premise cp

let pp_dimacs fmt { atoms; _} =
  let aux fmt a =
    Array.iter (fun p ->
      Format.fprintf fmt "%s%d "
        (if p == p.var.pa then "-" else "")
        (p.var.vid+1)
    ) a
  in
  Format.fprintf fmt "%a0" aux atoms

