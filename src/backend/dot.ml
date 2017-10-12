(*
MSAT is free software, using the Apache license, see file LICENSE
Copyright 2014 Guillaume Bury
Copyright 2014 Simon Cruanes
*)

open Mc2_core
open Solver_types

(** Output interface for the backend *)
module type S = Backend_intf.S

(** Input module for the backend *)
module type Arg = sig

  type atom
  (* Type of atoms *)

  type hyp
  type lemma
  type assumption
  (** Types for hypotheses, lemmas, and assumptions. *)

  val print_atom : Format.formatter -> atom -> unit
  (** Printing function for atoms *)

  val hyp_info : hyp -> string * string option * (Format.formatter -> unit -> unit) list
  val lemma_info : lemma -> string * string option * (Format.formatter -> unit -> unit) list
  val assumption_info : assumption -> string * string option * (Format.formatter -> unit -> unit) list
  (** Functions to return information about hypotheses and lemmas *)

end

module Default = struct

  let print_atom out a = Fmt.fprintf out "@[<h>%a@]" Atom.pp a

  let hyp_info c =
    "hypothesis", Some "LIGHTBLUE",
    [ fun fmt () -> Clause.pp_name fmt c ]

  let lemma_info c =
    "lemma", Some "BLUE",
    [ fun fmt () -> Clause.pp_name fmt c ]

  let assumption_info c =
    "assumption", Some "PURPLE",
    [ fun fmt () -> Clause.pp_name fmt c ]

end

(** Functor to provide dot printing *)
module Make(A : Arg with type atom := atom
                     and type hyp := clause
                     and type lemma := clause
                     and type assumption := clause) = struct

  let[@inline] node_id n = "n"^string_of_int (Clause.name n.Proof.conclusion)
  let[@inline] res_node_id n = node_id n ^ "_res"
  let[@inline] proof_id p = node_id (Proof.expand p)

  let print_clause fmt c =
    let v = c.c_atoms in
    if Array.length v = 0 then (
      Format.fprintf fmt "⊥"
    ) else (
      let n = Array.length v in
      for i = 0 to n - 1 do
        Format.fprintf fmt "%a" A.print_atom v.(i);
        if i < n - 1 then
          Format.fprintf fmt ", "
      done
    )

  let print_edge fmt i j = Format.fprintf fmt "%s -> %s;@\n" j i

  let print_edges fmt n =
    begin match n.Proof.step with
      | Proof.Hyper_res _ ->
        List.iter (fun p -> print_edge fmt (res_node_id n) (proof_id p))
          (Proof.parents n.Proof.step)
      | _ -> ()
    end

  let table_options fmt color =
    Format.fprintf fmt "BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\" BGCOLOR=\"%s\"" color

  let table fmt (c, rule, color, l) =
    Format.fprintf fmt "<TR><TD colspan=\"2\">%a</TD></TR>" print_clause c;
    match l with
      | [] ->
        Format.fprintf fmt "<TR><TD BGCOLOR=\"%s\" colspan=\"2\">%s</TD></TR>" color rule
      | f :: r ->
        Format.fprintf fmt "<TR><TD BGCOLOR=\"%s\" rowspan=\"%d\">%s</TD><TD>%a</TD></TR>"
          color (List.length l) rule f ();
        List.iter (fun f -> Format.fprintf fmt "<TR><TD>%a</TD></TR>" f ()) r

  let print_dot_node fmt id color c rule rule_color l =
    Format.fprintf fmt "%s [shape=plaintext, label=<<TABLE %a>%a</TABLE>>];@\n"
      id table_options color table (c, rule, rule_color, l)

  type inf_on =
    | Inf_pivot of atom

  let pp_inf_on out = function
    | Inf_pivot a -> A.print_atom out a

  let print_dot_res_node fmt id (inf_on:inf_on list) =
    Format.fprintf fmt "%s [label=<%a>];@\n"
      id (Util.pp_list ~sep:";" pp_inf_on) inf_on

  let ttify f c = fun fmt () -> f fmt c

  let print_contents fmt n =
    begin match n.Proof.step with
      (* Leafs of the proof tree *)
      | Proof.Hypothesis ->
        let rule, color, l = A.hyp_info Proof.(n.conclusion) in
        let color = match color with None -> "LIGHTBLUE" | Some c -> c in
        print_dot_node fmt (node_id n) "LIGHTBLUE" Proof.(n.conclusion) rule color l
      | Proof.Assumption ->
        let rule, color, l = A.assumption_info Proof.(n.conclusion) in
        let color = match color with None -> "LIGHTBLUE" | Some c -> c in
        print_dot_node fmt (node_id n) "LIGHTBLUE" Proof.(n.conclusion) rule color l
      | Proof.Lemma _lemma ->
        let rule, color, l = A.lemma_info Proof.(n.conclusion) in
        let color = match color with None -> "YELLOW" | Some c -> c in
        print_dot_node fmt (node_id n) "LIGHTBLUE" Proof.(n.conclusion) rule color l

      (* Tree nodes *)
      | Proof.Deduplicate (p, l) ->
        print_dot_node fmt (node_id n) "GREY" Proof.(n.conclusion) "Duplicate" "GREY"
          ((fun fmt () -> (Format.fprintf fmt "%s" (node_id n))) ::
             List.map (ttify A.print_atom) l);
        print_edge fmt (node_id n) (node_id (Proof.expand p))
      | Proof.Hyper_res {steps;_} ->
        print_dot_node fmt (node_id n) "GREY" Proof.(n.conclusion) "Hyper_res" "GREY"
          [(fun fmt () -> Format.fprintf fmt "%s" (node_id n))];
        let pivots =
          CCList.flat_map
            (function
              | Step_resolve {pivot;_} -> [Inf_pivot (Term.Bool.pa pivot)])
            steps
        in
        print_dot_res_node fmt (res_node_id n) pivots;
        print_edge fmt (node_id n) (res_node_id n);
    end

  let print_node fmt n =
    print_contents fmt n;
    print_edges fmt n

  let print fmt p =
    Format.fprintf fmt "digraph proof {@\n";
    Proof.fold (fun () -> print_node fmt) () p;
    Format.fprintf fmt "}@."

end
