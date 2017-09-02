
(* This file is free software, copyright Simon Cruanes. See file "LICENSE" for more details. *)

(** {1 Locations} *)

type t = {
  file : string;
  start_line : int;
  start_column : int;
  stop_line : int;
  stop_column : int;
}

let mk file start_line start_column stop_line stop_column =
  { file; start_line; start_column; stop_line; stop_column; }

let mk_pair file (a,b)(c,d) = mk file a b c d

let mk_pos start stop =
  let open Lexing in
  mk
    start.pos_fname
    start.pos_lnum (start.pos_cnum - start.pos_bol)
    stop.pos_lnum (stop.pos_cnum - stop.pos_bol)

let equal = (=)

let pp out pos =
  if pos.start_line = pos.stop_line
  then
    Format.fprintf out "file '%s': line %d, col %d to %d"
      pos.file pos.start_line pos.start_column pos.stop_column
  else
    Format.fprintf out "file '%s': line %d, col %d to line %d, col %d"
      pos.file
      pos.start_line pos.start_column
      pos.stop_line pos.stop_column

let pp_opt out = function
  | None -> Format.fprintf out "<no location>"
  | Some pos -> pp out pos

let pp_to_string pp x =
  let buf = Buffer.create 64 in
  let fmt = Format.formatter_of_buffer buf in
  pp fmt x;
  Format.pp_print_flush fmt ();
  Buffer.contents buf

let to_string_opt = pp_to_string pp_opt

(** {2 Lexbuf} *)

let set_file buf filename =
  let open Lexing in
  buf.lex_curr_p <- {buf.lex_curr_p with pos_fname=filename;};
  ()

let get_file buf =
  let open Lexing in
  buf.lex_curr_p.pos_fname

let of_lexbuf lexbuf =
  let start = Lexing.lexeme_start_p lexbuf in
  let end_ = Lexing.lexeme_end_p lexbuf in
  let s_l = start.Lexing.pos_lnum in
  let s_c = start.Lexing.pos_cnum - start.Lexing.pos_bol in
  let e_l = end_.Lexing.pos_lnum in
  let e_c = end_.Lexing.pos_cnum - end_.Lexing.pos_bol in
  let file = get_file lexbuf in
  mk file s_l s_c e_l e_c
