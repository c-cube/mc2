(*********************************************************************************)
(*  Copyright (c) 2015, INRIA, Universite de Nancy 2 and Universidade Federal    *)
(*  do Rio Grande do Norte.                                                      *)
(*                                                                               *)
(*  Permission to use, copy, modify, and distribute this software for any        *)
(*  purpose with or without fee is hereby granted, provided that the above       *)
(*  copyright notice and this permission notice appear in all copies.            *)
(*                                                                               *)
(*  THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES     *)
(*  WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF             *)
(*  MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR      *)
(*  ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES       *)
(*  WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN        *)
(*  ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF      *)
(*  OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.               *)
(*********************************************************************************)

type t = {
  loc_start: Lexing.position;
  loc_end: Lexing.position;
}

let mk_loc loc_start loc_end = { loc_start; loc_end; }

let in_file name =
  let loc = {
    Lexing.pos_fname = name;
    Lexing.pos_lnum = 1;
    Lexing.pos_bol = 0;
    Lexing.pos_cnum = -1;
  }
  in
  { loc_start = loc; loc_end = loc; }

let none = in_file "_none_";;

let dummy_loc = { loc_start = Lexing.dummy_pos; loc_end = Lexing.dummy_pos; }

let pp out pos =
  if pos.loc_start.Lexing.pos_lnum = pos.loc_end.Lexing.pos_lnum
  then
    Format.fprintf out "file '%s': line %d, col %d to %d"
      pos.loc_start.Lexing.pos_fname pos.loc_start.Lexing.pos_lnum
      pos.loc_start.Lexing.pos_cnum pos.loc_end.Lexing.pos_cnum
  else
    Format.fprintf out "file '%s': line %d, col %d to line %d, col %d"
      pos.loc_start.Lexing.pos_fname
      pos.loc_start.Lexing.pos_lnum pos.loc_start.Lexing.pos_cnum
      pos.loc_end.Lexing.pos_lnum pos.loc_end.Lexing.pos_cnum

let pp_opt out = function
  | None -> Format.fprintf out "<no location>"
  | Some pos -> pp out pos
