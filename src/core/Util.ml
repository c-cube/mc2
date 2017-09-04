
(** {1 Utils} *)

module Fmt = CCFormat

let pp_sep sep out () = Format.fprintf out "%s@," sep
let pp_list ?(sep=" ") pp = Fmt.list ~sep:(pp_sep sep) pp
let pp_seq ?(sep=" ") pp = Fmt.seq ~sep:(pp_sep sep) pp
let pp_array ?(sep=" ") pp = Fmt.array ~sep:(pp_sep sep) pp

exception Error of string

let () = Printexc.register_printer
    (function
      | Error msg -> Some msg
      | _ -> None)

let exn_ksprintf ~f fmt =
  let buf = Buffer.create 32 in
  let out = Format.formatter_of_buffer buf in
  Format.fprintf out "@[<2>@{<Red>error:@}@ ";
  Format.kfprintf
    (fun _ -> Format.fprintf out "@]@?"; raise (f (Buffer.contents buf)))
    out fmt

let errorf msg = exn_ksprintf ~f:(fun e -> raise (Error e)) msg
let error msg = errorf "%s" msg
