
(** {1 Utils} *)

module Fmt = CCFormat

let pp_sep sep out () = Format.fprintf out "%s@," sep
let pp_list ?(sep=" ") pp = Fmt.list ~sep:(pp_sep sep) pp
let pp_seq ?(sep=" ") pp = Fmt.seq ~sep:(pp_sep sep) pp
let pp_array ?(sep=" ") pp = Fmt.array ~sep:(pp_sep sep) pp

(* swap elements of array *)
let[@inline] swap_arr a i j =
  if i<>j then (
    let tmp = a.(i) in
    a.(i) <- a.(j);
    a.(j) <- tmp;
  )

exception Error of string

let err_ksprintf ~f fmt =
  let buf = Buffer.create 32 in
  let out = Format.formatter_of_buffer buf in
  CCFormat.set_color_tag_handling out;
  Format.fprintf out "@[<2>@{<Red>error:@}@ ";
  Format.kfprintf
    (fun _ -> Format.fprintf out "@]@?"; f (Buffer.contents buf))
    out fmt

let err_sprintf fmt = err_ksprintf ~f:CCFun.id fmt
let errorf msg = err_ksprintf ~f:(fun e -> raise (Error e)) msg
let error msg = errorf "%s" msg

exception Out_of_time
exception Out_of_space

let with_limits ~time ~memory f =
  (* Limits alarm *)
  let check () =
    let t = Sys.time () in
    let heap_size = (Gc.quick_stat ()).Gc.heap_words in
    let s = float heap_size *. float Sys.word_size /. 8. in
    if t > time then (
      raise Out_of_time
    ) else if s > memory then (
      raise Out_of_space
    )
  in
  let al = Gc.create_alarm check in
  CCFun.finally ~h:(fun () -> Gc.delete_alarm al) ~f

let setup_gc () =
  let g = Gc.get () in
  g.Gc.space_overhead <- 3_000; (* major gc *)
  g.Gc.max_overhead <- 10_000; (* compaction *)
  g.Gc.minor_heap_size <- 500_000; (* ×8 to obtain bytes on 64 bits -->  *)
  Gc.set g

let () = Printexc.register_printer
    (function
      | Error msg -> Some msg
      | Out_of_space -> Some "out of space"
      | Out_of_time -> Some "out of time"
      | _ -> None)
