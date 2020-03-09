
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

let () = Printexc.register_printer
    (function
      | Error msg -> Some msg
      | _ -> None)
