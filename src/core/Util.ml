
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

let setup_gc () =
  Gc.set {
    (Gc.get()) with
    Gc.space_overhead = 3_000; (* major gc *)
    Gc.max_overhead = 10_000; (* compaction *)
    Gc.minor_heap_size = 500_000; (* ×8 to obtain bytes on 64 bits -->  *)
  }

module Int_map = CCMap.Make(CCInt)
module Str_map = CCMap.Make(String)
