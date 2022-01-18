
(** {1 Utils} *)

module Fmt = CCFormat

let pp_sep sep out () = Format.fprintf out "%s@," sep
let pp_list ?(sep=" ") pp = Fmt.list ~sep:(pp_sep sep) pp
let pp_iter ?(sep=" ") pp = Fmt.iter ~sep:(pp_sep sep) pp
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

module Switch = struct
  type t = bool ref
  let create() = ref false
  let[@inline] activate self = self := true
  let[@inline] activated self = !self
  let activated_opt = function None -> false | Some s -> activated s
end

module Int_map = CCMap.Make(CCInt)
module Str_map = CCMap.Make(String)

module Option = CCOpt
