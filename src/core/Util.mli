
(** {1 Utils} *)

val pp_array : ?sep:string -> 'a CCFormat.printer -> 'a array CCFormat.printer
val pp_seq : ?sep:string -> 'a CCFormat.printer -> 'a Iter.t CCFormat.printer
val pp_list : ?sep:string -> 'a CCFormat.printer -> 'a list CCFormat.printer

val swap_arr : 'a array -> int -> int -> unit
(** [swap_arr arr i j] swaps elements at indices [i] and [j] *)

val setup_gc : unit -> unit
(** Change parameters of the GC *)

module Int_map : CCMap.S with type key = int
module Str_map : CCMap.S with type key = string
