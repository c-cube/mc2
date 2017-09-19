
(** {1 Utils} *)

val pp_array : ?sep:string -> 'a CCFormat.printer -> 'a array CCFormat.printer
val pp_seq : ?sep:string -> 'a CCFormat.printer -> 'a Sequence.t CCFormat.printer
val pp_list : ?sep:string -> 'a CCFormat.printer -> 'a list CCFormat.printer

val swap_arr : 'a array -> int -> int -> unit
(** [swap_arr arr i j] swaps elements at indices [i] and [j] *)

exception Error of string

val errorf : ('a, Format.formatter, unit, 'b) format4 -> 'a
val error : string -> 'a

val err_sprintf : ('a, Format.formatter, unit, unit, unit, string) format6 -> 'a
(** Like {!Fmt.sprintf} but specialized for errors *)


val setup_gc : unit -> unit
(** Change parameters of the GC *)

module Int_map : CCMap.S with type key = int
