
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


exception Out_of_time
exception Out_of_space

val with_limits :
  time:float ->
  memory:float ->
  (unit -> 'a) ->
  'a
(** Perform computation [f ()] with limited amount of time and space.
    @param time limit, in seconds, measured with [Sys.time()]
    @param memory number of words in the heap
    @raise Out_of_time if out of time
    @raise Out_of_space if out of space
*)

val setup_gc : unit -> unit
(** Change parameters of the GC *)
