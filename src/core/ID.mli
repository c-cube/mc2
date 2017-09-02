
(** {1 Unique Identifiers} *)

type t

val make : string -> t
val makef : ('a, Format.formatter, unit, t) format4 -> 'a
val copy : t -> t

val id : t -> int

val to_string : t -> string
val to_string_full : t -> string

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val pp : t CCFormat.printer

val pp_name : t CCFormat.printer

module Map : CCMap.S with type key = t
module Set : CCSet.S with type elt = t
module Tbl : CCHashtbl.S with type key = t
