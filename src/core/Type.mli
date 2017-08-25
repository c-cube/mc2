
(** {1 Simple Types} *)

type t = private {
  mutable id: int;
  view: view;
}
and view =
  | Atomic of ID.t * t array
  | Fun of t * t

val view : t -> view

val prop_id : ID.t
val prop : t

val const : ID.t -> t
val app : ID.t -> t array -> t

val fun_ : t -> t -> t
val fun_l : t list -> t -> t

val equal : t -> t -> bool
val compare : t -> t -> int
val hash : t -> int
val pp : t CCFormat.printer

val unfold_fun : t -> t list * t
(** [unfold_fun (a -> (b -> (c -> d)))] returns [[a;b;c], d] *)

val arity : t -> int
(** Number of arguments needed, as a function *)


