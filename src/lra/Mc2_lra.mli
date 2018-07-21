
(** {1 Linear Rational Arithmetic} *)

open Mc2_core

type num = Q.t

module LE = Linexp

(** Boolean operator *)
type op =
  | Eq0
  | Leq0
  | Lt0

val k_rat : ty Service.Key.t
(** Type of rationals *)

val k_make_const : (num -> term) Service.Key.t
(** Constant as a term *)

val k_make_pred : (op -> Linexp.t -> term) Service.Key.t
(** Build constraint *)

val k_make_linexp : (Linexp.t -> term) Service.Key.t
(** Build term *)

val plugin : Plugin.Factory.t
