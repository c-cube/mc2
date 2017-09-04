
(** {1 Simple Types} *)

open Solver_types

type t = ty
type view = ty_view

let[@inline] view = function
  | Bool -> assert false
  | Ty {view; _} -> view

let[@inline] id = function
  | Bool -> assert false
  | Ty {id;_} -> id

let[@inline] equal a b = match a, b with
  | Bool, Bool -> true
  | Ty _, Ty _ -> a==b
  | Bool, _
  | Ty _, _ -> false

let[@inline] compare a b = match a, b with
  | Bool, Bool -> 0
  | Bool, Ty _ -> -1
  | Ty _, Bool -> 1
  | Ty {id=i1;_}, Ty {id=i2; _} -> CCInt.compare i1 i2

let[@inline] hash t = match t with
  | Bool -> 1
  | Ty {id;_} -> CCHash.int id

let bool = Bool

let[@inline] is_bool = function
  | Bool -> true
  | Ty _ -> false

let[@inline] pp out t = match t with
  | Bool -> CCFormat.string out "Bool"
  | Ty {tc; view; _} -> tc.tcty_pp out view

let[@inline] decide (ty:t) (a:actions) (t:term) : value = match ty with
  | Bool -> assert false
  | Ty {tc; _} -> tc.tcty_decide a t

let[@inline] mk_decide_state (ty:t) : decide_state = match ty with
  | Bool -> assert false
  | Ty {tc; _} -> tc.tcty_mk_state()

module type TY_ALLOC_OPS = sig
  val initial_size: int (** initial size of table *)
  val equal : view -> view -> bool (** Shallow equality of two views of the plugin *)
  val hash : view -> int (** Shallow hash of a view of the plugin *)
  val tc : tc_ty
end

(* global ID allocator *)
let n_ = ref 0

module Alloc(Arg : TY_ALLOC_OPS) = struct
  module H = Weak.Make(struct
      type nonrec t = t
      let equal a b = match a, b with
        | Bool, _
        | _, Bool -> assert false
        | Ty {view=v1; _}, Ty {view=v2; _} -> Arg.equal v1 v2

      let hash t = match t with
        | Bool -> assert false
        | Ty {view; _} -> Arg.hash view
    end)

  let tbl = H.create Arg.initial_size

  let make view =
    let ty = Ty {id= ~-1; view; tc=Arg.tc } in
    let u = H.merge tbl ty in
    if ty == u then begin[@warning "-8"]
      let Ty v = ty in
      v.id <- !n_;
      incr n_;
    end;
    u
end
