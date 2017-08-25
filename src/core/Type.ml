
type t = {
  mutable id: int;
  view: view;
}
and view =
  | Atomic of ID.t * t array
  | Fun of t * t

let[@inline] view {view; _} = view

let[@inline] equal a b = a.id = b.id
let[@inline] compare a b = CCInt.compare a.id b.id
let[@inline] hash a = a.id

module H = Weak.Make(struct
    type nonrec t = t
    let equal a b = match a.view, b.view with
      | Atomic (i1,a1), Atomic (i2,a2) ->
        ID.equal i1 i2 && CCArray.equal equal a1 a2
      | Fun (a1,b1), Fun (a2,b2) ->
        equal a1 a2 && equal b1 b2
      | Atomic _, _
      | Fun _, _ -> false

    let hash t = match t.view with
      | Atomic (i,_) -> CCHash.combine2 2 (ID.hash i)
      | Fun (a,b) -> CCHash.combine3 3 (hash a) (hash b)
end)

let mk_ =
  let n = ref 0 in
  let tbl = H.create 128 in
  fun view : t ->
    let t = { view; id= -1; } in
    let u = H.merge tbl t in
    if t == u then (
      t.id <- !n;
      incr n;
    );
    u

let const id : t = mk_ (Atomic (id, [| |]))
let app id a : t = mk_ (Atomic (id, a))

let prop_id = ID.make "Bool"
let prop = const prop_id

let fun_ a b : t = mk_ (Fun (a,b))
let fun_l args ret : t = List.fold_right fun_ args ret

let unfold_fun t : t list * t =
  let rec aux acc t = match view t with
    | Atomic _ -> List.rev acc, t
    | Fun (a, b) -> aux (a::acc) b
  in
  aux [] t

let rec arity t : int = match view t with
  | Atomic _ -> 0
  | Fun (_, t) -> 1 + arity t

let rec pp out t = match view t with
  | Atomic (id, [| |]) -> ID.pp out id
  | Atomic (id, args) ->
    Format.fprintf out "(@[<hv2>%a@ %a@])" ID.pp id (Util.pp_array pp) args
  | Fun _ ->
    let args, ret = unfold_fun t in
    Format.fprintf out "(@[<hv2>-> %a@ %a@])" (Util.pp_list pp) args pp ret

