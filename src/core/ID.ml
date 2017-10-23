
module Fmt = CCFormat

type t = {
  id: int;
  name: string;
}

let make =
  let n = ref 0 in
  fun name ->
    let x = { id= !n; name; } in
    incr n;
    x

let makef fmt = CCFormat.ksprintf ~f:make fmt

let copy {name;_} = make name

let id {id;_} = id
let to_string id = id.name

let equal a b = a.id=b.id
let compare a b = CCInt.compare a.id b.id
let hash a = CCHash.int a.id
let pp out a = Format.fprintf out "%s/%d" a.name a.id
let pp_name out a = Fmt.string out a.name
let to_string_full a = Printf.sprintf "%s/%d" a.name a.id

module AsKey = struct
  type t_ = t
  type t = t_
  let equal = equal
  let compare = compare
  let hash = hash
end

module Map = CCMap.Make(AsKey)
module Set = CCSet.Make(AsKey)
module Tbl = CCHashtbl.Make(AsKey)

module Smtlib = struct
  let needs_escaping_ =
    CCString.exists
      (function
        | '|' | ' ' | '(' | ')' -> true
        | _ -> false)

  let pp out i =
    if needs_escaping_ i.name
    then Fmt.fprintf out "|%s|" i.name
    else Fmt.string out i.name

end
