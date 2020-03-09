
(** {1 Services} *)

(** A service is a feature provided by a plugin. A typical service
    would be a function to build terms, or to traverse all sub-terms,
    or to perform E-matching, etc.

    A registry is used to list all services provided by plugins and make
    them available to users of the library, or to other plugins.
*)

(* we use ['a lazy_t] to tie the knot properly when services
   mutually depend on one another *)

module M = Het_map

module Key = struct
  type 'a t = {
    key: 'a Het_map.Key.t;
    key_name: string;
  }

  let[@inline] make key_name = {key_name; key=M.Key.create()}
  let[@inline] name k = k.key_name
  let[@inline] makef fmt = CCFormat.ksprintf ~f:make fmt
end

type any = Any : 'a Key.t * 'a -> any
(** Existential wrapper around a service *)

module Registry = struct
  type t = {
    tbl: M.Tbl.t;
    mutable lst: any list;
  }

  let create() = {
    tbl=M.Tbl.create ~size:16 ();
    lst=[];
  }

  let register (r:t) (key:'a Key.t) (v:'a) : unit =
    if M.Tbl.mem r.tbl key.Key.key then (
      Error.errorf "service `%s` already registered" key.Key.key_name;
    );
    Log.debugf 5 (fun k->k "register service `%s`" key.Key.key_name);
    M.Tbl.add r.tbl key.Key.key v;
    r.lst <- Any (key,v) :: r.lst

  let[@inline] find (r:t) k = M.Tbl.find r.tbl k.Key.key
  let[@inline] to_seq (r:t) = Iter.of_list r.lst
  let[@inline] find_exn r k = match find r k with
    | Some v -> v
    | None -> Error.errorf "could not find service `%s`" (Key.name k)
end

