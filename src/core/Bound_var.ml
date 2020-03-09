
open Solver_types

let name = "bvar"
type t = bound_var

type term_view += BVar of bound_var

let pp out ((id,_ty) : t) : unit = ID.pp out id
let pp_with_ty out ((id,ty) : t) : unit =
  Fmt.fprintf out "(@[%a@ %a@])" ID.pp id Type.pp ty

let k_bvar = Service.Key.make name

let build (p_id:plugin_id) Plugin.S_nil : Plugin.t =
  let tc = Term.TC.lazy_make () in
  let module P : Plugin.S = struct
    let id = p_id
    let name = name

    (* term allocator *)
    module T_alloc = Term.Term_allocator(struct
        let tc = tc
        let p_id = p_id
        let initial_size=256
        let[@inline] equal v1 v2 = match v1, v2 with
          | BVar (v1,ty1), BVar (v2,ty2) -> ID.equal v1 v2 && Type.equal ty1 ty2
          | _ -> assert false
        let[@inline] hash = function
          | BVar (v,ty) -> CCHash.combine3 125 (ID.hash v) (Type.hash ty)
          | _ -> assert false
      end)

    let gc_all = T_alloc.gc_all
    let iter_terms = T_alloc.iter_terms

    let pp out = function
      | BVar v -> pp out v
      | _ -> assert false

    (* builder *)
    let[@inline] bvar ((id,ty):t) : term =
      T_alloc.make (BVar (id,ty)) ty

    let check_if_sat _ = Sat

    let () =
      Term.TC.lazy_complete tc ~pp

    let provided_services =
      [ Service.Any (k_bvar, bvar);
      ]
  end
  in
  (module P : Plugin.S)

let plugin = Plugin.Factory.make ~priority:10 ~name ~requires:Plugin.K_nil ~build ()
