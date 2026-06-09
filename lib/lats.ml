open Lat (* Ensure this is at the top *)

(* Generic type representing either a finite Set or Top *)
type ('elt, 'set) set_or_top =
  | Finite of 'set (* Store the actual Set instance *)
  | Top

(* == Float Set == *)
module FloatSet = Set.Make(struct type t = float let compare = compare end)

(* == Adapter for Lat == *)
module FloatSetContents : Lat with type t = (float, FloatSet.t) set_or_top = struct
  type t = (float, FloatSet.t) set_or_top
  let union v1 v2 =
    match v1, v2 with
    | Top, _ -> Top
    | _, Top -> Top
    | Finite s1, Finite s2 -> Finite (FloatSet.union s1 s2)

  let equal v1 v2 =
    match v1, v2 with
    | Top, Top -> true
    | Finite s1, Finite s2 -> FloatSet.equal s1 s2
    | _, _ -> false
end

(* == Lat Instantiation == *)
module FloatLat = Make(FloatSetContents)

let fresh_float_bag () : FloatLat.bag =
  FloatLat.create (Finite FloatSet.empty)
