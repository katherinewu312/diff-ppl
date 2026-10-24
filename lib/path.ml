(** Per-path symbolic state and the path monad. A computation of type ['a t]
    maps the state of one path to the outcomes of every path it forks into. *)
module S = Symbolic
module Store = Map.Make(Int)

type sample = { id : int; distribution : Distribution.t; parameters : S.term list }
type state = {
  constraints : S.term list;
  observations : S.term list;
  requirements : S.term list;
  samples : sample list;
  store : Value.t Store.t;
  next_location : int;
  steps : int;
}

type stop = Rejected | Step_limit | Runtime_error of string
type 'a outcome = Returned of state * 'a | Stopped of state * stop
type 'a t = state -> 'a outcome list

let empty = {
  constraints=[]; observations=[]; requirements=[]; samples=[];
  store=Store.empty; next_location=0; steps=0;
}

let state = function Returned (s,_) | Stopped (s,_) -> s

(** Bounds and counters shared by all paths of one exploration. Sample ids
    are global so that draws on different paths never share an id. *)
type exploration = {
  max_steps : int;
  max_paths : int;
  mutable leaves : int;
  mutable next_sample : int;
}
exception Path_limit of int

let exploration ~max_steps ~max_paths =
  { max_steps; max_paths; leaves=1; next_sample=0 }

(* Monad *)
let return v s = [Returned (s,v)]
let ( let* ) m f s =
  List.concat_map (function
    | Returned (s,v) -> f v s
    | Stopped (s,why) -> [Stopped (s,why)]) (m s)
let stop why s = [Stopped (s,why)]
let fail msg s = stop (Runtime_error msg) s
let rec all = function
  | [] -> return []
  | m :: ms -> let* v = m in let* vs = all ms in return (v :: vs)
let rec iter f = function
  | [] -> return ()
  | x :: xs -> let* () = f x in iter f xs

(* Path operations *)
let tick x s =
  if s.steps >= x.max_steps then stop Step_limit s
  else return () {s with steps=s.steps+1}

let assume s condition =
  match condition with
  | S.Boolean true -> Some s
  | S.Boolean false -> None
  | t when List.mem (S.negate t) s.constraints -> None
  | t when List.mem t s.constraints -> Some s
  | t -> Some {s with constraints=s.constraints @ [t]}

(** Continue with [v] on a new path for each [(condition, v)] that is not
    already known to be false. *)
let fork x branches s =
  let live = List.filter_map (fun (condition,v) ->
    Option.map (fun s -> Returned (s,v)) (assume s condition)) branches in
  x.leaves <- x.leaves + max 0 (List.length live - 1);
  if x.leaves > x.max_paths then raise (Path_limit x.max_paths);
  live

let branch x condition = fork x [condition,true; S.negate condition,false]

let require msg term s =
  match term with
  | S.Boolean true -> return () s
  | S.Boolean false -> fail msg s
  | t when List.mem t s.requirements -> return () s
  | t -> return () {s with requirements=s.requirements @ [t]}

let observe condition s =
  return () {s with observations=s.observations @ [condition]}

let draw x distribution parameters =
  let msg = "Invalid parameters for " ^ Distribution.name distribution in
  let* () = iter (require msg) (Distribution.requirements distribution parameters) in
  fun s ->
    let id = x.next_sample in
    x.next_sample <- id+1;
    return id {s with samples=s.samples @ [{id;distribution;parameters}]}

let alloc v s =
  let id = s.next_location in
  return id {s with next_location=id+1; store=Store.add id v s.store}
let read id s = return (Store.find id s.store) s
let write id v s = return () {s with store=Store.add id v s.store}
