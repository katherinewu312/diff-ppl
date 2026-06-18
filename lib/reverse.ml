module StringMap = Adev.StringMap

type seeds = Adev.seeds

let no_seeds = Adev.no_seeds
let add_seed = Adev.add_seed
let seeds_of_param = Adev.seeds_of_param

let const = Simplify.mk_const
let add = Simplify.mk_add
let mul = Simplify.mk_mul
let pair = Simplify.mk_pair

let resolve_seeds ?param ?seeds te =
  match seeds, param with
  | Some seeds, _ -> seeds
  | None, Some param -> seeds_of_param param
  | None, None -> Adev.infer_default_seeds te

let gradient_component_raw param te =
  Adev.gradient_raw ~seeds:(seeds_of_param param) te

let weighted_gradient_sum te seeds =
  let terms =
    StringMap.bindings seeds
    |> List.filter_map (fun (param, seed) ->
      if seed = 0.0 then None
      else Some (mul (const seed) (gradient_component_raw param te)))
  in
  match terms with
  | [] -> const 0.0
  | first :: rest -> List.fold_left add first rest

let dual_expectation_raw ?param ?seeds te =
  let seeds = resolve_seeds ?param ?seeds te in
  let primal = Adev.dual_primal (Adev.dual_expectation_raw ~seeds te) in
  pair primal (weighted_gradient_sum te seeds)

let gradient_raw ?param ?seeds te =
  Adev.dual_tangent (dual_expectation_raw ?param ?seeds te)

let dual_expectation ?param ?seeds te =
  Simplify.algebraic (dual_expectation_raw ?param ?seeds te)

let gradient ?param ?seeds te =
  Simplify.algebraic (gradient_raw ?param ?seeds te)
