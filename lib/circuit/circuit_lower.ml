(** Lowering from the typed, discretized Slice AST to arithmetic circuits and
    reduced decision diagrams.

    Every float carries two representations: a cheap expected-value arithmetic
    node and a lazy exact DD.  Affine operations and operations on independent
    values use the expected-value summaries directly.  The exact DD is forced
    only by an operation that needs joint information, such as multiplying two
    values with overlapping random-variable support.  This is a forward,
    demand-driven strategy; it requires no backward analysis.

    Exact float DDs retain reverse-ordered additive components.  Addition can
    therefore concatenate lazy components, preserving linearity even on paths
    that eventually demand the exact representation.

    Boolean and finite values always have exactly one component.  At DD leaves
    they are encoded as arithmetic constants: false/true as 0/1 and a finite
    value [k#n] as [float k].  They are consumed during lowering, so the final
    arithmetic circuit remains float-only.  Only the first moment is tracked;
    correlated products (including a random square) fall back to the exact DD.
*)

open Ast

module StringMap = Map.Make (String)
module RvSet = Set.Make (Int)

type value_kind =
  | Float
  | Bool
  | Fin of int

type value =
  { kind : value_kind
  ; parts : Circuit_dd.dd_id list Lazy.t
  ; mean : Circuit_ir.ac_id Lazy.t option
  ; support : RvSet.t
  ; additive_terms : int
  }

type choice_weights =
  { weights : Circuit_ir.ac_id array }

type operations =
  { add : Circuit_dd.binary_op
  ; sub : Circuit_dd.binary_op
  ; negate : Circuit_dd.unary_op
  ; mul : Circuit_dd.binary_op
  ; div : Circuit_dd.binary_op
  ; bool_and : Circuit_dd.binary_op
  ; bool_or : Circuit_dd.binary_op
  ; bool_not : Circuit_dd.unary_op
  ; less : Circuit_dd.binary_op
  ; less_equal : Circuit_dd.binary_op
  ; equal : Circuit_dd.binary_op
  }

type program =
  { arithmetic : Circuit_ir.t
  ; decisions : Circuit_dd.t
  ; choices : (Circuit_dd.rv_id, choice_weights) Hashtbl.t
  ; result_kind : value_kind
  ; result_parts : Circuit_dd.dd_id list
  ; additive_terms : int
  ; elimination_memo : (Circuit_dd.dd_id, Circuit_ir.ac_id) Hashtbl.t
  }

type builder =
  { arithmetic : Circuit_ir.t
  ; decisions : Circuit_dd.t
  ; choices : (Circuit_dd.rv_id, choice_weights) Hashtbl.t
  ; operations : operations
  ; zero : Circuit_ir.ac_id
  ; one : Circuit_ir.ac_id
  ; zero_dd : Circuit_dd.dd_id
  ; elimination_memo : (Circuit_dd.dd_id, Circuit_ir.ac_id) Hashtbl.t
  }

type env = value StringMap.t

let fail message = failwith ("Circuit compilation: " ^ message)

let unsupported construct =
  fail (construct ^ " is not supported by the initial circuit backend")

let kind_name = function
  | Float -> "float"
  | Bool -> "bool"
  | Fin n -> Printf.sprintf "Fin(%d)" n

let kind_of_ty ty =
  match Ast.force ty with
  | TFloat _ -> Float
  | TBool -> Bool
  | TFin n -> Fin n
  | TPair _ -> unsupported "pairs"
  | TFun _ -> unsupported "functions"
  | TUnit -> unsupported "unit values"
  | TList _ -> unsupported "lists"
  | TRef _ -> unsupported "references"
  | TMeta _ -> fail "encountered an unresolved type"

let require_kind expected value context =
  if value.kind <> expected then
    fail
      (Printf.sprintf "%s expected %s but received %s" context
         (kind_name expected) (kind_name value.kind))

let ac_constant arithmetic id =
  match Circuit_ir.lookup arithmetic id with
  | Circuit_ir.Const value -> Some value
  | Circuit_ir.Param _ | Circuit_ir.Add _ | Circuit_ir.Sub _
  | Circuit_ir.Mul _ | Circuit_ir.Div _ | Circuit_ir.Special _ -> None

let boolean_constant arithmetic id =
  match ac_constant arithmetic id with
  | Some value when value = 0.0 -> Some false
  | Some value when value = 1.0 -> Some true
  | Some _ | None -> None

let finite_constant arithmetic id =
  match ac_constant arithmetic id with
  | Some value ->
      let integer = int_of_float value in
      if float_of_int integer = value then Some integer else None
  | None -> None

let create_builder () =
  let arithmetic = Circuit_ir.create () in
  let decisions = Circuit_dd.create () in
  let zero = Circuit_ir.const arithmetic 0.0 in
  let one = Circuit_ir.const arithmetic 1.0 in
  let zero_dd = Circuit_dd.leaf decisions zero in
  let bool_binary name operation left right =
    match boolean_constant arithmetic left, boolean_constant arithmetic right with
    | Some left, Some right ->
        Circuit_ir.const arithmetic
          (if operation left right then 1.0 else 0.0)
    | _ -> fail (name ^ " reached a non-constant boolean DD leaf")
  in
  let bool_unary name operation value =
    match boolean_constant arithmetic value with
    | Some value ->
        Circuit_ir.const arithmetic (if operation value then 1.0 else 0.0)
    | None -> fail (name ^ " reached a non-constant boolean DD leaf")
  in
  let finite_binary name operation left right =
    match finite_constant arithmetic left, finite_constant arithmetic right with
    | Some left, Some right ->
        Circuit_ir.const arithmetic
          (if operation left right then 1.0 else 0.0)
    | _ -> fail (name ^ " reached a non-constant finite DD leaf")
  in
  let operations =
    { add = Circuit_dd.make_binary (Circuit_ir.add arithmetic)
    ; sub = Circuit_dd.make_binary (Circuit_ir.sub arithmetic)
    ; negate =
        Circuit_dd.make_unary
          (fun value -> Circuit_ir.sub arithmetic zero value)
    ; mul = Circuit_dd.make_binary (Circuit_ir.mul arithmetic)
    ; div = Circuit_dd.make_binary (Circuit_ir.div arithmetic)
    ; bool_and =
        Circuit_dd.make_binary (bool_binary "boolean conjunction" ( && ))
    ; bool_or =
        Circuit_dd.make_binary (bool_binary "boolean disjunction" ( || ))
    ; bool_not = Circuit_dd.make_unary (bool_unary "boolean negation" not)
    ; less = Circuit_dd.make_binary (finite_binary "comparison" ( < ))
    ; less_equal = Circuit_dd.make_binary (finite_binary "comparison" ( <= ))
    ; equal = Circuit_dd.make_binary (finite_binary "finite equality" ( = ))
    }
  in
  { arithmetic
  ; decisions
  ; choices = Hashtbl.create 31
  ; operations
  ; zero
  ; one
  ; zero_dd
  ; elimination_memo = Hashtbl.create 251
  }

let is_zero_part builder part =
  match Circuit_dd.lookup builder.decisions part with
  | Circuit_dd.Leaf id -> Circuit_ir.is_zero builder.arithmetic id
  | Circuit_dd.Choice _ -> false

let normalize_float_parts builder parts =
  match List.filter (fun part -> not (is_zero_part builder part)) parts with
  | [] -> [ builder.zero_dd ]
  | nonzero -> nonzero

let make_value builder ?(support = RvSet.empty) ?mean
    ?(additive_terms = 1) kind parts =
  match kind with
  | Float ->
      (match mean with
       | Some mean ->
           { kind
           ; parts = lazy (normalize_float_parts builder (Lazy.force parts))
           ; mean = Some mean
           ; support
           ; additive_terms
           }
       | None -> fail "float value did not have an expected-value summary")
  | Bool | Fin _ ->
      { kind
      ; parts =
          lazy
            (match Lazy.force parts with
             | [ _ ] as parts -> parts
             | _ ->
                 fail
                   (kind_name kind ^ " value did not have exactly one DD root"))
      ; mean = None
      ; support
      ; additive_terms = 1
      }

let singleton builder kind ac =
  make_value builder kind
    ~mean:(lazy ac)
    (lazy [ Circuit_dd.leaf builder.decisions ac ])

let mean value context =
  match value.mean with
  | Some mean -> Lazy.force mean
  | None -> fail (context ^ " requires a float expected-value summary")

let is_deterministic value = RvSet.is_empty value.support

let independent left right =
  RvSet.is_empty (RvSet.inter left.support right.support)

let only_part value context =
  match Lazy.force value.parts with
  | [ part ] -> part
  | _ -> fail (context ^ " requires a single decision diagram")

let materialize builder value =
  (* Components are accumulated in reverse source order so a left-associated
     chain of additions can prepend its usually-small right operand in O(1).
     Restore source order only when an actual DD addition is required. *)
  match List.rev (Lazy.force value.parts) with
  | [] -> builder.zero_dd
  | first :: rest ->
      List.fold_left
        (Circuit_dd.apply2 builder.decisions builder.operations.add)
        first rest

let rec eliminate_dd builder dd =
  match Hashtbl.find_opt builder.elimination_memo dd with
  | Some result -> result
  | None ->
      let result =
        match Circuit_dd.lookup builder.decisions dd with
        | Circuit_dd.Leaf arithmetic -> arithmetic
        | Circuit_dd.Choice (variable, children) ->
            let weights =
              match Hashtbl.find_opt builder.choices variable with
              | Some choice -> choice.weights
              | None ->
                  fail
                    (Printf.sprintf
                       "random variable %d has no probability table" variable)
            in
            if Array.length weights <> Array.length children then
              fail
                (Printf.sprintf
                   "random variable %d has %d branches but %d weights"
                   variable (Array.length children) (Array.length weights));
            Array.mapi
              (fun index child ->
                 Circuit_ir.mul builder.arithmetic weights.(index)
                   (eliminate_dd builder child))
              children
            |> Circuit_ir.sum builder.arithmetic
      in
      Hashtbl.add builder.elimination_memo dd result;
      result

let eliminate_parts builder parts =
  List.map (eliminate_dd builder) parts
  |> Circuit_ir.sum_list builder.arithmetic

let multiply_values builder left right =
  require_kind Float left "multiplication";
  require_kind Float right "multiplication";
  let parts =
    lazy
      (List.fold_left
         (fun result left_part ->
            List.fold_left
              (fun result right_part ->
                 Circuit_dd.apply2 builder.decisions builder.operations.mul
                   left_part right_part
                 :: result)
              result (Lazy.force right.parts))
         [] (Lazy.force left.parts)
       |> List.rev)
  in
  let support = RvSet.union left.support right.support in
  let mean =
    lazy
      (if is_deterministic left || is_deterministic right
          || independent left right
       then
         Circuit_ir.mul builder.arithmetic
           (mean left "multiplication") (mean right "multiplication")
       else
         eliminate_parts builder (Lazy.force parts))
  in
  make_value builder Float ~support ~mean
    ~additive_terms:(left.additive_terms * right.additive_terms)
    parts

let compare_values builder operation expected left right context =
  require_kind expected left context;
  require_kind expected right context;
  make_value builder Bool
    ~support:(RvSet.union left.support right.support)
    (lazy
       [ Circuit_dd.apply2 builder.decisions operation
           (only_part left context) (only_part right context)
       ])

let effect_is_prob effect =
  match Ast.force_effect effect with
  | Prob -> true
  | Pure | EMeta _ -> false

let rec lower_expr builder env ((ty, _effect, TAExprNode expression) : texpr) =
  match expression with
  | Const value -> singleton builder Float (Circuit_ir.const builder.arithmetic value)
  | BoolConst value ->
      singleton builder Bool (if value then builder.one else builder.zero)
  | FinConst (value, modulus) ->
      singleton builder (Fin modulus)
        (Circuit_ir.const builder.arithmetic (float_of_int value))
  | Var name ->
      (match StringMap.find_opt name env with
       | Some value -> value
       | None ->
           (match kind_of_ty ty with
            | Float ->
                singleton builder Float
                  (Circuit_ir.param builder.arithmetic name)
            | Bool | Fin _ ->
                fail
                  (Printf.sprintf
                     "free variable %s has unsupported non-float type %s"
                     name (kind_name (kind_of_ty ty)))))
  | Let (name, rhs, body) ->
      let rhs_value = lower_expr builder env rhs in
      lower_expr builder (StringMap.add name rhs_value env) body
  | Add (left, right) ->
      let left = lower_expr builder env left in
      let right = lower_expr builder env right in
      require_kind Float left "addition";
      require_kind Float right "addition";
      (* [parts] are reverse ordered, so the reversed right side precedes the
         reversed left side.  This copies only the right operand and avoids
         quadratic behavior for left-associated additive objectives. *)
      make_value builder Float
        ~support:(RvSet.union left.support right.support)
        ~mean:
          (lazy
             (Circuit_ir.add builder.arithmetic
                (mean left "addition") (mean right "addition")))
        ~additive_terms:(left.additive_terms + right.additive_terms)
        (lazy (Lazy.force right.parts @ Lazy.force left.parts))
  | Sub (left, right) ->
      let left = lower_expr builder env left in
      let right = lower_expr builder env right in
      require_kind Float left "subtraction";
      require_kind Float right "subtraction";
      let deterministic = is_deterministic left && is_deterministic right in
      let parts =
        lazy
          (if deterministic then
             [ Circuit_dd.apply2 builder.decisions builder.operations.sub
                 (materialize builder left) (materialize builder right)
             ]
           else
             let negated_right =
               List.map
                 (Circuit_dd.map builder.decisions builder.operations.negate)
                 (Lazy.force right.parts)
             in
             (* E[left - right] = sum E[left_i] + sum E[-right_i]. *)
             negated_right @ Lazy.force left.parts)
      in
      make_value builder Float
        ~support:(RvSet.union left.support right.support)
        ~mean:
          (lazy
             (Circuit_ir.sub builder.arithmetic
                (mean left "subtraction") (mean right "subtraction")))
        ~additive_terms:
          (if deterministic then 1
           else left.additive_terms + right.additive_terms)
        parts
  | Mul (left, right) ->
      multiply_values builder
        (lower_expr builder env left)
        (lower_expr builder env right)
  | Div (left, right) ->
      let left = lower_expr builder env left in
      let right = lower_expr builder env right in
      require_kind Float left "division";
      require_kind Float right "division";
      let parts =
        lazy
          [ Circuit_dd.apply2 builder.decisions builder.operations.div
              (materialize builder left) (materialize builder right)
          ]
      in
      make_value builder Float
        ~support:(RvSet.union left.support right.support)
        ~mean:
          (lazy
             (if is_deterministic right then
                Circuit_ir.div builder.arithmetic
                  (mean left "division") (mean right "division")
              else
                eliminate_parts builder (Lazy.force parts)))
        parts
  | FinCmp (operation, left, right, modulus, _flipped) ->
      let operation =
        match operation with
        | Lt -> builder.operations.less
        | Le -> builder.operations.less_equal
      in
      compare_values builder operation (Fin modulus)
        (lower_expr builder env left) (lower_expr builder env right)
        "finite comparison"
  | FinEq (left, right, modulus) ->
      compare_values builder builder.operations.equal (Fin modulus)
        (lower_expr builder env left) (lower_expr builder env right)
        "finite equality"
  | Cmp (operation, left, right, _flipped) ->
      let left = lower_expr builder env left in
      let right = lower_expr builder env right in
      require_kind Float left "float comparison";
      require_kind Float right "float comparison";
      let compare_constants left right =
        match ac_constant builder.arithmetic left,
              ac_constant builder.arithmetic right with
        | Some left, Some right ->
            let result =
              match operation with
              | Lt -> left < right
              | Le -> left <= right
            in
            Circuit_ir.const builder.arithmetic (if result then 1.0 else 0.0)
        | _ ->
            fail
              "parameter-dependent float comparisons must be discretized before circuit compilation"
      in
      let comparison = Circuit_dd.make_binary compare_constants in
      make_value builder Bool
        ~support:(RvSet.union left.support right.support)
        (lazy
           [ Circuit_dd.apply2 builder.decisions comparison
               (materialize builder left) (materialize builder right)
           ])
  | And (left, right) ->
      compare_values builder builder.operations.bool_and Bool
        (lower_expr builder env left) (lower_expr builder env right)
        "boolean conjunction"
  | Or (left, right) ->
      compare_values builder builder.operations.bool_or Bool
        (lower_expr builder env left) (lower_expr builder env right)
        "boolean disjunction"
  | Not expression ->
      let value = lower_expr builder env expression in
      require_kind Bool value "boolean negation";
      make_value builder Bool
        ~support:value.support
        (lazy
           [ Circuit_dd.map builder.decisions builder.operations.bool_not
               (only_part value "boolean negation")
           ])
  | If (condition, if_true, if_false) ->
      let condition = lower_expr builder env condition in
      require_kind Bool condition "conditional";
      let condition_root = only_part condition "conditional" in
      (match Circuit_dd.lookup builder.decisions condition_root with
       | Circuit_dd.Leaf boolean ->
           (match boolean_constant builder.arithmetic boolean with
            | Some true -> lower_expr builder env if_true
            | Some false -> lower_expr builder env if_false
            | None -> fail "conditional reached a non-boolean DD leaf")
       | Circuit_dd.Choice _ ->
           let if_true = lower_expr builder env if_true in
           let if_false = lower_expr builder env if_false in
           if if_true.kind <> if_false.kind then
             fail
               (Printf.sprintf "conditional branches have types %s and %s"
                  (kind_name if_true.kind) (kind_name if_false.kind));
           let support =
             RvSet.union condition.support
               (RvSet.union if_true.support if_false.support)
           in
           let parts =
             lazy
               [ Circuit_dd.ite builder.decisions builder.arithmetic
                   condition_root
                   (materialize builder if_true)
                   (materialize builder if_false)
               ]
           in
           (match if_true.kind with
            | Float ->
                let condition_is_independent =
                  RvSet.is_empty
                    (RvSet.inter condition.support
                       (RvSet.union if_true.support if_false.support))
                in
                let result_mean =
                  lazy
                    (let true_mean = mean if_true "conditional" in
                     let false_mean = mean if_false "conditional" in
                     if true_mean = false_mean then true_mean
                     else if condition_is_independent then
                       let probability_true =
                         eliminate_dd builder condition_root
                       in
                       let probability_false =
                         Circuit_ir.sub builder.arithmetic builder.one
                           probability_true
                       in
                       Circuit_ir.add builder.arithmetic
                         (Circuit_ir.mul builder.arithmetic
                            probability_true true_mean)
                         (Circuit_ir.mul builder.arithmetic
                            probability_false false_mean)
                     else
                       eliminate_parts builder (Lazy.force parts))
                in
                make_value builder Float ~support ~mean:result_mean parts
            | Bool | Fin _ ->
                make_value builder if_true.kind ~support parts))
  | DiscreteCase cases -> lower_discrete builder env cases
  | Sample _ -> unsupported "residual Sample"
  | Observe _ -> unsupported "Observe"
  | Fun _ | FuncApp _ -> unsupported "functions"
  | Fix _ -> unsupported "recursion"
  | Ref _ | Deref _ | Assign _ | Seq _ -> unsupported "references and mutation"
  | Nil | Cons _ | MatchList _ -> unsupported "lists"
  | Pair _ | First _ | Second _ -> unsupported "pairs"
  | Unit -> unsupported "unit values"
  | SpecialFunc _ -> unsupported "special functions"
  | Cdf _ | CdfExpr _ -> unsupported "CDF expressions"
  | RuntimeError _ -> unsupported "runtime errors"
  | Reset _ | Shift _ -> unsupported "internal reverse-AD operators"

and lower_discrete builder env cases =
  match cases with
  | [] -> fail "encountered an empty DiscreteCase"
  | _ ->
      let arity = List.length cases in
      let variable = Circuit_dd.fresh_rv builder.decisions ~arity in
      let lower_probability (_branch, ((_, effect, _) as probability)) =
        if effect_is_prob effect then
          fail "a DiscreteCase probability contains a fresh random choice";
        let probability = lower_expr builder env probability in
        require_kind Float probability "DiscreteCase probability";
        if not (is_deterministic probability) then
          fail
            "a DiscreteCase probability depends on an earlier random choice";
        mean probability "DiscreteCase probability"
      in
      let weights = Array.of_list (List.map lower_probability cases) in
      Hashtbl.add builder.choices variable { weights };
      let branches =
        Array.of_list
          (List.map
             (fun (branch, _probability) -> lower_expr builder env branch)
             cases)
      in
      let first = branches.(0) in
      Array.iter
        (fun branch ->
           if branch.kind <> first.kind then
             fail "DiscreteCase branches have different result types")
        branches;
      let support =
        Array.fold_left
          (fun support branch -> RvSet.union support branch.support)
          (RvSet.singleton variable) branches
      in
      let parts =
        lazy
          (let children = Array.map (materialize builder) branches in
           let root =
             try Circuit_dd.choice builder.decisions variable children with
             | Invalid_argument message ->
                 fail
                   ("unsupported random dependence inside DiscreteCase branches: "
                    ^ message)
           in
           [ root ])
      in
      (match first.kind with
       | Float ->
           let result_mean =
             lazy
               (Array.mapi
                  (fun index branch ->
                     Circuit_ir.mul builder.arithmetic weights.(index)
                       (mean branch "DiscreteCase branch"))
                  branches
                |> Circuit_ir.sum builder.arithmetic)
           in
           make_value builder Float ~support ~mean:result_mean parts
       | Bool | Fin _ -> make_value builder first.kind ~support parts)

let lower expression =
  let builder = create_builder () in
  let result = lower_expr builder StringMap.empty expression in
  (match result.kind with
   | Float | Bool -> ()
   | Fin _ -> fail "top-level circuit result must be float- or bool-valued");
  let result_parts =
    match result.kind with
    | Float ->
        [ Circuit_dd.leaf builder.decisions
            (mean result "top-level circuit result")
        ]
    | Bool -> List.rev (Lazy.force result.parts)
    | Fin _ -> assert false
  in
  { arithmetic = builder.arithmetic
  ; decisions = builder.decisions
  ; choices = builder.choices
  ; result_kind = result.kind
  ; result_parts
  ; additive_terms = result.additive_terms
  ; elimination_memo = builder.elimination_memo
  }
