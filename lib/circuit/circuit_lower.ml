(** Lowering from the typed, discretized Slice AST to arithmetic circuits and
    reduced decision diagrams.

    Float values are represented as a reverse-ordered list of additive DD
    components.  Addition merely concatenates those components; it does not
    take the product of their
    random-variable supports.  Elimination can consequently use linearity of
    expectation and eliminate each component independently.  Non-linear
    operations (multiplication and division) combine/materialize components as
    required.

    Boolean and finite values always have exactly one component.  At DD leaves
    they are encoded as arithmetic constants: false/true as 0/1 and a finite
    value [k#n] as [float k].  They are consumed during lowering, so the final
    arithmetic circuit remains float-only. *)

open Ast

module StringMap = Map.Make (String)

type value_kind =
  | Float
  | Bool
  | Fin of int

type value =
  { kind : value_kind
  ; parts : Circuit_dd.dd_id list
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
  }

type builder =
  { arithmetic : Circuit_ir.t
  ; decisions : Circuit_dd.t
  ; choices : (Circuit_dd.rv_id, choice_weights) Hashtbl.t
  ; operations : operations
  ; zero : Circuit_ir.ac_id
  ; one : Circuit_ir.ac_id
  ; zero_dd : Circuit_dd.dd_id
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
  }

let is_zero_part builder part =
  match Circuit_dd.lookup builder.decisions part with
  | Circuit_dd.Leaf id -> Circuit_ir.is_zero builder.arithmetic id
  | Circuit_dd.Choice _ -> false

let normalize_float_parts builder parts =
  match List.filter (fun part -> not (is_zero_part builder part)) parts with
  | [] -> [ builder.zero_dd ]
  | nonzero -> nonzero

let make_value builder kind parts =
  match kind with
  | Float -> { kind; parts = normalize_float_parts builder parts }
  | Bool | Fin _ ->
      (match parts with
       | [ _ ] -> { kind; parts }
       | _ -> fail (kind_name kind ^ " value did not have exactly one DD root"))

let singleton builder kind ac =
  make_value builder kind [ Circuit_dd.leaf builder.decisions ac ]

let only_part value context =
  match value.parts with
  | [ part ] -> part
  | _ -> fail (context ^ " requires a single decision diagram")

let materialize builder value =
  (* Components are accumulated in reverse source order so a left-associated
     chain of additions can prepend its usually-small right operand in O(1).
     Restore source order only when an actual DD addition is required. *)
  match List.rev value.parts with
  | [] -> builder.zero_dd
  | first :: rest ->
      List.fold_left
        (Circuit_dd.apply2 builder.decisions builder.operations.add)
        first rest

let multiply_values builder left right =
  require_kind Float left "multiplication";
  require_kind Float right "multiplication";
  let parts =
    List.fold_left
      (fun result left_part ->
         List.fold_left
           (fun result right_part ->
              Circuit_dd.apply2 builder.decisions builder.operations.mul
                left_part right_part
              :: result)
           result right.parts)
      [] left.parts
    |> List.rev
  in
  make_value builder Float parts

let compare_values builder operation expected left right context =
  require_kind expected left context;
  require_kind expected right context;
  make_value builder Bool
    [ Circuit_dd.apply2 builder.decisions operation
        (only_part left context) (only_part right context)
    ]

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
      make_value builder Float (right.parts @ left.parts)
  | Sub (left, right) ->
      let left = lower_expr builder env left in
      let right = lower_expr builder env right in
      require_kind Float left "subtraction";
      require_kind Float right "subtraction";
      let preserve_linearity () =
        let negated_right =
          List.map
            (Circuit_dd.map builder.decisions builder.operations.negate)
            right.parts
        in
        (* E[left - right] = sum E[left_i] + sum E[-right_i].  Keep those
           components separate rather than constructing their joint DD. *)
        make_value builder Float (negated_right @ left.parts)
      in
      (match left.parts, right.parts with
       | [ left_part ], [ right_part ] ->
           (match Circuit_dd.lookup builder.decisions left_part,
                  Circuit_dd.lookup builder.decisions right_part with
            | Circuit_dd.Leaf _, Circuit_dd.Leaf _ ->
                (* Keep deterministic expressions such as [1 - p] as one
                   compact subtraction node. *)
                make_value builder Float
                  [ Circuit_dd.apply2 builder.decisions builder.operations.sub
                      left_part right_part
                  ]
            | Circuit_dd.Leaf _, Circuit_dd.Choice _
            | Circuit_dd.Choice _, Circuit_dd.Leaf _
            | Circuit_dd.Choice _, Circuit_dd.Choice _ ->
                preserve_linearity ())
       | _ -> preserve_linearity ())
  | Mul (left, right) ->
      multiply_values builder
        (lower_expr builder env left)
        (lower_expr builder env right)
  | Div (left, right) ->
      let left = lower_expr builder env left in
      let right = lower_expr builder env right in
      require_kind Float left "division";
      require_kind Float right "division";
      make_value builder Float
        [ Circuit_dd.apply2 builder.decisions builder.operations.div
            (materialize builder left) (materialize builder right)
        ]
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
        [ Circuit_dd.apply2 builder.decisions comparison
            (materialize builder left) (materialize builder right)
        ]
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
        [ Circuit_dd.map builder.decisions builder.operations.bool_not
            (only_part value "boolean negation")
        ]
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
           if if_true.parts = if_false.parts then
             (* This is the DD reduction rule at the value-component level.
                Apply it before materializing either branch. *)
             if_true
           else
             make_value builder if_true.kind
               [ Circuit_dd.ite builder.decisions builder.arithmetic
                   condition_root
                   (materialize builder if_true)
                   (materialize builder if_false)
               ])
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
        let probability = materialize builder probability in
        match Circuit_dd.lookup builder.decisions probability with
        | Circuit_dd.Leaf weight -> weight
        | Circuit_dd.Choice _ ->
            fail
              "a DiscreteCase probability depends on an earlier random choice"
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
      let children = Array.map (materialize builder) branches in
      let root =
        try Circuit_dd.choice builder.decisions variable children with
        | Invalid_argument message ->
            fail
              ("unsupported random dependence inside DiscreteCase branches: "
               ^ message)
      in
      make_value builder first.kind [ root ]

let lower expression =
  let builder = create_builder () in
  let result = lower_expr builder StringMap.empty expression in
  (match result.kind with
   | Float | Bool -> ()
   | Fin _ -> fail "top-level circuit result must be float- or bool-valued");
  { arithmetic = builder.arithmetic
  ; decisions = builder.decisions
  ; choices = builder.choices
  ; result_kind = result.kind
  ; result_parts = List.rev result.parts
  }
