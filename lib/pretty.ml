open Ast
open Lats

(* ANSI color codes for syntax highlighting *)
let keyword_color = "\027[1;34m"  (* Bold Blue *)
let operator_color = "\027[1;31m" (* Bold Red *)
let number_color = "\027[0;32m"   (* Green *)
let variable_color = "\027[0;33m" (* Yellow *)
let reset_color = "\027[0m"       (* Reset *)
let paren_color = "\027[1;37m"   (* Bold White *)
let type_color = "\027[1;35m"    (* Bold Magenta *)
let bracket_color = "\027[1;36m" (* Bold Cyan *)

(* Pretty printer for continuous distributions (used in error
   messages only). *)
let string_of_cdistr = function
| Distributions.Uniform (lo, hi) ->
    Printf.sprintf "%suniform%s(%s%g%s, %s%g%s)"
        keyword_color reset_color number_color lo reset_color number_color hi reset_color
| Distributions.Gaussian (mean, std) ->
    Printf.sprintf "%sgaussian%s(%s%g%s, %s%g%s)"
        keyword_color reset_color number_color mean reset_color number_color std reset_color
| Distributions.Exponential rate ->
    Printf.sprintf "%sexponential%s(%s%g%s)"
        keyword_color reset_color number_color rate reset_color
| Distributions.Beta (alpha, beta) ->
    Printf.sprintf "%sbeta%s(%s%g%s, %s%g%s)"
        keyword_color reset_color number_color alpha reset_color number_color beta reset_color
| Distributions.LogNormal (mu, sigma) ->
    Printf.sprintf "%slognormal%s(%s%g%s, %s%g%s)"
        keyword_color reset_color number_color mu reset_color number_color sigma reset_color
| Distributions.Gamma (shape, scale) ->
    Printf.sprintf "%sgamma%s(%s%g%s, %s%g%s)"
        keyword_color reset_color number_color shape reset_color number_color scale reset_color
| Distributions.Laplace scale ->
    Printf.sprintf "%slaplace%s(%s%g%s)"
        keyword_color reset_color number_color scale reset_color
| Distributions.Cauchy scale ->
    Printf.sprintf "%scauchy%s(%s%g%s)"
        keyword_color reset_color number_color scale reset_color
| Distributions.Weibull (a, b) ->
    Printf.sprintf "%sweibull%s(%s%g%s, %s%g%s)"
        keyword_color reset_color number_color a reset_color number_color b reset_color
| Distributions.TDist nu ->
    Printf.sprintf "%stdist%s(%s%g%s)"
        keyword_color reset_color number_color nu reset_color
| Distributions.Chi2 nu ->
    Printf.sprintf "%schi2%s(%s%g%s)"
        keyword_color reset_color number_color nu reset_color
| Distributions.Logistic scale ->
    Printf.sprintf "%slogistic%s(%s%g%s)"
        keyword_color reset_color number_color scale reset_color
| _ -> "<unsupported distribution>"

(* ============== Plain (uncolored) pretty-printer for canonical
   identities of symbolic expressions.  Used only as a stable
   string key for sym-bags / cut-bags. ============== *)

let rec string_of_expr_plain (ExprNode e : expr) : string =
  match e with
  | Const f -> Printf.sprintf "%g" f
  | BoolConst b -> string_of_bool b
  | Var x -> x
  | Let (x, e1, e2) ->
      Printf.sprintf "let %s = %s in %s" x (string_of_expr_plain e1) (string_of_expr_plain e2)
  | Sample d -> string_of_sample_plain d
  | DiscreteCase cases ->
      let parts = List.map (fun (b, p) ->
        Printf.sprintf "%s: %s" (string_of_expr_plain p) (string_of_expr_plain b)) cases
      in
      Printf.sprintf "discrete(%s)" (String.concat ", " parts)
  | Cmp (op, e1, e2, flipped) ->
      let s, l, r =
        if flipped then
          (match op with Ast.Lt -> ">", e2, e1 | Ast.Le -> ">=", e2, e1)
        else
          (match op with Ast.Lt -> "<", e1, e2 | Ast.Le -> "<=", e1, e2)
      in
      Printf.sprintf "(%s %s %s)" (string_of_expr_plain l) s (string_of_expr_plain r)
  | FinCmp (op, e1, e2, n, flipped) ->
      let s, l, r =
        if flipped then
          (match op with Ast.Lt -> ">#", e2, e1 | Ast.Le -> ">=#", e2, e1)
        else
          (match op with Ast.Lt -> "<#", e1, e2 | Ast.Le -> "<=#", e1, e2)
      in
      Printf.sprintf "(%s %s%d %s)" (string_of_expr_plain l) s n (string_of_expr_plain r)
  | And (e1, e2) -> Printf.sprintf "(%s && %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | Or (e1, e2) -> Printf.sprintf "(%s || %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | Not e1 -> Printf.sprintf "(not %s)" (string_of_expr_plain e1)
  | If (e1, e2, e3) ->
      Printf.sprintf "if %s then %s else %s" (string_of_expr_plain e1) (string_of_expr_plain e2) (string_of_expr_plain e3)
  | Pair (e1, e2) -> Printf.sprintf "(%s, %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | First e1 -> Printf.sprintf "(fst %s)" (string_of_expr_plain e1)
  | Second e1 -> Printf.sprintf "(snd %s)" (string_of_expr_plain e1)
  | Fun (x, e1) -> Printf.sprintf "fun %s -> %s" x (string_of_expr_plain e1)
  | FuncApp (e1, e2) -> Printf.sprintf "(%s %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | Fix (f, x, e1) -> Printf.sprintf "fix %s %s := %s" f x (string_of_expr_plain e1)
  | FinConst (k, n) -> Printf.sprintf "%d#%d" k n
  | FinEq (e1, e2, n) -> Printf.sprintf "(%s ==#%d %s)" (string_of_expr_plain e1) n (string_of_expr_plain e2)
  | Observe e1 -> Printf.sprintf "observe(%s)" (string_of_expr_plain e1)
  | Nil -> "nil"
  | Cons (e1, e2) -> Printf.sprintf "(%s :: %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | MatchList (e1, en, y, ys, ec) ->
      Printf.sprintf "match %s with | nil -> %s | %s :: %s -> %s end"
        (string_of_expr_plain e1) (string_of_expr_plain en) y ys (string_of_expr_plain ec)
  | Ref e1 -> Printf.sprintf "ref %s" (string_of_expr_plain e1)
  | Deref e1 -> Printf.sprintf "!%s" (string_of_expr_plain e1)
  | Assign (e1, e2) -> Printf.sprintf "(%s := %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | Seq (e1, e2) -> Printf.sprintf "(%s; %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | Unit -> "()"
  | RuntimeError s -> Printf.sprintf "RUNTIME_ERROR(\"%s\")" s
  | Reset e1 -> Printf.sprintf "reset <%s>" (string_of_expr_plain e1)
  | Shift (k, e1) -> Printf.sprintf "shift %s in %s" k (string_of_expr_plain e1)
  | Add (e1, e2) -> Printf.sprintf "(%s + %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | Sub (e1, e2) -> Printf.sprintf "(%s - %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | Mul (e1, e2) -> Printf.sprintf "(%s * %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | Div (e1, e2) -> Printf.sprintf "(%s / %s)" (string_of_expr_plain e1) (string_of_expr_plain e2)
  | SpecialFunc (name, args) ->
      Printf.sprintf "%s(%s)" name (String.concat ", " (List.map string_of_expr_plain args))
  | Cdf (d, e1) -> Printf.sprintf "CDF(%s, %s)" (string_of_sample_plain d) (string_of_expr_plain e1)
  | CdfExpr (k, e1) -> Printf.sprintf "CDF(%s, %s)" (string_of_expr_plain k) (string_of_expr_plain e1)

and string_of_sample_plain = function
  | Distr1 (kind, e1) ->
      Printf.sprintf "%s(%s)" (Distributions.string_of_single_arg_dist_kind kind) (string_of_expr_plain e1)
  | Distr2 (kind, e1, e2) ->
      Printf.sprintf "%s(%s, %s)" (Distributions.string_of_two_arg_dist_kind kind) (string_of_expr_plain e1) (string_of_expr_plain e2)

(* ============== Colored pretty-printer (the original) ============= *)

let rec string_of_expr_indented ?(indent=0) e =
  string_of_expr_node ~indent e
and string_of_aexpr_indented ?(indent=0) ae =
  string_of_aexpr_node ~indent ae
and string_of_texpr_indented ?(indent=0) ((ty, eff, aexpr) : texpr) : string =
  let aexpr_str = string_of_aexpr_indented ~indent aexpr in
  match aexpr with
  | TAExprNode (FinConst (_, _)) -> aexpr_str
  | _ ->
      let eff_str =
        match Ast.force_effect eff with
        | Pure | EMeta _ -> ""
        | Prob -> Printf.sprintf " %s!prob%s" type_color reset_color
      in
      Printf.sprintf "%s(%s%s : %s%s%s)%s"
        paren_color reset_color aexpr_str (string_of_ty ty) eff_str paren_color reset_color

and string_of_expr_node ?(indent=0) (ExprNode expr_node) : string =
  match expr_node with
  | Const f ->
      Printf.sprintf "%s%g%s" number_color f reset_color
  | BoolConst b ->
      Printf.sprintf "%s%b%s" keyword_color b reset_color
  | Var x -> Printf.sprintf "%s%s%s" variable_color x reset_color
  | Let (x, e1, e2) ->
      let indent_str = String.make indent ' ' in
      let e1_str = string_of_expr_indented ~indent:(indent+2) e1 in
      let e2_str = string_of_expr_indented ~indent:(indent+2) e2 in
      Printf.sprintf "%slet%s %s%s%s = %s %sin%s\n%s%s"
        keyword_color reset_color variable_color x reset_color e1_str
        keyword_color reset_color indent_str e2_str
  | Sample dist_exp -> string_of_sample ~indent dist_exp
  | DiscreteCase cases ->
      let format_case (expr, prob) =
        Printf.sprintf "%s: %s"
          (string_of_expr_indented ~indent prob)
          (string_of_expr_indented ~indent expr)
      in
      Printf.sprintf "%sdiscrete%s(%s%s%s)"
        keyword_color reset_color paren_color
        (String.concat ", " (List.map format_case cases))
        reset_color
  | Cmp (cmp_op, e1, e2, flipped) ->
      let op_str, left_expr, right_expr =
        if flipped then
          match cmp_op with
          | Ast.Lt -> ">", e2, e1
          | Ast.Le -> ">=", e2, e1
        else
          match cmp_op with
          | Ast.Lt -> "<", e1, e2
          | Ast.Le -> "<=", e1, e2
      in
      Printf.sprintf "%s %s%s%s %s"
        (string_of_expr_indented ~indent left_expr) operator_color op_str reset_color (string_of_expr_indented ~indent right_expr)
  | FinCmp (cmp_op, e1, e2, n, flipped) ->
      let op_str, left_expr, right_expr =
        if flipped then
          match cmp_op with
          | Ast.Lt -> ">#", e2, e1
          | Ast.Le -> ">=#", e2, e1
        else
          match cmp_op with
          | Ast.Lt -> "<#", e1, e2
          | Ast.Le -> "<=#", e1, e2
      in
      Printf.sprintf "%s %s%s%s%s%d%s %s"
        (string_of_expr_indented ~indent left_expr) operator_color op_str reset_color type_color n reset_color (string_of_expr_indented ~indent right_expr)
  | Not e1 ->
      Printf.sprintf "(%snot%s %s)"
        operator_color reset_color (string_of_expr_indented ~indent e1)
  | And (e1, e2) ->
      Printf.sprintf "%s %s&&%s %s"
        (string_of_expr_indented ~indent e1) operator_color reset_color (string_of_expr_indented ~indent e2)
  | Or (e1, e2) ->
      Printf.sprintf "%s %s||%s %s"
        (string_of_expr_indented ~indent e1) operator_color reset_color (string_of_expr_indented ~indent e2)
  | If (e1, e2, e3) ->
      let indent_str = String.make indent ' ' in
      let next_indent_str = String.make (indent+2) ' ' in
      let e1_str = string_of_expr_indented ~indent e1 in
      let e2_str = string_of_expr_indented ~indent:(indent+2) e2 in
      let e3_str = string_of_expr_indented ~indent:(indent+2) e3 in
      Printf.sprintf "%sif%s %s %sthen%s\n%s%s\n%s%selse%s\n%s%s"
        keyword_color reset_color e1_str keyword_color reset_color
        next_indent_str e2_str indent_str keyword_color reset_color next_indent_str e3_str
  | Pair (e1, e2) ->
      let e1_str = string_of_expr_indented ~indent e1 in
      let e2_str = string_of_expr_indented ~indent e2 in
      Printf.sprintf "(%s, %s)" e1_str e2_str
  | First e ->
      let e_str = string_of_expr_indented ~indent e in
      Printf.sprintf "(%sfst%s %s)" keyword_color reset_color e_str
  | Second e ->
      let e_str = string_of_expr_indented ~indent e in
      Printf.sprintf "(%ssnd%s %s)" keyword_color reset_color e_str
  | Fun (x, e) ->
      let e_str = string_of_expr_indented ~indent:(indent+2) e in
      Printf.sprintf "%sfun%s %s%s%s %s->%s %s"
        keyword_color reset_color variable_color x reset_color
        operator_color reset_color e_str
  | FuncApp (e1, e2) ->
      let e1_str = string_of_expr_indented ~indent e1 in
      let e2_str = string_of_expr_indented ~indent e2 in
      Printf.sprintf "(%s %s)" e1_str e2_str
  | Fix (f, x, e) ->
      let e_str = string_of_expr_indented ~indent:(indent+2) e in
      Printf.sprintf "%sfix%s %s%s%s %s%s%s %s:=%s %s"
        keyword_color reset_color variable_color f reset_color variable_color x reset_color
        operator_color reset_color e_str
  | FinConst (k, n) ->
      Printf.sprintf "%s%d%s%s#%d%s" number_color k reset_color type_color n reset_color
  | FinEq (e1, e2, n) ->
      Printf.sprintf "%s %s==%s%s#%d%s %s"
        (string_of_expr_indented ~indent e1) operator_color reset_color type_color n reset_color (string_of_expr_indented ~indent e2)
  | Observe e1 ->
      let e1_str = string_of_expr_indented ~indent e1 in
      Printf.sprintf "%sobserve%s (%s)"
        keyword_color reset_color e1_str
  | Nil -> Printf.sprintf "%snil%s" keyword_color reset_color
  | Cons (e1, e2) ->
      Printf.sprintf "%s %s::%s %s"
        (string_of_expr_indented ~indent e1) operator_color reset_color (string_of_expr_indented ~indent e2)
  | MatchList (e1, e_nil, y, ys, e_cons) ->
      let e1_str = string_of_expr_indented ~indent:(indent+2) e1 in
      let e_nil_str = string_of_expr_indented ~indent:(indent+2) e_nil in
      let e_cons_str = string_of_expr_indented ~indent:(indent+4) e_cons in
      Printf.sprintf "%smatch%s %s %swith%s\n%s  | %snil%s %s->%s %s\n%s  | %s%s%s %s::%s %s%s%s %s->%s %s\n%s%send%s"
        keyword_color reset_color e1_str keyword_color reset_color
        (String.make indent ' ') keyword_color reset_color operator_color reset_color e_nil_str
        (String.make indent ' ') variable_color y reset_color operator_color reset_color variable_color ys reset_color operator_color reset_color e_cons_str
        (String.make indent ' ') keyword_color reset_color
  | Ref e1 ->
      Printf.sprintf "%sref%s %s"
        keyword_color reset_color (string_of_expr_indented ~indent e1)
  | Deref e1 ->
      Printf.sprintf "%s!%s%s"
        operator_color reset_color (string_of_expr_indented ~indent e1)
  | Assign (e1, e2) ->
      Printf.sprintf "%s %s:=%s %s"
        (string_of_expr_indented ~indent e1) operator_color reset_color (string_of_expr_indented ~indent e2)
  | Seq (e1, e2) ->
      Printf.sprintf "%s %s;%s %s"
        (string_of_expr_indented ~indent e1) operator_color reset_color (string_of_expr_indented ~indent e2)
  | Unit -> Printf.sprintf "%s()%s" keyword_color reset_color
  | RuntimeError s -> Printf.sprintf "%sRUNTIME_ERROR%s(\"%s%s%s\")" operator_color reset_color variable_color s reset_color
  | Reset e1 ->
      Printf.sprintf "%sreset%s <%s>"
        keyword_color reset_color (string_of_expr_indented ~indent:(indent+2) e1)
  | Shift (k, e1) ->
      Printf.sprintf "%sshift%s %s%s%s %sin%s %s"
        keyword_color reset_color variable_color k reset_color
        keyword_color reset_color (string_of_expr_indented ~indent:(indent+2) e1)
  | Add (e1, e2) ->
      Printf.sprintf "(%s %s+%s %s)"
        (string_of_expr_indented ~indent e1) operator_color reset_color (string_of_expr_indented ~indent e2)
  | Sub (e1, e2) ->
      Printf.sprintf "(%s %s-%s %s)"
        (string_of_expr_indented ~indent e1) operator_color reset_color (string_of_expr_indented ~indent e2)
  | Mul (e1, e2) ->
      Printf.sprintf "(%s %s*%s %s)"
        (string_of_expr_indented ~indent e1) operator_color reset_color (string_of_expr_indented ~indent e2)
  | Div (e1, e2) ->
      Printf.sprintf "(%s %s/%s %s)"
        (string_of_expr_indented ~indent e1) operator_color reset_color (string_of_expr_indented ~indent e2)
  | SpecialFunc (name, args) ->
      Printf.sprintf "%s%s%s(%s)"
        keyword_color name reset_color
        (String.concat ", " (List.map (string_of_expr_indented ~indent) args))
  | Cdf (d, e1) ->
      Printf.sprintf "%sCDF%s(%s, %s)"
        keyword_color reset_color (string_of_sample ~indent d) (string_of_expr_indented ~indent e1)
  | CdfExpr (k, e1) ->
      Printf.sprintf "%sCDF%s(%s, %s)"
        keyword_color reset_color (string_of_expr_indented ~indent k) (string_of_expr_indented ~indent e1)

and string_of_sample ?(indent=0) dist_exp =
  match dist_exp with
  | Distr1 (kind, e1) ->
      Printf.sprintf "%s%s%s(%s)"
        keyword_color (Distributions.string_of_single_arg_dist_kind kind) reset_color (string_of_expr_indented ~indent e1)
  | Distr2 (kind, e1, e2) ->
      Printf.sprintf "%s%s%s(%s, %s)"
        keyword_color (Distributions.string_of_two_arg_dist_kind kind) reset_color (string_of_expr_indented ~indent e1) (string_of_expr_indented ~indent e2)

and string_of_aexpr_node ?(indent=0) (TAExprNode ae_node) : string =
 match ae_node with
  | Const f ->
      Printf.sprintf "%s%g%s" number_color f reset_color
  | BoolConst b ->
      Printf.sprintf "%s%b%s" keyword_color b reset_color
  | Var x -> Printf.sprintf "%s%s%s" variable_color x reset_color
  | Let (x, te1, te2) ->
      let indent_str = String.make indent ' ' in
      let e1_str = string_of_texpr_indented ~indent:(indent+2) te1 in
      let e2_str = string_of_texpr_indented ~indent:(indent+2) te2 in
      Printf.sprintf "%slet%s %s%s%s = %s %sin%s\n%s%s"
        keyword_color reset_color variable_color x reset_color e1_str
        keyword_color reset_color indent_str e2_str
  | Sample dist_exp -> string_of_asample ~indent dist_exp
  | DiscreteCase cases ->
      let format_case (texpr, prob) =
        Printf.sprintf "%s: %s"
          (string_of_texpr_indented ~indent prob)
          (string_of_texpr_indented ~indent texpr)
      in
      Printf.sprintf "%sdiscrete%s(%s%s%s)"
        keyword_color reset_color paren_color
        (String.concat ", " (List.map format_case cases))
        reset_color
  | Cmp (cmp_op, te1, te2, flipped) ->
      let op_str, left_expr, right_expr =
        if flipped then
          match cmp_op with
          | Ast.Lt -> ">", te2, te1
          | Ast.Le -> ">=", te2, te1
        else
          match cmp_op with
          | Ast.Lt -> "<", te1, te2
          | Ast.Le -> "<=", te1, te2
      in
      Printf.sprintf "%s %s%s%s %s"
        (string_of_texpr_indented ~indent left_expr) operator_color op_str reset_color (string_of_texpr_indented ~indent right_expr)
  | FinCmp (cmp_op, te1, te2, n, flipped) ->
      let op_str, left_expr, right_expr =
        if flipped then
          match cmp_op with
          | Ast.Lt -> ">#", te2, te1
          | Ast.Le -> ">=#", te2, te1
        else
          match cmp_op with
          | Ast.Lt -> "<#", te1, te2
          | Ast.Le -> "<=#", te1, te2
      in
      Printf.sprintf "%s %s%s%s%s%d%s %s"
        (string_of_texpr_indented ~indent left_expr) operator_color op_str reset_color type_color n reset_color (string_of_texpr_indented ~indent right_expr)
  | Not te1 ->
      Printf.sprintf "(%snot%s %s)"
        operator_color reset_color (string_of_texpr_indented ~indent te1)
  | And (te1, te2) ->
      Printf.sprintf "%s %s&&%s %s"
        (string_of_texpr_indented ~indent te1) operator_color reset_color (string_of_texpr_indented ~indent te2)
  | Or (te1, te2) ->
      Printf.sprintf "%s %s||%s %s"
        (string_of_texpr_indented ~indent te1) operator_color reset_color (string_of_texpr_indented ~indent te2)
  | If (te1, te2, te3) ->
      let indent_str = String.make indent ' ' in
      let next_indent_str = String.make (indent+2) ' ' in
      let e1_str = string_of_texpr_indented ~indent te1 in
      let e2_str = string_of_texpr_indented ~indent:(indent+2) te2 in
      let e3_str = string_of_texpr_indented ~indent:(indent+2) te3 in
      Printf.sprintf "%sif%s %s %sthen%s\n%s%s\n%s%selse%s\n%s%s"
        keyword_color reset_color e1_str keyword_color reset_color
        next_indent_str e2_str indent_str keyword_color reset_color next_indent_str e3_str
  | Pair (te1, te2) ->
      let e1_str = string_of_texpr_indented ~indent te1 in
      let e2_str = string_of_texpr_indented ~indent te2 in
      Printf.sprintf "(%s, %s)" e1_str e2_str
  | First te ->
      let e_str = string_of_texpr_indented ~indent te in
      Printf.sprintf "(%sfst%s %s)" keyword_color reset_color e_str
  | Second te ->
      let e_str = string_of_texpr_indented ~indent te in
      Printf.sprintf "(%ssnd%s %s)" keyword_color reset_color e_str
  | Fun (x, te) ->
      let e_str = string_of_texpr_indented ~indent:(indent+2) te in
      Printf.sprintf "%sfun%s %s%s%s %s->%s %s"
        keyword_color reset_color variable_color x reset_color
        operator_color reset_color e_str
  | FuncApp (te1, te2) ->
      let e1_str = string_of_texpr_indented ~indent te1 in
      let e2_str = string_of_texpr_indented ~indent te2 in
      Printf.sprintf "(%s %s)" e1_str e2_str
  | Fix (f, x, te) ->
      let te_str = string_of_texpr_indented ~indent:(indent+2) te in
      Printf.sprintf "%sfix%s %s%s%s %s%s%s %s:=%s %s"
        keyword_color reset_color variable_color f reset_color variable_color x reset_color
        operator_color reset_color te_str
  | FinConst (k, n) ->
      Printf.sprintf "%s%d%s%s#%d%s" number_color k reset_color type_color n reset_color
  | FinEq (te1, te2, n) ->
      Printf.sprintf "%s %s==%s%s#%d%s %s"
        (string_of_texpr_indented ~indent te1) operator_color reset_color type_color n reset_color (string_of_texpr_indented ~indent te2)
  | Observe te1 ->
      let e1_str = string_of_texpr_indented ~indent te1 in
      Printf.sprintf "%sobserve%s (%s)"
        keyword_color reset_color e1_str
  | Nil -> Printf.sprintf "%snil%s" keyword_color reset_color
  | Cons (te1, te2) ->
      Printf.sprintf "%s %s::%s %s"
        (string_of_texpr_indented ~indent te1) operator_color reset_color (string_of_texpr_indented ~indent te2)
  | MatchList (te1, te_nil, y, ys, te_cons) ->
      let te1_str = string_of_texpr_indented ~indent:(indent+2) te1 in
      let te_nil_str = string_of_texpr_indented ~indent:(indent+2) te_nil in
      let te_cons_str = string_of_texpr_indented ~indent:(indent+4) te_cons in
      Printf.sprintf "%smatch%s %s %swith%s\n%s  | %snil%s %s->%s %s\n%s  | %s%s%s %s::%s %s%s%s %s->%s %s\n%s%send%s"
        keyword_color reset_color te1_str keyword_color reset_color
        (String.make indent ' ') keyword_color reset_color operator_color reset_color te_nil_str
        (String.make indent ' ') variable_color y reset_color operator_color reset_color variable_color ys reset_color operator_color reset_color te_cons_str
        (String.make indent ' ') keyword_color reset_color
  | Ref te1 ->
      Printf.sprintf "%sref%s %s"
        keyword_color reset_color (string_of_texpr_indented ~indent te1)
  | Deref te1 ->
      Printf.sprintf "%s!%s%s"
        operator_color reset_color (string_of_texpr_indented ~indent te1)
  | Assign (te1, te2) ->
      Printf.sprintf "%s %s:=%s %s"
        (string_of_texpr_indented ~indent te1) operator_color reset_color (string_of_texpr_indented ~indent te2)
  | Seq (te1, te2) ->
      Printf.sprintf "%s %s;%s %s"
        (string_of_texpr_indented ~indent te1) operator_color reset_color (string_of_texpr_indented ~indent te2)
  | Unit -> Printf.sprintf "%s()%s" keyword_color reset_color
  | RuntimeError s -> Printf.sprintf "%sRUNTIME_ERROR%s(\"%s%s%s\")" operator_color reset_color variable_color s reset_color
  | Reset te1 ->
      Printf.sprintf "%sreset%s <%s>"
        keyword_color reset_color (string_of_texpr_indented ~indent:(indent+2) te1)
  | Shift (k, te1) ->
      Printf.sprintf "%sshift%s %s%s%s %sin%s %s"
        keyword_color reset_color variable_color k reset_color
        keyword_color reset_color (string_of_texpr_indented ~indent:(indent+2) te1)
  | Add (te1, te2) ->
      Printf.sprintf "(%s %s+%s %s)"
        (string_of_texpr_indented ~indent te1) operator_color reset_color (string_of_texpr_indented ~indent te2)
  | Sub (te1, te2) ->
      Printf.sprintf "(%s %s-%s %s)"
        (string_of_texpr_indented ~indent te1) operator_color reset_color (string_of_texpr_indented ~indent te2)
  | Mul (te1, te2) ->
      Printf.sprintf "(%s %s*%s %s)"
        (string_of_texpr_indented ~indent te1) operator_color reset_color (string_of_texpr_indented ~indent te2)
  | Div (te1, te2) ->
      Printf.sprintf "(%s %s/%s %s)"
        (string_of_texpr_indented ~indent te1) operator_color reset_color (string_of_texpr_indented ~indent te2)
  | SpecialFunc (name, args) ->
      Printf.sprintf "%s%s%s(%s)"
        keyword_color name reset_color
        (String.concat ", " (List.map (string_of_texpr_indented ~indent) args))
  | Cdf (d, te1) ->
      Printf.sprintf "%sCDF%s(%s, %s)"
        keyword_color reset_color (string_of_asample ~indent d) (string_of_texpr_indented ~indent te1)
  | CdfExpr (k, te1) ->
      Printf.sprintf "%sCDF%s(%s, %s)"
        keyword_color reset_color (string_of_texpr_indented ~indent k) (string_of_texpr_indented ~indent te1)

and string_of_ty = function
  | TBool -> Printf.sprintf "%sbool%s" type_color reset_color
  | TFloat (cut_bag_ref, const_bag_ref, sym_bag_ref) ->
      let bounds_str =
        match Ast.CutLat.get cut_bag_ref with
        | Top -> "T"
        | Finite bound_set ->
            if Ast.CutSet.is_empty bound_set then ""
            else
              let string_of_cv = function
                | CVConst c -> Printf.sprintf "%g" c
                | CVSym (s, _) -> s
              in
              let string_of_cut = function
                | Less cv -> Printf.sprintf "<%s" (string_of_cv cv)
                | LessEq cv -> Printf.sprintf "<=%s" (string_of_cv cv)
              in
              let elements = Ast.CutSet.elements bound_set in
              String.concat "," (List.map string_of_cut elements)
      in
      let consts_str =
        match FloatLat.get const_bag_ref with
        | Top -> "T"
        | Finite float_set ->
            if FloatSet.is_empty float_set then ""
            else
              let elements = FloatSet.elements float_set in
              String.concat "," (List.map (Printf.sprintf "%g") elements)
      in
      let syms_str =
        match Ast.SymLat.get sym_bag_ref with
        | Top -> "T"
        | Finite sym_set ->
            if Ast.SymSet.is_empty sym_set then ""
            else
              let elements = Ast.SymSet.elements sym_set in
              String.concat "," (List.map (fun (s, _) -> s) elements)
      in
      let content_str =
        match bounds_str, consts_str, syms_str with
        | "", "", "" -> ""
        | b, "", "" -> Printf.sprintf "%s[%s]%s" type_color b reset_color
        | "", c, "" -> Printf.sprintf "%s[; %s]%s" type_color c reset_color
        | "", "", s -> Printf.sprintf "%s[;; %s]%s" type_color s reset_color
        | b, c, ""  -> Printf.sprintf "%s[%s; %s]%s" type_color b c reset_color
        | b, "", s  -> Printf.sprintf "%s[%s;; %s]%s" type_color b s reset_color
        | "", c, s  -> Printf.sprintf "%s[; %s; %s]%s" type_color c s reset_color
        | b, c, s   -> Printf.sprintf "%s[%s; %s; %s]%s" type_color b c s reset_color
      in
      Printf.sprintf "%sfloat%s%s" type_color reset_color content_str
  | TPair (t1, t2) ->
        Printf.sprintf "%s(%s * %s)%s"
          bracket_color (string_of_ty t1) (string_of_ty t2) reset_color
  | TFun (t1, eff, t2) ->
        let arrow =
          match Ast.force_effect eff with
          | Pure | EMeta _ -> "->"
          | Prob -> "~>"
        in
        Printf.sprintf "%s(%s %s %s)%s"
          bracket_color (string_of_ty t1) arrow (string_of_ty t2) reset_color
  | TFin n ->
        Printf.sprintf "%s#%d%s" type_color n reset_color
  | TUnit -> Printf.sprintf "%sunit%s" type_color reset_color
  | TList t -> Printf.sprintf "%slist%s %s" type_color reset_color (string_of_ty t)
  | TRef t -> Printf.sprintf "%s%s ref%s" type_color (string_of_ty t) reset_color
  | TMeta r ->
        match !r with
        | Known t -> string_of_ty t
        | Unknown _ -> "?"
and string_of_asample ?(indent=0) dist_exp =
  match dist_exp with
  | Distr1 (kind, te1) ->
      Printf.sprintf "%s%s%s(%s)"
        keyword_color (Distributions.string_of_single_arg_dist_kind kind) reset_color (string_of_texpr_indented ~indent te1)
  | Distr2 (kind, te1, te2) ->
      Printf.sprintf "%s%s%s(%s, %s)"
        keyword_color (Distributions.string_of_two_arg_dist_kind kind) reset_color (string_of_texpr_indented ~indent te1) (string_of_texpr_indented ~indent te2)

(* Wrappers *)
let string_of_expr expr =
  string_of_expr_indented expr

let string_of_texpr texpr =
  string_of_texpr_indented texpr

let string_of_aexpr aexpr =
  string_of_aexpr_indented aexpr

let rec expr_list_elements (ExprNode e) =
  match e with
  | Nil -> Some []
  | Cons (hd, tl) ->
      Option.map (fun rest -> hd :: rest) (expr_list_elements tl)
  | _ -> None

let string_of_labeled_expr_list labels expr_list =
  match expr_list_elements expr_list with
  | Some exprs when List.length labels = List.length exprs ->
      List.map2
        (fun label expr ->
           "d" ^ label ^ " = " ^ string_of_expr expr)
        labels
        exprs
      |> String.concat "; "
      |> Printf.sprintf "(%s)"
  | _ -> string_of_expr expr_list

let string_of_dual_with_labeled_expr_list labels = function
  | ExprNode (Pair (primal, gradient)) ->
      Printf.sprintf
        "(%s, %s)"
        (string_of_expr primal)
        (string_of_labeled_expr_list labels gradient)
  | expr -> string_of_expr expr

let string_of_float_list (l : float list) : string =
  "[" ^ (String.concat "; " (List.map (Printf.sprintf "%g") l)) ^ "]"
