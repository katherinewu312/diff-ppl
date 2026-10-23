%{
open Ast
%}

%token <string> IDENT
%token <float> FLOAT
%token <int> INT
%token LET IN
%token IF THEN ELSE
%token TRUE FALSE
%token AND OR NOT
%token UNIFORM
%token GAUSSIAN
%token EXPONENTIAL
%token BETA
%token LOGNORMAL
%token DISCRETE
%token FLIP
%token FST SND
%token FUN ARROW
%token LESS
%token LESSEQ
%token GREATER
%token GREATEREQ
%token HASH
%token LT_HASH
%token LEQ_HASH
%token GT_HASH
%token GEQ_HASH
%token EQ_HASH
%token LPAREN RPAREN
%token COMMA
%token EQUAL
%token COLON
%token EOF
%token OBSERVE
%token FIX
%token COLON_EQUAL (* := *)
%token NIL          
%token CONS         (* :: *)
%token MATCH WITH END BAR
%token REF          (* ref *)
%token BANG         (* ! *)
%token SEMICOLON    (* ; *)
%token GAMMA
%token LAPLACE
%token CAUCHY
%token WEIBULL
%token TDIST
%token CHI2
%token LOGISTIC
%token PLUS
%token MINUS
%token TIMES
%token DIVIDE
%token RAYLEIGH
%token PARETO
%token GUMBELONE
%token GUMBELTWO
%token EXPPOW
%token POISSON
%token BINOMIAL

%start <Ast.expr> prog

(* Define types for non-terminals *) 
%type <Ast.expr> expr assign_expr cons_expr cmp_expr app_expr atomic_expr prefix_expr
%type <Ast.expr list> expr_comma_list (* New type for list of expressions *)
%type <unit> opt_bar
%type <float> number
%type <Ast.expr> arith_expr mul_expr

(* Operator precedence and associativity from commit 23e2e6c *)
%left ARROW             (* Function type arrow *)
%left SEMICOLON
%left PLUS MINUS
%left TIMES DIVIDE
%left OR                (* OR has lower precedence than AND *)
%left AND               (* AND has lower precedence than NOT/comparison *)
%right NOT              (* Unary NOT has high precedence *)
%right COMMA
%nonassoc LESS LESSEQ GREATER GREATEREQ LT_HASH LEQ_HASH GT_HASH GEQ_HASH EQ_HASH (* Comparison operators *)

%% 

prog: e = expr EOF { e };

/* Lowest precedence: LET, IF, FUN, FIX, MATCH (handled by structure) 
   then SEMICOLON, then assign_expr and higher operators */
expr:
    expr SEMICOLON expr 
    { ExprNode (Seq ($1, $3)) }
  | LET x = IDENT EQUAL e1 = expr IN e2 = expr
    { ExprNode (Let (x, e1, e2)) }
  | IF cond = expr THEN e1 = expr ELSE e2 = expr
    { ExprNode (If (cond, e1, e2)) }
  | FUN x = IDENT ARROW e = expr
    { ExprNode (Fun (x, e)) }
  | OBSERVE e = expr
    { ExprNode (Observe e) }
  | FIX f = IDENT x = IDENT COLON_EQUAL e = expr 
    { ExprNode (Fix (f, x, e)) }
  | MATCH e1 = expr WITH opt_bar NIL ARROW e_nil = expr BAR y = IDENT CONS ys = IDENT ARROW e_cons = expr END 
    { ExprNode (MatchList (e1, e_nil, y, ys, e_cons)) } 
  (*
  | FOR i = IDENT EQUAL n1 = expr TO n2 = expr DO body = expr
    { ExprNode (For (i, n1, n2, body)) }
  *)
  | assign_expr { $1 } /* Fallthrough to assign_expr */
  ;

/* Assignment level */
assign_expr:
  | prefix_expr COLON_EQUAL assign_expr { ExprNode (Assign ($1, $3)) }
  | or_expr { $1 } /* Fallthrough to or_expr, as per diff */
  ;

/* OR Level */
or_expr:
  | or_expr OR and_expr  { ExprNode (Or ($1, $3)) }
  | and_expr { $1 }     /* Fallthrough to and_expr */
  ;

/* AND Level */
and_expr:
  | and_expr AND not_expr { ExprNode (And ($1, $3)) }
  | not_expr { $1 }      /* Fallthrough to not_expr */
  ;

/* NOT Level */
not_expr:
  | NOT not_expr          { ExprNode (Not $2) }
  | cmp_expr { $1 }       /* Fallthrough to cmp_expr */
  ;

/* Comparison level */
cmp_expr:
  | cmp_expr LESS arith_expr     { ExprNode (Cmp (Lt, $1, $3, false)) }     (* Original < *)
  | cmp_expr LESSEQ arith_expr   { ExprNode (Cmp (Le, $1, $3, false)) }     (* Original <= *)
  | cmp_expr GREATER arith_expr  { ExprNode (Cmp (Lt, $3, $1, true)) }      (* Flipped > to < *)
  | cmp_expr GREATEREQ arith_expr { ExprNode (Cmp (Le, $3, $1, true)) }     (* Flipped >= to <= *)
  | arith_expr LT_HASH INT arith_expr { ExprNode (FinCmp (Lt, $1, $4, $3, false)) }   (* Original <#n *)
  | arith_expr LEQ_HASH INT arith_expr { ExprNode (FinCmp (Le, $1, $4, $3, false)) }  (* Original <=#n *)
  | arith_expr GT_HASH INT arith_expr { ExprNode (FinCmp (Lt, $4, $1, $3, true)) }    (* Flipped >#n to <#n *)
  | arith_expr GEQ_HASH INT arith_expr { ExprNode (FinCmp (Le, $4, $1, $3, true)) }   (* Flipped >=#n to <=#n *)
  | arith_expr EQ_HASH INT arith_expr { ExprNode (FinEq ($1, $4, $3)) }
  | arith_expr { $1 }            /* Fallthrough to arith_expr */
  ;

/* Additive arithmetic on float-typed expressions (left assoc) */
arith_expr:
  | arith_expr PLUS mul_expr  { ExprNode (Add ($1, $3)) }
  | arith_expr MINUS mul_expr { ExprNode (Sub ($1, $3)) }
  | mul_expr { $1 }
  ;

/* Multiplicative arithmetic (left assoc) */
mul_expr:
  | mul_expr TIMES cons_expr  { ExprNode (Mul ($1, $3)) }
  | mul_expr DIVIDE cons_expr { ExprNode (Div ($1, $3)) }
  | cons_expr { $1 }
  ;

/* Cons level (right-associative) */
cons_expr:
  | prefix_expr CONS cons_expr   { ExprNode (Cons ($1, $3)) } (* Use prefix_expr here *) 
  | prefix_expr { $1 }           /* Fallthrough to prefix_expr */
  ;

/* Prefix operators level */
prefix_expr:                  (* New level for prefix ops like ! and ref *)
  | MINUS prefix_expr         { ExprNode (Sub (ExprNode (Const 0.), $2)) }
  | BANG prefix_expr          { ExprNode (Deref $2) }
  | REF prefix_expr           { ExprNode (Ref $2) }
  | app_expr { $1 }           /* Fallthrough to app_expr */
  ;

/* Application Level */
app_expr:
  | app_expr atomic_expr                                                        { ExprNode (FuncApp ($1, $2)) }
  | FST atomic_expr                                                             { ExprNode (First $2) }
  | SND atomic_expr                                                             { ExprNode (Second $2) }
  | atomic_expr                                                                 { $1 }        /* Fallthrough to atomic_expr */
  ;

/* Atomic expressions (variables, constants, parens, tuples, distributions, nil) */ 
atomic_expr:
  | n = number                { ExprNode (Const n) }
  | TRUE                      { ExprNode (BoolConst true) }
  | FALSE                     { ExprNode (BoolConst false) }
  | NIL                       { ExprNode Nil }
  | k = INT HASH n = INT
    { if k < 0 || k >= n then failwith (Printf.sprintf "Invalid FinConst: %d#%d" k n) else ExprNode (FinConst (k, n)) }
  | x = IDENT                 { ExprNode (Var x) }
  | FLIP LPAREN p = expr RPAREN { ExprNode (Flip p) }
  | DISCRETE LPAREN probs = separated_nonempty_list(COMMA, expr) RPAREN
    {
      (* Syntax: discrete(p1, p2, ...) where each pi is a
         probability expression; the i-th branch is the value i#n. *)
      let n = List.length probs in
      let cases = List.mapi (fun i p -> (ExprNode (FinConst (i, n)), p)) probs in
      ExprNode (DiscreteCase cases)
    }
  | UNIFORM LPAREN lo = expr COMMA hi = expr RPAREN
    { ExprNode (Sample (Distr2 (DUniform, lo, hi))) }
  | GAUSSIAN LPAREN mean = expr COMMA std = expr RPAREN
    { ExprNode (Sample (Distr2 (DGaussian, mean, std))) }
  | EXPONENTIAL LPAREN rate = expr RPAREN
    { ExprNode (Sample (Distr1 (DExponential, rate))) }
  | BETA LPAREN alpha = expr COMMA beta = expr RPAREN
    { ExprNode (Sample (Distr2 (DBeta, alpha, beta))) }
  | LOGNORMAL LPAREN mu = expr COMMA sigma = expr RPAREN
    { ExprNode (Sample (Distr2 (DLogNormal, mu, sigma))) }
  | GAMMA LPAREN shape = expr COMMA scale = expr RPAREN
    { ExprNode (Sample (Distr2 (DGamma, shape, scale))) }
  | LAPLACE LPAREN scale = expr RPAREN
    { ExprNode (Sample (Distr1 (DLaplace, scale))) }
  | CAUCHY LPAREN scale = expr RPAREN
    { ExprNode (Sample (Distr1 (DCauchy, scale))) }
  | WEIBULL LPAREN a = expr COMMA b = expr RPAREN
    { ExprNode (Sample (Distr2 (DWeibull, a, b))) }
  | TDIST LPAREN nu = expr RPAREN
    { ExprNode (Sample (Distr1 (DTDist, nu))) }
  | CHI2 LPAREN nu = expr RPAREN
    { ExprNode (Sample (Distr1 (DChi2, nu))) }
  | LOGISTIC LPAREN scale = expr RPAREN
    { ExprNode (Sample (Distr1 (DLogistic, scale))) }
  | RAYLEIGH LPAREN sigma = expr RPAREN
    { ExprNode (Sample (Distr1 (DRayleigh, sigma))) }
  | PARETO LPAREN xm = expr COMMA alpha = expr RPAREN
    { ExprNode (Sample (Distr2 (DPareto, xm, alpha))) }
  | GUMBELONE LPAREN mu = expr COMMA beta_param = expr RPAREN
    { ExprNode (Sample (Distr2 (DGumbel1, mu, beta_param))) }
  | GUMBELTWO LPAREN mu = expr COMMA beta_param = expr RPAREN
    { ExprNode (Sample (Distr2 (DGumbel2, mu, beta_param))) }
  | EXPPOW LPAREN arg1 = expr COMMA arg2 = expr RPAREN
    { ExprNode (Sample (Distr2 (DExppow, arg1, arg2))) }
  | POISSON LPAREN mu = expr RPAREN
    { ExprNode (Sample (Distr1 (DPoisson, mu))) }
  | BINOMIAL LPAREN arg1 = expr COMMA arg2 = expr RPAREN
    { ExprNode (Sample (Distr2 (DBinomial, arg1, arg2))) }
  | LPAREN RPAREN { ExprNode Unit } 
  | LPAREN el = expr_comma_list RPAREN (* New rule for (e1), (e1,e2), (e1,e2,e3), etc. *)
    { 
      let rec build_pairs_from_list expr_list =
        match expr_list with
        | [] -> failwith "Impossible: empty list in tuple construction - expr_comma_list should be non-empty"
        | [single_e] -> single_e (* Parsed (e), not a pair *)
        | first_e :: second_e :: rest_of_list -> (* Parsed (e1, e2, ...), create Pair(e1, rec_parse(e2,...)) *)
            ExprNode (Pair (first_e, build_pairs_from_list (second_e :: rest_of_list)))
      in
      build_pairs_from_list el
    }
  ;

/* Optional bar rule */
opt_bar:
  | /* empty */ { () }
  | BAR         { () }
  ;

number:
  | f = FLOAT { f }
  | i = INT   { float_of_int i }
  ;

expr_comma_list: (* Definition for comma-separated list of expressions *)
    e = expr                         { [e] }
  | e = expr COMMA rest = expr_comma_list { e :: rest }
  ;

%% (* This %% should mark the end of rules and precede any OCaml code if present *)
