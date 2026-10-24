%{
open Ast

let rec tuple = function
  | [e] -> e
  | e :: rest -> Pair (e, tuple rest)
  | [] -> assert false

let sample d args =
  if not (Distribution.accepts d (List.length args)) then
    failwith (Printf.sprintf "%s does not take %d parameter(s)"
      (Distribution.name d) (List.length args));
  Sample (d, args)
%}

%token <string> IDENT
%token <float> FLOAT
%token <int> INT
%token <Distribution.t> DIST
%token LET IN
%token IF THEN ELSE
%token TRUE FALSE
%token AND OR NOT
%token FST SND
%token FUN ARROW
%token LESS LESSEQ GREATER GREATEREQ
%token HASH LT_HASH LEQ_HASH GT_HASH GEQ_HASH EQ_HASH
%token LPAREN RPAREN
%token COMMA
%token EQUAL
%token EOF
%token OBSERVE
%token FIX
%token COLON_EQUAL  (* := *)
%token NIL
%token CONS         (* :: *)
%token MATCH WITH END BAR
%token REF          (* ref *)
%token BANG         (* ! *)
%token SEMICOLON    (* ; *)
%token PLUS MINUS TIMES DIVIDE

%start <Ast.expr> prog

(* Define types for non-terminals *) 
%type <Ast.expr> expr assign_expr cons_expr cmp_expr app_expr atomic_expr prefix_expr
%type <Ast.expr list> expr_comma_list (* New type for list of expressions *)
%type <unit> opt_bar
%type <float> number
%type <Ast.expr> arith_expr mul_expr

%left ARROW
%left SEMICOLON

%% 

prog: e = expr EOF { e };

/* Lowest precedence: LET, IF, FUN, FIX, MATCH (handled by structure) 
   then SEMICOLON, then assign_expr and higher operators */
expr:
    expr SEMICOLON expr 
    { Seq ($1, $3) }
  | LET x = IDENT EQUAL e1 = expr IN e2 = expr
    { Let (x, e1, e2) }
  | IF cond = expr THEN e1 = expr ELSE e2 = expr
    { If (cond, e1, e2) }
  | FUN x = IDENT ARROW e = expr
    { Fun (x, e) }
  | OBSERVE e = expr
    { Observe e }
  | FIX f = IDENT x = IDENT COLON_EQUAL e = expr 
    { Fix (f, x, e) }
  | MATCH e1 = expr WITH opt_bar NIL ARROW e_nil = expr BAR y = IDENT CONS ys = IDENT ARROW e_cons = expr END 
    { Match_list (e1, e_nil, y, ys, e_cons) } 
  (*
  | FOR i = IDENT EQUAL n1 = expr TO n2 = expr DO body = expr
    { For (i, n1, n2, body) }
  *)
  | assign_expr { $1 } /* Fallthrough to assign_expr */
  ;

/* Assignment level */
assign_expr:
  | prefix_expr COLON_EQUAL assign_expr { Assign ($1, $3) }
  | or_expr { $1 } /* Fallthrough to or_expr, as per diff */
  ;

/* OR Level */
or_expr:
  | or_expr OR and_expr  { Or ($1, $3) }
  | and_expr { $1 }     /* Fallthrough to and_expr */
  ;

/* AND Level */
and_expr:
  | and_expr AND not_expr { And ($1, $3) }
  | not_expr { $1 }      /* Fallthrough to not_expr */
  ;

/* NOT Level */
not_expr:
  | NOT not_expr          { Not $2 }
  | cmp_expr { $1 }       /* Fallthrough to cmp_expr */
  ;

/* Comparison level */
cmp_expr:
  | cmp_expr LESS arith_expr     { Compare (Lt, $1, $3) }
  | cmp_expr LESSEQ arith_expr   { Compare (Le, $1, $3) }
  | cmp_expr GREATER arith_expr  { Compare (Lt, $3, $1) }
  | cmp_expr GREATEREQ arith_expr { Compare (Le, $3, $1) }
  | arith_expr LT_HASH INT arith_expr { Finite_compare (Lt, $3, $1, $4) }
  | arith_expr LEQ_HASH INT arith_expr { Finite_compare (Le, $3, $1, $4) }
  | arith_expr GT_HASH INT arith_expr { Finite_compare (Lt, $3, $4, $1) }
  | arith_expr GEQ_HASH INT arith_expr { Finite_compare (Le, $3, $4, $1) }
  | arith_expr EQ_HASH INT arith_expr { Finite_compare (Eq, $3, $1, $4) }
  | arith_expr { $1 }            /* Fallthrough to arith_expr */
  ;

/* Additive arithmetic on float-typed expressions (left assoc) */
arith_expr:
  | arith_expr PLUS mul_expr  { Arith (Add, $1, $3) }
  | arith_expr MINUS mul_expr { Arith (Sub, $1, $3) }
  | mul_expr { $1 }
  ;

/* Multiplicative arithmetic (left assoc) */
mul_expr:
  | mul_expr TIMES cons_expr  { Arith (Mul, $1, $3) }
  | mul_expr DIVIDE cons_expr { Arith (Div, $1, $3) }
  | cons_expr { $1 }
  ;

/* Cons level (right-associative) */
cons_expr:
  | prefix_expr CONS cons_expr   { Cons ($1, $3) }
  | prefix_expr { $1 }           /* Fallthrough to prefix_expr */
  ;

/* Prefix operators level */
prefix_expr:                  (* New level for prefix ops like ! and ref *)
  | MINUS prefix_expr         { Arith (Sub, Const 0., $2) }
  | BANG prefix_expr          { Deref $2 }
  | REF prefix_expr           { Ref $2 }
  | app_expr { $1 }           /* Fallthrough to app_expr */
  ;

/* Application Level */
app_expr:
  | app_expr atomic_expr                                                        { Apply ($1, $2) }
  | FST atomic_expr                                                             { First $2 }
  | SND atomic_expr                                                             { Second $2 }
  | atomic_expr                                                                 { $1 }        /* Fallthrough to atomic_expr */
  ;

/* Atomic expressions (variables, constants, parens, tuples, distributions, nil) */
atomic_expr:
  | n = number                { Const n }
  | TRUE                      { Bool true }
  | FALSE                     { Bool false }
  | NIL                       { Nil }
  | k = INT HASH n = INT
    { if k < 0 || k >= n then failwith (Printf.sprintf "Invalid finite constant: %d#%d" k n) else Finite (k, n) }
  | x = IDENT                 { Var x }
  | d = DIST LPAREN args = separated_nonempty_list(COMMA, expr) RPAREN
    { sample d args }
  | LPAREN RPAREN { Unit }
  | LPAREN el = expr_comma_list RPAREN (* (e), (e1,e2), (e1,e2,e3), ... *)
    { tuple el }
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


