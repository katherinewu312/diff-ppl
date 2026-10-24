{
open Parser

exception LexError of string

let error lexbuf msg =
  let pos = Lexing.lexeme_start_p lexbuf in
  let line = pos.pos_lnum in
  let col = pos.pos_cnum - pos.pos_bol in
  raise (LexError (Printf.sprintf "Line %d, column %d: %s" line col msg))

let next_line lexbuf = 
  let open Lexing in
  let pos = lexbuf.lex_curr_p in
  lexbuf.lex_curr_p <- {
    pos with 
    pos_lnum = pos.pos_lnum + 1;
    pos_bol = lexbuf.lex_curr_pos;
  }

let keywords = [
  "let", LET; "in", IN; "if", IF; "then", THEN; "else", ELSE;
  "true", TRUE; "false", FALSE; "not", NOT; "observe", OBSERVE;
  "fst", FST; "snd", SND; "fun", FUN; "fix", FIX;
  "nil", NIL; "match", MATCH; "with", WITH; "end", END; "ref", REF;
]

let identifier s =
  match List.assoc_opt s keywords with
  | Some token -> token
  | None ->
      match Distribution.of_name s with
      | Some d -> DIST d
      | None -> IDENT s
}

let digit = ['0'-'9']
let int = digit+
let float = digit+ ('.' digit*)? (['e' 'E'] ['+' '-']? digit+)?
let lower = ['a'-'z']
let upper = ['A'-'Z']
let alpha = lower | upper | '_'
let ident = alpha (alpha | digit)*

rule token = parse
  | [' ' '\t' '\r']+ { token lexbuf }
  | '\n'      { next_line lexbuf; token lexbuf }
  | "(*"      { comment lexbuf; token lexbuf }
  | "&&"      { AND }
  | "||"      { OR }
  | "->"      { ARROW }
  | '<'       { LESS }
  | "<="      { LESSEQ }
  | '>'       { GREATER }
  | ">="      { GREATEREQ }
  | '='       { EQUAL }
  | '('       { LPAREN }
  | ')'       { RPAREN }
  | ','       { COMMA }
  | ":="      { COLON_EQUAL }
  | ";"       { SEMICOLON }
  | "::"      { CONS }
  | "|"       { BAR }
  | '!'       { BANG }
  | '+'       { PLUS }
  | '-'       { MINUS }
  | '*'       { TIMES }
  | '/'       { DIVIDE }
  | int as i   { try INT (int_of_string i)
                 with _ -> error lexbuf (Printf.sprintf "Invalid integer literal: %s" i) }
  | float as f { try FLOAT (float_of_string f)
                 with _ -> error lexbuf (Printf.sprintf "Invalid float literal: %s" f) }
  | ident as s { identifier s }
  | "<=" "#"   { LEQ_HASH }
  | "<" "#"    { LT_HASH }
  | ">=" "#"   { GEQ_HASH }
  | ">" "#"    { GT_HASH }
  | "==" "#"   { EQ_HASH }
  | "#"        { HASH }
  | eof       { EOF }
  | _ as c    { error lexbuf (Printf.sprintf "Unexpected character: %c" c) }

and comment = parse
  | "(*" { comment lexbuf; comment lexbuf }
  | "*)" { () }
  | '\n' { next_line lexbuf; comment lexbuf }
  | eof  { error lexbuf "Unterminated comment" }
  | _    { comment lexbuf }
