{

  open Lexing
  open Kawaparser

  exception Error of string

  let keyword_or_ident =
  let h = Hashtbl.create 17 in
  List.iter (fun (s, k) -> Hashtbl.add h s k)
    [
    "print",      PRINT;
    "println",    PRINTLN;
    "main",       MAIN;

    "if",         IF;
    "else",       ELSE;
    "while",      WHILE;
    "break",      BREAK;
    "continue",   CONTINUE;

    "true",       BOOL true;
    "false",      BOOL false;

    "class",      CLASS;
    "new",        NEW;
    "extends",    EXTENDS;

    "final",      FINAL;
    "static",     STATIC;
    "private",    PRIVATE;
    "protected",  PROTECTED;

    "method",     METHOD;
    "return",     RETURN;
    "this",       THIS;
    "super",      SUPER;

    "int",        TINT;
    "bool",       TBOOL;
    "void",       TVOID;

    "create_tab", CREATE_TAB;
    "size_tab",   SIZE_TAB;

    "instanceof", INSTANCEOF;
    ] ;
  fun s ->
    try
      Hashtbl.find h s
    with Not_found ->
      match s.[0] with
        | 'a'..'z'
        | '_'      -> IDENT(s)
        | 'A'..'Z' -> IDENT_CLASS(s)
        | _        -> assert false

}

let digit = ['0'-'9']
let number = ['-']? digit+
let alpha = ['a'-'z' 'A'-'Z']
let ident = ['a'-'z' '_'] (alpha | '_' | digit)*
let ident_class = ['A'-'Z'] (alpha | '_' | digit)*

rule token = parse
  | ['\n']            { new_line lexbuf; token lexbuf }
  | [' ' '\t' '\r']+  { token lexbuf }

  | "//" [^ '\n']* "\n"  { new_line lexbuf; token lexbuf }
  | "/*"                 { comment lexbuf; token lexbuf }

  | number as n       { INT(int_of_string n) }
  | ident  as id      { keyword_or_ident id  }
  | ident_class as id { keyword_or_ident id  }

  | "+"   { PLUS }
  | "-"   { MINUS }
  | "*"   { STAR }
  | "/"   { DIV }
  | "%"   { REM }
  | "=="  { EQUAL }
  | "!="  { N_EQUAL }
  | "===" { S_EQUAL }
  | "=!=" { SN_EQUAL }
  | "<"   { LT }
  | "<="  { LE }
  | ">"   { GT }
  | ">="  { GE }
  | "!"   { NOT }
  | "&&"  { AND }
  | "||"  { OR  }

  | "="   { ASSIGN }
  | "."   { DOT }
  | ","   { COMMA }


  | ";"   { SEMI }
  | "("   { LPAR }
  | ")"   { RPAR }
  | "{"   { BEGIN }
  | "}"   { END }

  | "["   { LBRA }
  | "]"   { RBRA }

  | _    { raise (Error ("unknown character : " ^ lexeme lexbuf)) }
  | eof  { EOF }

and comment = parse
  | "*/" { () }
  | _    { comment lexbuf }
  | eof  { raise (Error "unterminated comment") }
