%{

  open Lexing
  open Kawa

%}


(* LISTE LEXEMES *)
%token <int> INT
%token <bool> BOOL
%token <string> IDENT
%token <string> IDENT_CLASS
%token TINT TBOOL TVOID

%token ASSIGN INSTANCEOF

%token STATIC FINAL PRIVATE PROTECTED
%token METHOD RETURN THIS SUPER
%token CLASS DOT NEW EXTENDS

%token PLUS STAR DIV REM MINUS U_MINUS
%token EQUAL N_EQUAL S_EQUAL SN_EQUAL
%token LT LE GT GE
%token AND OR NOT

%token IF ELSE
%token WHILE BREAK CONTINUE

%token LPAR RPAR BEGIN END LBRA RBRA
%token SEMI COMMA
%token CREATE_TAB SIZE_TAB
%token PRINT PRINTLN
%token MAIN EOF


(* REGLES DE PRIORITES *)
%nonassoc LBRA

%right OR
%right AND
%nonassoc NOT

%left EQUAL N_EQUAL S_EQUAL SN_EQUAL
%left LT LE GT GE

%left INSTANCEOF

%left PLUS MINUS
%left STAR DIV REM
%nonassoc U_MINUS

%nonassoc DOT


(* POINT D'ENTREE *)
%start program
%type <Kawa.program> program

%%


program:
| v=declaration* c=class_def* MAIN BEGIN main=list(instruction) END EOF
    { {classes=c; globals=v; main} }
;


heritage:
| EXTENDS s=IDENT_CLASS { s }
;


class_def:
 | CLASS s=IDENT_CLASS p=option(heritage) BEGIN a=declaration* m=method_def* END
    { {class_name=s; attributes=a; methods=m; parent=p} }
 ;


declaration:
| vf=vis_field? tf=typ_field? t=typ l=separated_nonempty_list(COMMA, decl) SEMI
 {
   let map_l =
   let tf = match tf with | None -> (false, false) | Some(b) -> b in
   let f = fun x -> (fst x, snd x, (vf, fst tf, snd tf))
   in List.map f l in
   (map_l, t)
 }
;


decl:
 | s=IDENT { (s, ExprNull) }
 | s=IDENT ASSIGN e=expression { (s, e) }
;


typ:
 | TVOID           { TVoid     }
 | TINT            { TInt      }
 | TBOOL           { TBool     }
 | s=IDENT_CLASS   { TClass(s) }
 | t=typ LBRA RBRA { TArray(t) }
;


typ_field:
 | STATIC       { (true,  false ) }
 | FINAL        { (false, true  ) }
 | STATIC FINAL { (true,  true  ) }
;


vis_field:
 | PRIVATE   { Private   }
 | PROTECTED { Protected }
;


params:
 | t=typ s=IDENT { (s, t) }
;


method_def:
 | METHOD vf=vis_field? t=typ s=IDENT LPAR p=separated_list(COMMA, params) RPAR BEGIN v=declaration* i=instruction* END
    {   {method_name=s; visible=vf; code=i; params=p; locals=v; return=t}   }
 ;


mem:
 | s=IDENT { Var(s) }
 | e=expression DOT s=IDENT { Field(e, s) }
 | e1=expression LBRA e2=expression RBRA { ArrField(e1, e2) }
;


instruction:
| PRINT LPAR e=expression RPAR SEMI { Print(e) }
| PRINTLN LPAR e=expression RPAR SEMI { Println(e) }

| IF LPAR e=expression RPAR BEGIN t=list(instruction) END { If(e, t, []) }
| IF LPAR e=expression RPAR BEGIN t=list(instruction) END ELSE BEGIN f=list(instruction) END { If(e, t, f) }

| m=mem ASSIGN e=expression SEMI { Set(m, e) }

| WHILE LPAR e=expression RPAR BEGIN t=list(instruction) END { While(e, t) }
| BREAK SEMI { Break }
| CONTINUE SEMI { Continue }

| RETURN e=expression SEMI { Return(e) }
| e=expression SEMI { Expr(e) }
;


args_create_tab:
| COMMA l=separated_nonempty_list(COMMA, expression) { l }
;


expression:
| n=INT  { Int(n)  }
| b=BOOL { Bool(b) }

| LBRA l=separated_list(COMMA, expression) RBRA { Array(l) }
| CREATE_TAB LPAR t=typ o=option(args_create_tab) RPAR
   { let l = match o with Some l -> l | None -> [] in ArrayCreate (t, l) }
| SIZE_TAB LPAR e=expression RPAR { ArraySize(e) }

| LPAR e1=expression RPAR { e1 }

| e1=expression op=binop e2=expression { Binop(op, e1, e2) }
| MINUS e=expression { Unop(Opp, e) } %prec U_MINUS
| NOT   e=expression { Unop(Not, e) }

| m=mem { Get(m) }

| THIS { This }

| NEW s=IDENT_CLASS { New(s) }
| NEW s=IDENT_CLASS LPAR a=separated_list(COMMA, expression) RPAR { NewCstr(s, a) }

| e=expression DOT s=IDENT LPAR a=separated_list(COMMA, expression) RPAR { MethCall(e, s, a) }
| SUPER DOT s=IDENT LPAR a=separated_list(COMMA, expression) RPAR { SuperCall(s, a) }

| e=expression INSTANCEOF t=typ { Instanceof(e, t) }
;

%inline binop:
 | PLUS       { Add  }
 | MINUS      { Sub  }
 | STAR       { Mul  }
 | DIV        { Div  }
 | REM        { Rem  }
 | LT         { Lt   }
 | LE         { Le   }
 | GT         { Gt   }
 | GE         { Ge   }
 | EQUAL      { Eq   }
 | N_EQUAL    { Neq  }
 | S_EQUAL    { Seq  }
 | SN_EQUAL   { Sneq }
 | AND        { And  }
 | OR         { Or   }
