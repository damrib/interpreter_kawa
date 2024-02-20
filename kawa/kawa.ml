(** Kawa : un petit langage à objets inspiré de Java *)

(* Types déclarés pour les attributs, pour les variables, et pour les
   paramètres et résultats des méthodes. *)

exception Error of string

let error s = raise (Error s)

type typ =
  | TVoid
  | TInt
  | TBool
  | TArray of typ
  | TClass of string

type vis =
  | Protected
  | Private

type vis_stc_fin = vis option * bool * bool

let rec typ_to_string = function
  | TVoid -> "void"
  | TInt -> "int"
  | TBool -> "bool"
  | TArray t -> Printf.sprintf "%s array" (typ_to_string t)
  | TClass c -> c

type unop =
  | Opp
  | Not

type binop =
  | Add
  | Sub
  | Mul
  | Div
  | Rem
  | Lt
  | Le
  | Gt
  | Ge
  | Eq
  | Neq
  | Seq
  | Sneq
  | And
  | Or

(* Expressions *)
type expr =
  (* Base arithmétique *)
  | Int of int
  | Bool of bool
  | Unop of unop * expr
  | Binop of binop * expr * expr
  (* Accès à une variable ou un attribut *)
  | Get of mem_access
  (* Objet courant *)
  | This
  (* Création d'un nouvel objet *)
  | New of string
  | NewCstr of string * expr list
  (* Appel de méthode *)
  | MethCall of expr * string * expr list
  (* Appel  de methode de la classe mere*)
  | SuperCall of string * expr list
  (* Instanceof *)
  | Instanceof of expr * typ
  (* Tableau explicite *)
  | Array of expr list
  (* Alloue un tableau de type et de dimensions données *)
  | ArrayCreate of typ * expr list
  (* Renvoie la taille du tableau *)
  | ArraySize of expr
  (* Valeur null jamais init par l'utilisateur *)
  | ExprNull

(* Accès mémoire : variable ou attribut d'un objet *)
and mem_access =
  | Var of string
  | Field of expr (* objet *) * string (* nom d'un attribut *)
  | ArrField of expr * expr

(* Instructions *)
type instr =
  (* Affichage d'une expression *)
  | Print of expr
  | Println of expr
  (* Écriture dans une variable ou un attribut *)
  | Set of mem_access * expr
  (* Structures de contrôle usuelles *)
  | If of expr * seq * seq
  | While of expr * seq
  | Break
  | Continue
  (* Fin d'une fonction *)
  | Return of expr
  (* Expression utilisée comme instruction *)
  | Expr of expr

and seq = instr list

(* Définition de méthode

   Syntaxe : method <type de retour> <nom> (<params>) { ... }

   Le corps de la méthode est similaire au corps d'une fonction. *)
type method_def =
  { method_name : string
  ; visible : vis option
  ; code : seq
  ; params : (string * typ) list
  ; locals : ((string * expr * vis_stc_fin) list * typ) list
  ; return : typ
  }

(* Définition de classe

   Syntaxe : class <nom de la classe> { ... }
        ou : class <nom de la classe> extends <nom de la classe mère> { ... }

   On considère que toute classe C contient une définition de méthode de nom
   "constructor" et de type de retour void, qui initialise les champs du
   paramètre implicite this. *)
type class_def =
  { class_name : string
  ; attributes : ((string * expr * vis_stc_fin) list * typ) list
  ; methods : method_def list
  ; parent : string option
  }

(* Programme complet : variables globales, classes, et une séquence
   d'instructions *)
type program =
  { classes : class_def list
  ; globals : ((string * expr * vis_stc_fin) list * typ) list
  ; main : seq
  }
