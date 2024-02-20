open Kawa

type value =
  | VInt of int
  | VBool of bool
  | VObj of obj
  | VArray of value array
  | Null

and obj =
  { cls : string
  ; fields : (string, value) Hashtbl.t
  }

type classe =
  { cls_name : string
  ; attrs : (string * expr) list
  ; meths : (string, method_def) Hashtbl.t
  ; part : string option
  }

exception Return of value

exception Error of string

let error s = raise (Error s)

let exec_prog (p : program) : unit =
  (* On stocke ici les attributs statiques *)
  let (statics : (string, value) Hashtbl.t) = Hashtbl.create 16 in
  (* Sert a sauvegarder la dernière position lors d'appels de supercall imbriqués *)
  let (this_supercall : classe ref) =
    ref { cls_name = ""; attrs = []; meths = Hashtbl.create 0; part = None }
  in

  let instr_prog = ref p.main in
  let (statics_ht : (string, (string * expr) list) Hashtbl.t) =
    Hashtbl.create 16
  in

  let rec add_list l1 l2 =
    match l1 with [] -> l2 | e :: ll1 -> add_list ll1 (e :: l2)
  in

  let add_vars_env decl_list f =
    let affect_list = ref [] in
    List.iter
      (fun (l, _) ->
        List.iter
          (fun (str, expr, _) ->
            f str;
            match expr with
            | ExprNull -> ()
            | _ -> affect_list := Set (Var str, expr) :: !affect_list )
          l )
      decl_list;
    !affect_list
  in

  let env = Hashtbl.create 16 in
  let affect_instr =
    add_vars_env p.globals (fun str -> Hashtbl.replace env str Null)
  in
  instr_prog := add_list affect_instr !instr_prog;
  let p = { classes = p.classes; globals = p.globals; main = !instr_prog } in

  let method_list_to_hashtbl l =
    let tbl = Hashtbl.create 16 in
    List.iter (fun x -> Hashtbl.replace tbl x.method_name x) l;
    tbl
  in
  let update_attributes l cls_name =
    let add_static attr_name expr =
      match Hashtbl.find_opt statics_ht cls_name with
      | None -> Hashtbl.replace statics_ht cls_name [ (attr_name, expr) ]
      | Some st_l ->
        Hashtbl.replace statics_ht cls_name ((attr_name, expr) :: st_l)
    in

    List.fold_left
      (fun acc (str_expr_list, _) ->
        List.fold_left
          (fun acc (str, expr, (_, is_static, _)) ->
            if is_static then begin
              add_static str expr;
              acc
            end
            else (str, expr) :: acc )
          acc str_expr_list )
      [] l
  in

  let create_class c =
    { cls_name = c.class_name
    ; attrs = update_attributes c.attributes c.class_name
    ; meths = method_list_to_hashtbl c.methods
    ; part = c.parent
    }
  in
  let (classes : (string, classe) Hashtbl.t) = Hashtbl.create 16 in
  List.iter
    (fun c -> Hashtbl.replace classes c.class_name (create_class c))
    p.classes;

  let rec eval_call f this args =
    let local_env = Hashtbl.create 16 in
    Hashtbl.replace local_env "this" this;

    List.iter2 (fun (s, _) e -> Hashtbl.replace local_env s e) f.params args;
    let affect_instr =
      add_vars_env f.locals (fun str -> Hashtbl.replace local_env str Null)
    in
    let f_code = add_list affect_instr f.code in

    try
      exec_seq f_code local_env;
      Null
    with Return v -> v
  and exec_seq s lenv =
    let rec evali e = match eval e with VInt n -> n | _ -> assert false
    and evalb e = match eval e with VBool b -> b | _ -> assert false
    and evalo e = match eval e with VObj o -> o | _ -> assert false
    and evalt e = match eval e with VArray t -> t | _ -> assert false
    and check_not_zero e =
      let res = eval e in
      match res with
      | VInt 0 -> error "Division_by_zero"
      | VInt n -> n
      | _ -> assert false
    and create_obj cls =
      let rec add_attrs c table =
        List.iter
          (fun (s, e) ->
            match Hashtbl.find_opt table s with
            | Some _ -> ()
            | None -> (
              match e with
              | ExprNull -> Hashtbl.replace table s Null
              | _ -> Hashtbl.replace table s (eval e) ) )
          c.attrs;
        match c.part with
        | None -> ()
        | Some s -> add_attrs (Hashtbl.find classes s) table
      in
      let table = Hashtbl.create 16 in
      add_attrs cls table;
      VObj { cls = cls.cls_name; fields = table }
    and search_method cls f_name =
      match Hashtbl.find_opt cls.meths f_name with
      | Some f -> f
      | None -> (
        match cls.part with
        | None -> assert false
        | Some s -> search_method (Hashtbl.find classes s) f_name )
    and search_static_and_apply f attr_name inst =
      let rec loop f attr_name cls =
        match
          Hashtbl.find_opt statics
            (Printf.sprintf "%s.%s" cls.cls_name attr_name)
        with
        | Some v -> f v cls.cls_name
        | None -> (
          match cls.part with
          | None -> f Null cls.cls_name
          | Some name -> loop f attr_name (Hashtbl.find classes name) )
      in
      loop f attr_name (Hashtbl.find classes inst.cls)
    and physical_equality e1 e2 =
      match (eval e1, eval e2) with
      | VInt n1, VInt n2 -> n1 == n2
      | VBool b1, VBool b2 -> b1 == b2
      | VObj o1, VObj o2 -> o1 == o2
      | _, _ -> false
    and create_tab typ l =
      let verif_dim n =
        let dim = evali n in
        if dim <= 0 then
          error
            (Printf.sprintf "%d size is not a valid dimension for create_tab"
               dim )
        else dim
      in
      let rec loop l =
        VArray
          ( match l with
          | [] -> [||]
          | [ n ] -> Array.init (verif_dim n) (fun _i -> Null)
          | n :: ll -> Array.init (verif_dim n) (fun _i -> loop ll) )
      in
      loop l
    and is_sub_class c parent_name =
      let rec loop cls_name =
        if cls_name = parent_name then true
        else
          match (Hashtbl.find classes cls_name).part with
          | None -> false
          | Some name -> loop name
      in
      loop c.cls
    and eval (e : expr) : value =
      match e with
      | Int n -> VInt n
      | Bool b -> VBool b
      | Array l -> VArray (Array.of_list (List.map (fun x -> eval x) l))
      | ArrayCreate (typ, l) -> create_tab typ l
      | ArraySize e -> VInt (Array.length (evalt e))
      | Binop (Add, e1, e2) -> VInt (evali e1 + evali e2)
      | Binop (Mul, e1, e2) -> VInt (evali e1 * evali e2)
      | Binop (Sub, e1, e2) -> VInt (evali e1 - evali e2)
      | Binop (Div, e1, e2) ->
        let e2' = check_not_zero e2 in
        VInt (evali e1 / e2')
      | Binop (Rem, e1, e2) ->
        let e2' = check_not_zero e2 in
        VInt (evali e1 mod e2')
      | Binop (Lt, e1, e2) -> VBool (evali e1 < evali e2)
      | Binop (Le, e1, e2) -> VBool (evali e1 <= evali e2)
      | Binop (Gt, e1, e2) -> VBool (evali e1 > evali e2)
      | Binop (Ge, e1, e2) -> VBool (evali e1 >= evali e2)
      | Binop (And, e1, e2) -> VBool (evalb e1 && evalb e2)
      | Binop (Or, e1, e2) -> VBool (evalb e1 || evalb e2)
      | Binop (Eq, e1, e2) -> VBool (physical_equality e1 e2)
      | Binop (Neq, e1, e2) -> VBool (not (physical_equality e1 e2))
      | Binop (Seq, e1, e2) -> VBool (eval e1 = eval e2)
      | Binop (Sneq, e1, e2) -> VBool (eval e1 <> eval e2)
      | Unop (Opp, e) -> VInt (-evali e)
      | Unop (Not, b) -> VBool (not (evalb b))
      | Get (Var s) -> (
        match Hashtbl.find_opt lenv s with
        | Some v when v <> Null -> v
        | _ -> (
          match Hashtbl.find_opt env s with
          | Some v when v <> Null -> v
          | _ -> error (Printf.sprintf "%s variable is null" s) ) )
      | Get (Field (o, s)) -> (
        let inst = evalo o in
        match Hashtbl.find_opt inst.fields s with
        | Some v when v <> Null -> v
        | _ -> (
          let res = ref Null in
          search_static_and_apply (fun v _ -> res := v) s inst;
          match !res with
          | Null -> error (Printf.sprintf "%s attribute is null" s)
          | v -> v ) )
      | Get (ArrField (e1, e2)) ->
        let t = evalt e1 in
        let i = evali e2 in
        if 0 <= i && i < Array.length t then t.(i)
        else error (Printf.sprintf "The index %d is out of bounds" i)
      | New s ->
        let cls = Hashtbl.find classes s in
        create_obj cls
      | NewCstr (s, a) ->
        let cls = Hashtbl.find classes s in
        let obj = create_obj cls in
        let f = search_method cls "constructor" in
        let _ = eval_call f obj (List.map (fun e -> eval e) a) in
        obj
      | This -> Hashtbl.find lenv "this"
      | MethCall (o, s, a) ->
        let inst = evalo o in
        let cls = Hashtbl.find classes inst.cls in
        let f = search_method cls s in
        eval_call f (VObj inst) (List.map (fun e -> eval e) a)
      | SuperCall (s, a) ->
        let _ =
          match Hashtbl.find_opt env "$this_super" with
          | Some _ -> ()
          | None -> (
            match eval This with
            | VObj inst as o ->
              Hashtbl.replace env "$this_super" o;
              let cls = Hashtbl.find classes inst.cls in
              this_supercall := cls
            | _ -> assert false )
        in

        let part =
          match !this_supercall.part with
          | None -> assert false
          | Some part ->
            let part = Hashtbl.find classes part in
            this_supercall := part;
            part
        in

        let f = search_method part s in
        let res =
          eval_call f
            (Hashtbl.find env "$this_super")
            (List.map (fun e -> eval e) a)
        in

        Hashtbl.remove env "$this_super";
        res
      | Instanceof (expr, typ) -> (
        match typ with
        | TClass name -> VBool (is_sub_class (evalo expr) name)
        | _ -> assert false )
      | ExprNull -> assert false
    in

    let rec exec (i : instr) : unit =
      match i with
      | Print e -> print_expr e
      | Println e ->
        print_expr e;
        Printf.printf "\n"
      | If (e, s1, s2) -> if evalb e then exec_seq s1 else exec_seq s2
      | While (e, s) -> if evalb e then if exec_seq_loop s then exec i
      | Break | Continue ->
        error "Instruction 'break' or 'continue' have to be inside a loop"
      | Set (Var s, e) -> (
        match Hashtbl.find_opt lenv s with
        | Some _ -> Hashtbl.replace lenv s (eval e)
        | None -> Hashtbl.replace env s (eval e) )
      | Set (Field (o, s), e) -> (
        try
          let inst = evalo o in
          match Hashtbl.find_opt inst.fields s with
          | Some _ -> Hashtbl.replace inst.fields s (eval e)
          | None ->
            let v = eval e in
            search_static_and_apply
              (fun _ cls_name ->
                Hashtbl.replace statics (Printf.sprintf "%s.%s" cls_name s) v )
              s inst
        with Assert_failure _ ->
          error (Printf.sprintf "The attribute %s not exist" s) )
      | Set (ArrField (e1, e2), e3) ->
        let t = evalt e1 in
        let i = evali e2 in
        if 0 <= i && i < Array.length t then t.(i) <- eval e3
        else error (Printf.sprintf "The index %d is out of bounds" i)
      | Return e -> raise (Return (eval e))
      | Expr e ->
        let _ = eval e in
        ()
    and exec_seq s = List.iter exec s
    and exec_seq_loop s =
      match s with
      | [] -> true
      | i :: s1 -> (
        match i with
        | Continue -> true
        | Break -> false
        | _ ->
          exec i;
          exec_seq_loop s1 )
    and init_static () =
      Hashtbl.iter
        (fun cls_name l ->
          List.iter
            (fun (attr_name, expr) ->
              let expr_val =
                match expr with ExprNull -> Null | _ -> eval expr
              in
              Hashtbl.replace statics
                (Printf.sprintf "%s.%s" cls_name attr_name)
                expr_val )
            (List.rev l) )
        statics_ht
    and print_expr e =
      let rec loop = function
        | Null -> error "Null value is not printable"
        | VInt n -> Printf.printf "%d" n
        | VBool b -> Printf.printf "%b" b
        | VArray t ->
          Printf.printf "[";
          let cpt = ref (Array.length t) in
          Array.iter
            (fun x ->
              loop x;
              decr cpt;
              if !cpt > 0 then Printf.printf ", " )
            t;
          Printf.printf "]"
        | VObj o ->
          Printf.printf "{ class : %s ; attributes : [| " o.cls;
          let tbl = o.fields in
          let cpt = ref (Hashtbl.length tbl) in
          Hashtbl.iter
            (fun key value ->
              Printf.printf "%s = " key;
              loop value;
              decr cpt;
              if !cpt > 0 then Printf.printf ", " )
            tbl;
          Printf.printf " |] }"
      in
      loop (eval e)
    in

    init_static ();
    exec_seq s
  in

  exec_seq p.main (Hashtbl.create 1)
