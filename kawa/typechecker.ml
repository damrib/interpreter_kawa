open Kawa

exception Error of string

let error s = raise (Error s)

let type_error ty_actual ty_expected =
  error
    (Printf.sprintf "expected %s, got %s"
       (typ_to_string ty_expected)
       (typ_to_string ty_actual) )

module Env = Map.Make (String)

(* Dans l'environnement de typage, pour chaque variable ou attribut que l'on regarde,
   on stocke:
   * le type
   * l'option de visibilite private ou protected ou public (None)
   * si l'attribut est final ou non
   * si l'attribut ou la variable est initialise ou non
   * On ne sauvegarde pas static dans l'environnement car le seul moment on la seule chose que l'on verifie pour les attributs

   Dans l'environnement, on stocke aussi bien les variable (globales et locales) que
   les attributs.
   * La clé pour une variable correspond au nom de la variable
   * La clé pour les attributs correspond à nom_de_la_classe.nom_attribut
     le nom de la classe correspond au type "dynamique" de l'objet auxquel appartient l'attribut,
     si une classe test2 est la classe fille d'une classe test1 et que cette dernière à un attribut x
     alors si dans l'environnement on a un element de type test2, on pourra retrouver l'attribut x à partir
     de la chaine de caractere "test2.x".

    Pour les variables et les parametres on met dans l'environnement (typ, (None, false, true)).

    Nous avons fait ce choix lorsque l'on a implemente private, protected, static et final, nous avons besoin de savoir
    si les attributs ont ete declares avec l'un de ces mots-cles. De plus, nous avons besoin de savoir à la fin des constructeurs
    de classes si les champs finaux ou les champs publics sont initialises. Nous pensons qu'il est necessaire d'avoir les attributs
    dans l'environnement au moment de la verification du typage des constructeurs car avec l'heritage, il faut verifier la bonne
    initialisation des attributs de la classe mere.

    Cependant, on a besoin des informations uniquement lorsque l'on verifie le bon typage des constructeurs. Une meilleure approche
    aurait ete de creer un envionnement comme celui qu'on utilise uniquement dans check_mth lorsque la methode passee en argument est
    un constructeur. Pour verifier le reste du programme, on aurait pu utiliser un environnement ne contenant que le type des variables
    et des parametres.

    Un autre defaut de notre methode est que lorsque l'on ajoute une variable dont le type est une classe, on va ajouter tous les attributs a
    l'environnement, or si une autre variable du meme type etait deja dans l'environnement tous les attributs de la classe sont deja dans
    l'environnement.
    Un avantage de notre methode est que nous n'avons pas besoin d'iterer sur les classes de la hierarchie a chaque fois que l'on cherche a
    trouver le type d'un champ. (On va doit faire de tels iterations lorsque l'attribut est private ou protected)
*)
type tenv = (typ * (vis option * bool * bool)) Env.t

let typecheck_prog p =
  let rec check e typ tenv =
    let typ_e = type_expr e tenv in
    if typ_e <> typ then
      match (typ_e, typ) with
      | TArray r_type, TArray l_type -> check_arr_typ typ typ_e
      | TClass f_name, TClass p_name -> check_dyn_lia p_name f_name
      | _, _ -> type_error typ_e typ
  (* Procedure qui verifie que le type de deux arrays sont les memes
   * l_typ : typ
   * r_typ : typ
   * *)
  and check_arr_typ l_typ r_typ =
    let rec loop typ1 typ2 =
      match (typ1, typ2) with
      | TArray t1, TArray t2 -> loop t1 t2
      | typ, TVoid -> ()
      | t1, t2 -> if typ1 <> typ2 then type_error r_typ l_typ
    in
    loop l_typ r_typ
  (* Procefure qui verifie que la classe f_name est en-dessous de p_name dans la hierarchie de classe
   * p_name : string  le nom de la classe qui doit etre au dessus dans la hierarchie
   * f_name : string : le nom de la classe qui doit etre en dessous dans la hierarchie
   * *)
  and check_dyn_lia p_name f_name =
    let f_cls = List.find (fun c -> c.class_name = f_name) p.classes in
    match f_cls.parent with
    | Some parent_name ->
      if parent_name <> p_name then check_dyn_lia p_name parent_name
    | None ->
      if p_name <> f_name then
        error
          (Printf.sprintf "type %s is not a sub class of type %s" f_name p_name)
  (* Fonction qui verifie qu'il n'y a pas de boucle dans la hierarchie de classe et qui ajoute les attributs des classes mères à l'environnement de typage
   * cls_def : classe_def la classe fille
   * cls_name : string le nom de la classe fille pour ajouter correctement l'attribut dans l'environnement de typage
   * tenv : tenv l'environnement de typage
   * p : program
   * return : tenv l'environnement de typage dans lequel on ajoute les attributs des parents
   * *)
  and inheritance cls_def cls_name tenv p =
    let env = ref tenv in

    let rec loop cls_def inh_ht =
      match cls_def.parent with
      | None -> ()
      | Some parent_name -> (
        match Hashtbl.find_opt inh_ht parent_name with
        | Some _ -> error (Printf.sprintf "there is a loop in the hierarchy")
        | None ->
          let cls =
            match
              List.find_opt (fun c -> c.class_name = parent_name) p.classes
            with
            | Some cl -> cl
            | None ->
              error (Printf.sprintf "Class %s does not exist" parent_name)
          in
          env :=
            add_in_env (Printf.sprintf "%s." cls_name) cls.attributes !env p;
          Hashtbl.replace inh_ht parent_name ();
          loop cls inh_ht )
    in

    loop cls_def (Hashtbl.create 16);
    !env
  (* Fonction qui ajoute 1 élément dans l'environnement de typage
   * var : string * (typ * (vis option * bool * bool * bool))
   * env : tenv l'environnement de typage
   * p : program
   * return : tenv, l'environnement de typage
   * *)
  and add_env var env p =
    match fst (snd var) with
    | TVoid -> error "Il n'y a pas de variable de type void"
    | TClass s -> (
      match List.find_opt (fun c -> c.class_name = s) p.classes with
      | None -> error (Printf.sprintf "Class %s not exist" s)
      | Some cl ->
        let env = inheritance cl cl.class_name env p in
        let env =
          add_in_env (Printf.sprintf "%s." cl.class_name) cl.attributes env p
        in
        (* On ajoute les attributs a l'environnement de typage *)
        Env.add (fst var) (snd var)
          env (* On ajoute la variable a l'environnement de typage *) )
    | TArray t as typ_arr ->
      (* Procedure verifiant que l'array n'est pas un array de type void[]...[] *)
      let rec check_not_void typ =
        match typ with
        | TArray t -> check_not_void t
        | TVoid -> error (Printf.sprintf "%s not exist" (typ_to_string typ_arr))
        | _ -> ()
      in
      check_not_void typ_arr;
      Env.add (fst var) (snd var) env
    | _ -> Env.add (fst var) (snd var) env
  (* Ajoute tous les paramètres dans l'environnement de typage
   * l : (string * (typ * (vis option * bool * bool * bool))) list
   * tenv : tenv l'environnement de typage
   * p : program
   * *)
  and add_params l tenv p =
    List.fold_left (fun env (x, t) -> add_env (x, t) env p) tenv l
  (* Ajoute toutes la liste de variable dans l'environnement de typage
   * l : (string * (typ * (vis option * bool * bool * bool))) list
   * tenv : tenv l'environnement de typage
   * p : program
   * return : tenv
   * *)
  and add_var l tenv p = add_in_env "" l tenv p
  (* Ajoute tous les at dans l'environnement de typage
   * l : (((string * expr * vis_stc_fin) list * typ) list) list, liste des attributs
   * tenv : tenv l'environnement de typage
   * p : program
   * return : tenv
   * *)
  and add_in_env prefix l tenv p =
    List.fold_left
      (fun env (str_expr_l, typ) ->
        List.fold_left
          (fun env (s, expr, v_t_f) ->
            if v_t_f <> (None, false, false) && String.equal prefix "" then
              error
                "non fields variable cannot be declared with key words \
                 'static', 'final', 'private' or 'protected'";
            let attr_decl =
              match (v_t_f, expr) with
              | (_, true, true), ExprNull ->
                error
                  "static final fields have to be assigned a value when it is \
                   declared"
              | (v, s, f), ExprNull ->
                (typ, (v, f, false))
                (* false pour indiquer qu'un champ n'est pas initialise *)
              | (v, s, f), _ ->
                check expr typ env;
                (typ, (v, f, true))
              (* true pour indiquer qu'un champ est initialise *)
            in
            add_env (Printf.sprintf "%s%s" prefix s, attr_decl) env p )
          env str_expr_l )
      tenv l
  (* Fonction qui renvoie la sur-classe qui a la methode dont on passe le nom en argument
   * cls : class_def
   * mth_name : string nom de la methode
   * return : (method * typ) option la methode et le type de la classe
   *)
  and search_method_opt cls mth_name =
    match List.find_opt (fun m -> m.method_name = mth_name) cls.methods with
    | Some f ->
      Some (f, TClass cls.class_name) (* cls a une methode mth_name on a fini *)
    | None -> (
      (* sinon on verifie si la classe parent a une telle methode *)
      match cls.parent with
      | None as res -> res
      | Some s ->
        let o = List.find (fun c -> c.class_name = s) p.classes in
        search_method_opt o mth_name )
  (* Procedure qui verifie si les expressions de la liste d'expression lexpr a les memes types que la liste larg
   * lexpr : expr list
   * largs : typ list
   *)
  and verif_typ_args lexpr largs tenv =
    match (lexpr, largs) with
    | [], [] -> ()
    | e :: le, a :: la -> check e (snd a) tenv
    | le, [] -> error (Printf.sprintf "too many arguments in method call")
    | [], la -> error (Printf.sprintf "missing arguments in method call ")
  (* Fonction qui renvoie le type de retour de la methode dont le nom est passé en argument
   * cls_name : string nom de la classe
   * s : string nom de la methode dont on cherche le type
   * lexpr : expr list la liste des expressions passees en argument
   * tenv : tenv l'environnement de typage
   * return : typ
   * *)
  and check_type_method cls_name s lexpr tenv =
    let cl =
      match List.find_opt (fun c -> c.class_name = cls_name) p.classes with
      | None -> error (Printf.sprintf "%s is not a class" cls_name)
      | Some cl -> cl
    in
    match search_method_opt cl s with
    (* On cherche la classe a laquelle appartient la methode *)
    | None -> error (Printf.sprintf "%s has not %s method" cl.class_name s)
    | Some (m, t) ->
      ( if m.visible = Some Private then
          (* methode privee *)
          try
            let typ = type_expr This tenv in
            (* si la classe dans laquelle est defini la methode ne correspond pas au type de la classe appelante on renvoie une erreur *)
            if t <> typ then
              error "Private method cannot be called outside own class"
            (* si on a l'erreur ci-dessous cela veut dire que l'on est dans le main *)
          with Error "You cannot use 'this' outside of a method" ->
            error "cannot call Private method outside method"
        else if m.visible = Some Protected then
          (* methode protected *)
          try
            let _ = typ_to_string (type_expr This tenv) in
            ()
          with Error "You cannot use 'this' outside of a method" ->
            error "cannot call Protected method outside method" );
      verif_typ_args lexpr m.params tenv;
      (* on verifie que les expressions passees en argument sont de meme types que les parametres formels *)
      if String.equal s "constructor" then TClass cls_name
        (* si la methode est un constructeur on renvoie le type de la classe *)
      else m.return (* sinon on renvoie le type de retour *)
  (* Fonction qui renvoie la premiere classe dans la hierarchie de classe qui a attribut recherche
   * typ_cls : string option nom de classe
   * attr : string nom de l'attribut
   * return : string nom de classe dans lequel est declare le champ attr
   * *)
  and find_attribute typ_cls attr =
    match typ_cls with
    | None ->
      assert false
      (* Au moment ou l'on appelle cette fonction, on sait que ce champ existe dans une classe tester *)
    | Some typ_cls ->
      let cls = List.find (fun c -> c.class_name = typ_cls) p.classes in
      if
        List.exists
          (fun (a, _) -> List.exists (fun (s, _, _) -> s = attr) a)
          cls.attributes
      then cls.class_name
      else find_attribute cls.parent attr
  (* Procedure qui verifie les attributs privee ne puissent etre accedee qu'a partir de la classe dans laquelle ils ont ete declares
   * field : expr mem_access d'un champ
   * typ_x : (typ * (vis option * bool * bool * bool)) information sur la variable
   * tenv : tenv environnement de typage
   * *)
  and check_private_field field typ_x tenv =
    match field with
    | Field (o, s) -> (
      try
        let typ1 = typ_to_string (type_expr This tenv) in
        let typ2 = find_attribute (Some typ1) s in
        if not (String.equal typ1 typ2) then
          error "private field can only be accessed from own class"
      with Error "You cannot use 'this' outside of a method" ->
        error "private field cannot be accessed from outside methods" )
    | _ -> assert false
  (* Procedure qui verifie les attributs protected ne puissent etre accedee qu'a partir des sous-classes ou de la classe dans laquelle ils ont ete declares
   * field : expr mem_access d'un champ
   * typ_x : (typ * (vis option * bool * bool * bool)) information sur la variable
   * tenv : tenv environnement de typage
   * *)
  and check_protected_field x typ_x tenv =
    match x with
    | Field (o, s) -> (
      try
        let typ1 = typ_to_string (type_expr This tenv) in
        let typ2 = find_attribute (Some typ1) s in
        try check_dyn_lia typ2 typ1 (* tester *)
        with _ ->
          error "protected field can only be accessed from subclass class"
      with Error "You cannot use 'this' outside of a method" ->
        error "protected field cannot be accessed from outside methods" )
    | _ -> assert false
  (* Fonction qui renvoie le type de l'expression passee en argument
   * e : expr
   * tenv : tenv l'environnement de typage
   * return : typ
   * *)
  and type_expr e tenv =
    match e with
    | Int _ -> TInt
    | Bool _ -> TBool
    | Array l -> (
      match l with
      | [] -> TArray TVoid
      | e :: l ->
        let t = type_expr e tenv in
        List.iter (fun x -> check e t tenv) l;
        TArray t )
    | ArrayCreate (typ, l) -> (
      match typ with
      | TVoid | TArray _ ->
        error
          (Printf.sprintf "%s is not a correct for create_array"
             (typ_to_string typ) )
      | _ -> (
        let rec get_typ typ l =
          match l with [] -> typ | _ :: ll -> TArray (get_typ typ ll)
        in
        match l with
        | [] -> TArray TVoid
        | _ ->
          List.iter (fun x -> check x TInt tenv) l;
          get_typ typ l ) )
    | ArraySize e -> (
      match type_expr e tenv with
      | TArray _ -> TInt
      | typ ->
        error (Printf.sprintf "expected 'a array, got %s" (typ_to_string typ)) )
    | Binop ((Add | Mul | Sub | Div | Rem), e1, e2) ->
      check e1 TInt tenv;
      check e2 TInt tenv;
      TInt
    | Binop ((Lt | Le | Gt | Ge), e1, e2) ->
      check e1 TInt tenv;
      check e2 TInt tenv;
      TBool
    | Binop ((Eq | Neq | Seq | Sneq), e1, e2) ->
      let typ_e1 = type_expr e1 tenv in
      let typ_e2 = type_expr e2 tenv in
      if typ_e1 <> typ_e2 then type_error typ_e2 typ_e1;
      TBool
    | Binop ((And | Or), b1, b2) ->
      check b1 TBool tenv;
      check b2 TBool tenv;
      TBool
    | Unop (Not, b) ->
      check b TBool tenv;
      TBool
    | Unop (Opp, n) ->
      check n TInt tenv;
      TInt
    | Get m ->
      let mem = type_mem_access m tenv in
      ( match snd mem with
      | None, _, _ -> ()
      | Some Private, _, _ -> check_private_field m mem tenv
      | Some Protected, _, _ -> check_protected_field m mem tenv );
      fst mem
    | This -> (
      match Env.find_opt "this" tenv with
      | None -> error "You cannot use 'this' outside of a method"
      | Some o -> fst o )
    | New s -> (
      match List.find_opt (fun c -> c.class_name = s) p.classes with
      | None -> error (Printf.sprintf "%s is not a class" s)
      | Some _ -> TClass s )
    | NewCstr (c, expr) -> (
      match List.find_opt (fun cls -> cls.class_name = c) p.classes with
      | None -> error (Printf.sprintf "%s is not a class" c)
      | Some cl -> check_type_method cl.class_name "constructor" expr tenv )
    | MethCall (e, s, lexpr) -> (
      match type_expr e tenv with
      | TClass cl -> check_type_method cl s lexpr tenv
      | _ -> error (Printf.sprintf "") )
    | SuperCall (s, lexpr) -> (
      match Env.find_opt "this" tenv with
      | None -> error "You cannot use 'super' outside of a method"
      | Some o -> (
        let cls =
          List.find (fun cls -> TClass cls.class_name = fst o) p.classes
        in
        match cls.parent with
        | None -> error "current object has no parent class"
        | Some p_name -> check_type_method p_name s lexpr tenv ) )
    | Instanceof (expr, typ) -> (
      match (type_expr expr tenv, typ) with
      | TClass _, TClass _ -> TBool
      | typ, TClass _ | TClass _, typ ->
        error (Printf.sprintf "expected 'a class, got %s" (typ_to_string typ))
      | typ1, typ2 ->
        let s1 = typ_to_string typ1 in
        let s2 = typ_to_string typ2 in
        error
          (Printf.sprintf
             "expected 'a class instanceof 'b class, got %s instanceof %s" s1 s2 )
      )
    | ExprNull -> assert false
  (* fonction qui renvoie les informations sur les variables et attributs stockés dans l'environnement de typage
   * m : mem_access
   * tenv : tenv environnement de typage
   * return : (typ * (vis option * bool * bool * bool))
   * *)
  and type_mem_access m tenv =
    match m with
    | Var x -> (
      match Env.find_opt x tenv with
      | Some t -> t
      | None ->
        let msg = Printf.sprintf "variable '%s' not declared" x in
        error_not_found msg x "" tenv )
    | Field (o, s) -> (
      match type_expr o tenv with
      | TClass nm -> (
        let name = Printf.sprintf "%s.%s" nm s in
        match Env.find_opt name tenv with
        | Some t -> t
        | None ->
          let msg = Printf.sprintf "object doesn't have attribute %s" s in
          error_not_found msg name "" tenv )
      | _ -> (
        let msg = Printf.sprintf "expr is not a class in <expr>.%s " s in
        match o with
        | Get (Var x) -> error_not_found msg x (Printf.sprintf ".%s" s) tenv
        | _ -> error msg ) )
    | ArrField (e1, e2) -> (
      match type_expr e1 tenv with
      | TArray t ->
        check e2 TInt tenv;
        (t, (None, false, true))
      | typ ->
        error
          (Printf.sprintf "An array was expected, not a %s" (typ_to_string typ))
      )
  (* Procedure qui souleve une erreur lorsque l'on cherche a acceder un mem_access qui n'existe pas *)
  and error_not_found msg_error s suffixe tenv =
    let s_length = String.length s in
    let limit_error = if s_length <= 5 then 1 else 2 in

    let calc_nb_error ident_map ident_prog length =
      let nb_error = ref 0 in
      let score = ref 0 in

      let rec loop i =
        if !nb_error > limit_error then None
        else if i < 0 then Some (!nb_error, !score)
        else
          let c_prog = ident_prog.[i] in
          let c_map = ident_map.[i] in

          if c_map <> c_prog then begin
            incr nb_error;
            score := abs (Char.code c_map - Char.code c_prog) + !score
          end;

          loop (i - 1)
      in

      loop (length - 1)
    in

    let nearest_ident () =
      (* res = ref (ident, nb_error, score) *)
      let res = ref ("", limit_error + 1, 0) in

      Env.iter
        (fun key _ ->
          let key_length = String.length key in
          if abs (key_length - s_length) <= limit_error && key <> s then
            match calc_nb_error key s (min key_length s_length) with
            | None -> ()
            | Some (new_nb_error, new_score) ->
              let _, old_nb_error, old_score = !res in
              if
                new_nb_error < old_nb_error
                || (new_nb_error = old_nb_error && new_score < old_score)
              then res := (key, new_nb_error, new_score) )
        tenv;

      !res
    in

    let str, nb_error, _ = nearest_ident () in

    if nb_error <= limit_error then
      error (Printf.sprintf "Did you mean '%s%s' ?" str suffixe)
    else error msg_error
  in

  (* Procedure verifiant le bon typage des instructions *)
  let rec check_instr i ret tenv =
    match i with
    | Print e | Println e -> (
      match type_expr e tenv with
      | TInt | TBool | TClass _ | TArray _ -> ()
      | t ->
        error
          (Printf.sprintf "print operation not implemented for type %s"
             (typ_to_string t) ) )
    | If (b, s1, s2) ->
      check b TBool tenv;
      check_seq s1 ret tenv;
      check_seq s2 ret tenv
    | While (b, s) ->
      check b TBool tenv;
      check_seq s ret tenv
    | Break | Continue -> ()
    | Set (x, e) ->
      let typ_x = type_mem_access x tenv in
      ( match snd typ_x with
      | _, true, _ -> error "cannot change value of final field"
      | None, false, _ -> ()
      | Some Private, false, _ -> check_private_field x typ_x tenv
      | Some Protected, false, _ -> check_protected_field x typ_x tenv );
      check e (fst typ_x) tenv
    | Expr e ->
      let _ = type_expr e tenv in
      () (* On appelle type_expr pour vérifier que e soit bien type *)
    | Return e -> (
      match ret with
      | TVoid -> error (Printf.sprintf "return instruction outside a method")
      | _ -> check e ret tenv )
  (* Fonction qui verifie le bon typage des constructeurs et qui renvoie un environnement nous permettant de determiner si
   * s : seq le code du constructeur
   * ret : typ
   * cls_def : class_def la classe du constructeur
   * tenv : tenv environnement de typage
   * return : tenv un environnement où les attributs initialises dans le constructeur sont considerees comme initialises dans l'environnement
   * *)
  and check_constr s ret cls_def tenv =
    (* Fonction qui verifie le bon typage d'une instruction dans le constructeur *)
    let rec check_instr_constr i ret cur_cls tenv =
      (* Fonction qui renvoie un environnement dans lequel le type de this correspond pas au type de l'objet courant mais a celui du pere de l'objet courant s'il en existe un
       * On utiliser cette fonction pour eviter un bug avec les attributs prive et super.constructor lorsque l'on verifie le bon typages des constructeurs
       * tenv : tenv environnement de typage
       * return : tenv environnement de typage modifie
       *)
      let setup_parent tenv =
        Env.add "this" (TClass cur_cls.class_name, (None, false, true)) tenv
      in
      (* Fonction qui renvoie un environnement modifie dans lequel l'attribut passe en argument est considere comme initialise dans l'environnement *)
      let init x typ_x vis fin tenv =
        match x with
        | Field (o, s) ->
          let nm_class = cls_def.class_name in
          Env.add
            (Printf.sprintf "%s.%s" nm_class s)
            (fst typ_x, (vis, fin, true))
            tenv
        | _ ->
          error
            (Printf.sprintf "In constructor of %s, expected a field but got %s"
               cls_def.class_name
               (typ_to_string (fst typ_x)) )
      in
      match i with
      | Expr (SuperCall (s, lexpr)) -> (
        (* On verifie les attributs sont bien intialise dans le constructeur de la classe mere *)
        let cl =
          List.find
            (fun cls -> String.equal cls.class_name cur_cls.class_name)
            p.classes
        in
        match cl.parent with
        | None -> error "current object has no parent class"
        | Some p_name -> (
          let p_cls =
            List.find (fun cls -> String.equal cls.class_name p_name) p.classes
          in
          (* On trouve la classe parent *)
          let s_cls = search_method_opt p_cls s in
          (* On cherche la methode appele avec super et le type de la classe qui a la methode *)
          match s_cls with
          | Some (mth, TClass sup_name) ->
            let sup_cls =
              List.find
                (fun cls -> String.equal cls.class_name sup_name)
                p.classes
            in
            (* On trouve la classe_def qui a la methode *)
            (* On transforme les informations de typage dans une forme de l'environnement de typage *)
            let mth_params =
              List.map (fun (k, t) -> (k, (t, (None, false, true)))) mth.params
            in
            (* On ajoute les parametre dans l'environnement de typage *)
            let tenv = add_params mth_params tenv p in
            (* On verifie le bon typage des expressions passees en argument *)
            let _ = check_type_method sup_name s lexpr tenv in
            List.fold_left
              (fun tenv i ->
                let tenv = check_instr_constr i mth.return sup_cls tenv in
                tenv )
              tenv mth.code
            (* On verifie le code de la methode appelle avec super afin de pouvoir mettre a jour l'environnement de typage correctement.
               Comme l'appel super est dans le constructeur on verifie le code de la methode comme si c'etait un constructeur.
            *)
          | _ -> error "no super constructor" ) )
      | Set (x, e) ->
        let typ_x = type_mem_access x tenv in
        let tenv =
          match snd typ_x with
          | _, true, true ->
            error "cannot change value of final field" (* final initialized *)
          | (None as v), fin, false ->
            init x typ_x v fin tenv (* Public non initialized *)
          | (Some Private as v), fin, false ->
            let env = setup_parent tenv in
            check_private_field x typ_x env;
            init x typ_x v fin tenv (* Private non initialized *)
          | (Some Protected as v), fin, false ->
            check_protected_field x typ_x tenv;
            init x typ_x v fin tenv
          | Some Private, _, _ ->
            let env = setup_parent tenv in
            check_private_field x typ_x env;
            tenv
          | Some Protected, _, _ ->
            check_protected_field x typ_x tenv;
            tenv
          | _, false, true -> tenv
        in
        check e (fst typ_x) tenv;
        tenv
      | _ ->
        check_instr i ret tenv;
        tenv
    in
    List.fold_left
      (fun tenv i ->
        let tenv = check_instr_constr i ret cls_def tenv in
        tenv )
      tenv s
  and check_seq s ret tenv = List.iter (fun i -> check_instr i ret tenv) s
  (* Fonction qui verifie le bon typage d'une methode
   * tenv : tenv l'environnement de typage
   * cls_def : class_def
   * mth : method_def
   * return : tenv * bool le booleen indique si la methode que l'on a check est un constructeur
   * *)
  and check_mth tenv cls_def mth =
    let mth_params =
      List.map (fun (k, t) -> (k, (t, (None, false, true)))) mth.params
    in
    let tenv = add_params mth_params tenv p in
    let tenv = add_var mth.locals tenv p in
    let tenv =
      Env.add "this" (TClass cls_def.class_name, (None, false, true)) tenv
    in

    if mth.method_name = "constructor" then (
      let tenv = check_constr mth.code mth.return cls_def tenv in
      (* a la fin d'un constructeur les attributs "publics" et que les attributs finaux doivent etre initialises*)
      let non_init_null s x =
        let cls_iden = Printf.sprintf "%s." cls_def.class_name in
        if
          String.length cls_iden < String.length s
          && String.equal cls_iden (String.sub s 0 (String.length cls_iden))
        then
          match snd x with
          | _, true, false -> error "no value assigned to final field"
          | None, false, false ->
            error "no value assigned to public attribute in constructor"
          | _ -> ()
      in
      Env.iter non_init_null tenv;
      (tenv, true) )
    else (
      check_seq mth.code mth.return tenv;
      (tenv, false) )
  and check_cls tenv cls_def =
    (* procedure renvoyant une erreur si l'element passe en argument est final et non initialisee *)
    let final_null s x =
      let cls_iden = Printf.sprintf "%s." cls_def.class_name in
      if
        String.length cls_iden < String.length s
        && String.equal cls_iden (String.sub s 0 (String.length cls_iden))
      then
        match snd x with
        | _, true, false -> error "no value assigned to final field"
        | _ -> ()
    in
    let tenv = inheritance cls_def cls_def.class_name tenv p in
    let tenv =
      add_in_env
        (Printf.sprintf "%s." cls_def.class_name)
        cls_def.attributes tenv p
    in
    let tenv, has_cstr =
      List.fold_left
        (fun (tenv, b) mth ->
          let tenv, fl = check_mth tenv cls_def mth in
          (tenv, b || fl) )
        (tenv, false) cls_def.methods
    in
    (* Puisque les declarations d'attributs des classes filles peuvent ecraser les declarations d'attributs des classes mere, il est possible que l'on doive
       verifier le bon typage du code des methode herite. Cependant, cela n'a pas l'air d'etre fait en Java, On a donc decider de ne pas le faire.
     * *)
    if not has_cstr then
      (* dans les classes sans construteur, on regarde seulement que les variables finales soient bien initialises lors de leur declaration *)
      let tenv =
        (* On regarde si la classe n'herite pas d'un constructeur *)
        match search_method_opt cls_def "constructor" with
        | Some (mth, TClass sup_name) -> fst (check_mth tenv cls_def mth)
        | _ -> tenv
      in
      Env.iter final_null tenv
  and check_classes l tenv =
    let class_ht = Hashtbl.create 16 in
    List.iter
      (fun cls ->
        let cls_name = cls.class_name in
        match Hashtbl.find_opt class_ht cls_name with
        | None ->
          check_cls tenv cls;
          Hashtbl.replace class_ht cls_name ()
        | Some _ -> error (Printf.sprintf "duplicate class %s" cls_name) )
      l
  in

  let tenv = add_var p.globals Env.empty p in
  check_classes p.classes tenv;
  check_seq p.main TVoid tenv
