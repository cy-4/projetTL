
(* Module de la passe de gestion des identifiants *)
module PasseCodeRatToTam : Passe.Passe with type t1 = Ast.AstPlacement.programme and type t2 = string =
struct

  open Tds
  open Ast
  open Type
  open Code

  type t1 = Ast.AstPlacement.programme
  type t2 = string

(* utiliser_id_pointeur : AstType.affectable -> bool-> string *)
(* Paramètre aff : l'affectable à manipuler *)
(* Paramètre droite_instruction : savoir si l'affectable est à droite de l'instruction ou non*)
(* Transforme l'affections en code assembleur *)
let rec utiliser_id_pointeur affectable droite_instruction =
  match affectable with 
    | AstType.Ident(info) -> 
      begin 
        match info_ast_to_info info with 
        |InfoVar (_,typ,base,r) -> if droite_instruction then
            (* Si le pointeur se trouve à droite, on fait un LOADI*)
            let taille = string_of_int(getTaille typ) in
            "LOAD "^"("^taille^")"^" "^string_of_int base^"["^r^"] \n"^
            "LOADI "^"("^taille^")\n"
          else
            (* Si le pointeur se trouve à droite, on fait un STOREI*)
            let taille = string_of_int(getTaille typ) in
            "LOAD "^"("^taille^")"^" "^string_of_int base^"["^r^"] \n"^
            "STOREI "^"("^taille^")\n"
        | _ -> failwith "erreur interne"
      end
    (* Il faut déréférencé jusqu'à tomber sur l'info*)
    | AstType.Dref(sous_affect) -> utiliser_id_pointeur sous_affect droite_instruction
    |_ -> failwith "intern error cela ne doit pas un cons"


(* analyse_code_affectable : AstType.affectable -> string *)
(* Paramètre aff : l'affectable à manipuler *)
(* Transforme l'affections en code assembleur *)
let analyse_code_affectable aff = 
begin 
  match aff with
  | AstType.Ident (n) -> 
    begin
      match info_ast_to_info n with 
        | InfoVar (_,t,base,r) ->   
          (* On load la valeur se trouvant dans la variable*)
          let taille = string_of_int (getTaille t) in
          "LOAD "^"("^taille^")"^" "^string_of_int base^"["^r^"] \n"
        | _ ->  failwith "erreur interne"
    end
  | AstType.Dref(affectable)-> utiliser_id_pointeur affectable true
  (* On Load la constante qu'on a remplacé par sa valeur dans la passe Tds*)
  | AstType.EntierCons(entier) -> "LOADL " ^ string_of_int entier ^"\n"
  | AstType.Champ(_) -> failwith "internal error, pas encore fait, ne peut pas rentrer dans ce cas"
end

(* analyse_code_expression : AstType.expression -> string *)
(* Paramètre aff : l'affectable à manipuler *)
(* Transforme l'expression en code assembleur  *)
let rec analyse_code_expression e = 
  match e with 
    | AstType.AppelFonction (f,eliste) ->
      let nom_f = (
        begin
        match info_ast_to_info f with 
        | InfoVar(nom,_,_,_)-> nom
        | InfoFun(nom,_,_) -> nom
        | _ -> failwith "erreur interne pas de InfoVar"
        end) in
      (* On met le code assembleur des paramètres de la fonction avant de mettre le CALL (ST) "la fonction"*)
      String.concat "" (List.map analyse_code_expression eliste) ^ "CALL (ST) " ^ nom_f^ "\n"
    (* Vrai est représenté par un 1 et Faux par 0*)
    | AstType.Booleen (b) -> if b then "LOADL 1 \n" else "LOADL 0 \n"
    (* On LOAD la valeur de l'entier*)
    | AstType.Entier (i) ->  "LOADL " ^ string_of_int i ^"\n"
    (* Selon si c'est un Denominateur ou un Numérateur on pop la dernière instruction ou l'avant dernière*)
    | AstType.Unaire (u, e1) -> (analyse_code_expression e1)^(match u with
          | Numerateur -> "POP (0) 1 \n"
          | Denominateur  -> "POP (1) 1 \n")
    (* On appelle selon le type des expression une fonction soit directement native de TAM (SUBR)
     ou rajouté à la mai (CALL (ST))*)
    | AstType.Binaire (b, e1, e2) -> (analyse_code_expression e1)^(analyse_code_expression e2)^(match b with 
          |PlusRat -> "CALL (ST) RAdd \n"
          |MultRat -> "CALL (ST) RMul \n"   
          |Fraction -> "CALL (ST) norm \n"
          |PlusInt -> "SUBR IAdd \n"
          |MultInt -> "SUBR IMul \n"
          |EquInt  -> "SUBR IEq \n"
          |EquBool -> "SUBR IEq \n"
          |Inf -> "SUBR ILss \n" )
    | AstType.Affectable(aff) -> analyse_code_affectable aff
    (* Renvoie la valeur « adresse non initialisée »*)
    | AstType.Null -> "SUBR MVoid \n"
    (* Renvoie l'addresse d'un emplacement mémoire de taille getTaille typ*)
    | AstType.NouveauType(typ) -> "LOADL "^string_of_int(getTaille typ)^
          "\nSUBR MAlloc \n"
    (* Renvoie l'addresse de la variable se trouvant à base [r] du pointeur*)
    | AstType.Adresse(info) ->
      begin
      match info_ast_to_info info with 
        |InfoVar (_,_,base,r) ->   
          "LOADA "^string_of_int base^"["^r^"] \n"
        | _ -> failwith "erreur interne"
      end
    | AstType.ListeChamp(_) -> failwith "internal error, pas encore fait, ne peut pas rentrer dans ce cas"
    

(* analyse_code_instruction : AstType.instruction -> string *)
(* Paramètre i : l'instruction à manipuler *)
(* Parametre (nb_p, t): nb_p correspond à la taille des paramètre et t la taille du résultat *)
(* Transforme l'instruction en code assembleur et renvoie la taille que ça a pris 
(juste pour une déclaration du coup)*)
let rec analyse_code_instruction i (nb_p, t)  =
  begin
  match i with
    | AstType.Declaration (n, e) -> 
      begin 
      match info_ast_to_info n with 
      |InfoVar (_,typ,b,r) ->
        (* On PUSH la taille de l'expression*)   
        let taille = string_of_int(getTaille typ) in
        ("PUSH "^taille^"\n"^ 
        (* On rajoute l'expression qu'on va enregister*)
        (analyse_code_expression e)^
        (* On enregistre le résultat dans la variable*)
        "STORE ("^taille^") "^(string_of_int b)^"["^r^"]"^"\n",getTaille typ)
      | _ -> failwith "erreur interne"
      end
  | AstType.AffectationPointeur (aff,e) ->
      begin
      match aff with 
        | Ident(n) -> 
            begin 
            match info_ast_to_info n with 
            | InfoVar (_,typ,b,r) -> 
              (* On enregistre le résultat dans la variable*)
              let taille = string_of_int(getTaille typ) in
              ((analyse_code_expression e)^"STORE ("^taille^") " ^(string_of_int b)^"["^r^"] \n", 0)
            | _ -> failwith "internal error"
            end
        (* Si c'est un pointeur, on fait appel à utiliser_id_pointeur pour mettre le code TAM du pointeur*)
        |Dref(affectable) -> ((analyse_code_expression e)^(utiliser_id_pointeur affectable false),0)
        | _ -> failwith "internal error cela peut pas etre un Cons"
      end
  (* Instruction d'affichage pour un Entier*)
  | AstType.AffichageInt e -> ((analyse_code_expression e)^"SUBR IOut \n",0)
  (* Instruction d'affichage pour un Rat*)
  | AstType.AffichageRat e -> ((analyse_code_expression e)^"CALL (ST) ROut \n",0)
  (* Instruction d'affichage pour un Entier/Bool*)
  | AstType.AffichageBool e -> ((analyse_code_expression e)^"SUBR BOut \n",0)
  (* On met des étiquettes pour y aller selon le resultat du code TAM de c*)
  | AstType.Conditionnelle (c,f,e) -> let vrai = getEtiquette () in
                                           let fin = getEtiquette () in
                                           ((analyse_code_expression c)^"JUMPIF (1) "^vrai^"\n"^
                                           (analyse_code_bloc e (nb_p, t) )^"JUMP "^fin^"\n"^
                                           vrai^"\n"^(analyse_code_bloc f (nb_p, t))^fin^"\n",0)

  (* On met des étiquettes pour y aller selon le resultat du code TAM de c*)                                   
  | AstType.TantQue (c,b) -> let depart= getEtiquette () in
                                  let fin = getEtiquette () in
                            (depart^"\n" ^ (analyse_code_expression c ) ^"JUMPIF (0) " ^ fin ^"\n" ^
                            (analyse_code_bloc b (nb_p, t))^"JUMP "^depart^"\n"^fin^"\n",0)
  (* On utilise les paramètres données à la fonction pour mettre les parametre de RETURN*)
  | AstType.Retour (e) -> ( analyse_code_expression e^ "RETURN ("^string_of_int t ^") "^string_of_int nb_p^"\n",0)
  | AstType.Empty-> ("",0) 
  end
      
(* analyse_code_bloc : AstType.bloc -> string *)
(* Paramètre li : liste d'inscription *)
(* Parametre (nb_p, t): nb_p correspond à la taille des paramètre et t la taille du résultat *)
(* Transforme la liste d'instruction en code assembleur *)
and analyse_code_bloc li (nb_p, t) =
  (* Récupére une liste de (string*int)*)
  let listeanalyse = (List.map (fun i -> 
                          analyse_code_instruction i (nb_p, t)) li) in 
  (* Compteur correspond à la taille à Pop à la fin du bloc*)
  let compteur = (List.fold_right (fun t i -> i+snd(t)) listeanalyse 0) in
  (* On récupere le string de listeanalyse*)
  let listestring = String.concat "" (List.map(fun i -> fst(i)) listeanalyse) in

  listestring^"POP (0) "^string_of_int compteur ^"\n"
  
(* recuper_nombre_memoire : info.ast liste -> int *)
(* Paramètre listeparametre : une liste d'info.Ast *)
(* On récupére le placement du premier parametre de la fonction qui correspond à
la taille des paramètre, utile quand on voudra utiliser le RETURN*)
let recuper_nombre_memoire listeparametre=
  begin
  match listeparametre with 
    | []-> 0
    | t::_ -> 
      match info_ast_to_info t with
        | InfoVar(_,_,placement_derniere_variable,_) -> -placement_derniere_variable
        | _ -> failwith "Interne error"
      end

(* analyse_code_fonction : AstType.fonction -> string *)
(* Paramètre lafonction : la fonction à manipuler *)
(* On génere le code TAM associé à la fonction*)
let analyse_code_fonction (AstPlacement.Fonction(n,lp,li))  =
  match info_ast_to_info n with
    | InfoFun(nom,nb_retour,_) -> "\n"^nom^"\n"^analyse_code_bloc li (recuper_nombre_memoire lp, getTaille nb_retour)^ "HALT\n"
    | _ -> failwith "internal error"


  
(* analyser : AstType.programme -> string *)
(* Paramètre leprogamme : le programme à manipuler *)
(* On génere le code TAM associé au programme*)
let analyser (AstPlacement.Programme (fonctions,prog)) =
  (* On assemble tous les strings obtenus grace aux programmes précédents*)
  getEntete() ^  (String.concat "" (List.map analyse_code_fonction fonctions)) ^"\n"^ "main \n"^analyse_code_bloc prog (0,0) ^ "\nHALT\n"
end
