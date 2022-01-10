
(* Module de la passe de gestion des identifiants *)
module PasseCodeRatToTam : Passe.Passe with type t1 = Ast.AstPlacement.programme and type t2 = string =
struct

  open Tds
  open Ast
  open Type
  open Code

  type t1 = Ast.AstPlacement.programme
  type t2 = string

let rec utiliser_id_pointeur affectable droite_instruction =
  match affectable with 
    | AstType.Ident(info) -> 
      begin 
        match info_ast_to_info info with 
        |InfoVar (_,typ,base,r) -> if droite_instruction then
            let taille = string_of_int(getTaille typ) in
            "LOAD "^"("^taille^")"^" "^string_of_int base^"["^r^"] \n"^
            "LOADI "^"("^taille^")\n"
          else
            let taille = string_of_int(getTaille typ) in
            "LOAD "^"("^taille^")"^" "^string_of_int base^"["^r^"] \n"^
            "STOREI "^"("^taille^")\n"
        | _ -> failwith "erreur interne"
      end
    | AstType.Dref(sous_affect) -> utiliser_id_pointeur sous_affect droite_instruction
    |_ -> failwith "intern error cela ne doit pas un cons"

let analyse_code_affectable aff = 
begin 
  match aff with
  | AstType.Ident (n) -> 
    begin
      match info_ast_to_info n with 
        | InfoVar (_,t,base,r) ->   
          let taille = string_of_int (getTaille t) in
          "LOAD "^"("^taille^")"^" "^string_of_int base^"["^r^"] \n"
        | _ ->  failwith "erreur interne"
    end
  | AstType.Dref(affectable)-> utiliser_id_pointeur affectable true
  | AstType.EntierCons(entier) -> "LOADL " ^ string_of_int entier ^"\n"
  | AstType.Champ(_) -> failwith "internal error, pas encore fait, ne peut pas rentrer dans ce cas"
end

(* analyse_tds_expression : AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
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
      String.concat "" (List.map analyse_code_expression eliste) ^ "CALL (ST) " ^ nom_f^ "\n"
    | AstType.Booleen (b) -> if b then "LOADL 1 \n" else "LOADL 0 \n"
    | AstType.Entier (i) ->  "LOADL " ^ string_of_int i ^"\n"
    | AstType.Unaire (u, e1) -> (analyse_code_expression e1)^(match u with
          | Numerateur -> "POP (0) 1 \n"
          | Denominateur  -> "POP (1) 1 \n")
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
    | AstType.Null -> "SUBR MVoid \n"
    | AstType.NouveauType(typ) -> "LOADL "^string_of_int(getTaille typ)^
          "\nSUBR MAlloc \n"
    | AstType.Adresse(info) ->
      begin
      match info_ast_to_info info with 
        |InfoVar (_,_,base,r) ->   
          "LOADA "^string_of_int base^"["^r^"] \n"
        | _ -> failwith "erreur interne"
      end
    | AstType.ListeChamp(_) -> failwith "internal error, pas encore fait, ne peut pas rentrer dans ce cas"
    

(* analyse_tds_instruction : AstSyntax.instruction -> tds -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_code_instruction i (nb_p, t)  =
  begin
  match i with
    | AstType.Declaration (n, e) -> 
      begin 
      match info_ast_to_info n with 
      |InfoVar (_,typ,b,r) ->   
        let taille = string_of_int(getTaille typ) in
        ("PUSH "^taille^"\n"^ 
        (analyse_code_expression e)^
        "STORE ("^taille^") "^(string_of_int b)^"["^r^"]"^"\n",1)
      | _ -> failwith "erreur interne"
      end
  | AstType.AffectationPointeur (aff,e) ->
      begin
      match aff with 
        | Ident(n) -> 
            begin 
            match info_ast_to_info n with 
            | InfoVar (_,typ,b,r) -> 
              let taille = string_of_int(getTaille typ) in
              ((analyse_code_expression e)^"STORE ("^taille^") " ^(string_of_int b)^"["^r^"] \n", 0)
            | _ -> failwith "internal error"
            end
        |Dref(affectable) -> ((analyse_code_expression e)^(utiliser_id_pointeur affectable false),0)
        | _ -> failwith "internal error cela peut pas etre un Cons"
      end
  | AstType.AffichageInt e -> ((analyse_code_expression e)^"SUBR IOut \n",0)

  | AstType.AffichageRat e -> ((analyse_code_expression e)^"CALL (ST) ROut \n",0)

  | AstType.AffichageBool e -> ((analyse_code_expression e)^"SUBR BOut \n",0)
      
  | AstType.Conditionnelle (c,f,e) -> let vrai = getEtiquette () in
                                           let fin = getEtiquette () in
                                           ((analyse_code_expression c)^"JUMPIF (1) "^vrai^"\n"^
                                           (analyse_code_bloc e (nb_p, t) )^"JUMP "^fin^"\n"^
                                           vrai^"\n"^(analyse_code_bloc f (nb_p, t))^fin^"\n",0)

                                          
  | AstType.TantQue (c,b) -> let depart= getEtiquette () in
                                  let fin = getEtiquette () in
                            (depart^"\n" ^ (analyse_code_expression c ) ^"JUMPIF (0) " ^ fin ^"\n" ^
                            (analyse_code_bloc b (nb_p, t))^"JUMP "^depart^"\n"^fin^"\n",0)
     
  | AstType.Retour (e) -> ( analyse_code_expression e^ "RETURN ("^string_of_int t ^") "^string_of_int nb_p^"\n",0)
  | AstType.Empty-> ("",0) 
  end
      
(* analyse_tds_bloc : AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_code_bloc li (nb_p, t) =
  let listeanalyse = (List.map (fun i -> 
                          analyse_code_instruction i (nb_p, t)) li) in 
  let compteur = (List.fold_right (fun t i -> i+snd(t)) listeanalyse 0) in
  let listestring = String.concat "" (List.map(fun i -> fst(i)) listeanalyse) in

  listestring^"POP (0) "^string_of_int compteur ^"\n"
  
(* analyse_tds_fonction : AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let recuper_nombre_memoire liste=
  begin
  match liste with 
    | []-> 0
    | t::_ -> 
      match info_ast_to_info t with
        | InfoVar(_,_,placement_derniere_variable,_) -> -placement_derniere_variable
        | _ -> failwith "Interne error"
      end

let analyse_code_fonction (AstPlacement.Fonction(n,lp,li))  =
  match info_ast_to_info n with
    | InfoFun(nom,nb_retour,_) -> "\n"^nom^"\n"^analyse_code_bloc li (recuper_nombre_memoire lp, getTaille nb_retour)^ "HALT\n"
    | _ -> failwith "internal error"


  

let analyser (AstPlacement.Programme (fonctions,prog)) =
  getEntete() ^  (String.concat "" (List.map analyse_code_fonction fonctions)) ^"\n"^ "main \n"^analyse_code_bloc prog (0,0) ^ "\nHALT\n"
end
