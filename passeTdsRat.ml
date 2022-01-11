(* Module de la passe de gestion des identifiants *)

module PasseTdsRat : Passe.Passe with type t1 = Ast.AstSyntax.programme and type t2 = Ast.AstTds.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstTds

  type t1 = Ast.AstSyntax.programme
  type t2 = Ast.AstTds.programme

(* analyse_tds_affectable : AstSyntax.affectable -> AstTds.affectable *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre aff : l'affectable à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'affectable
en une affectable de type AstTds.affectable *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_affectable tds aff = 
  begin 
  match aff with
  | AstSyntax.Ident(identificateur)-> begin
    match chercherGlobalement tds identificateur with
    | None -> 
      raise (IdentifiantNonDeclare identificateur)
    | Some info -> 
      begin
      match info_ast_to_info info with 
      (* On rajoute un 2e parametre de retour car on besoin du nom de l'identifiant
      pour pouvoir soulever l'exception MauvaiseUtilisationIdentifiant 
      dans AffectationPointeur *)
      | InfoVar _ ->
         (AstTds.Ident(info),identificateur)
      (* Correspond à remplacer l'identicateur par sa valeur*)
      | InfoConst(_,v) -> 
        (AstTds.EntierCons(v),identificateur)
      | _ ->
        raise (MauvaiseUtilisationIdentifiant identificateur)
      end
    end
  (* On déréférence jusqu'à tomber sur l'identificateur et faire les vérif*)
  | AstSyntax.Dref(affectable)-> 
    let (newaff,id)=analyse_tds_affectable tds affectable in
    (AstTds.Dref(newaff),id)
  | AstSyntax.Champ(_,_) ->  failwith "internal error, pas encore fait, on devrait pas rentrer dans ce cas"
  end


(* analyse_tds_expression : AstSyntax.expression -> AstTds.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'expression
en une expression de type AstTds.expression *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_expression tds e = 
   match e with 
   | AstSyntax.AppelFonction (f,eliste) -> 
      begin
      match chercherGlobalement tds f with
      | None -> 
        raise (IdentifiantNonDeclare f)
      | Some info ->
        begin
        match info_ast_to_info info with
        | InfoFun _ -> 
          let l = List.map(fun t -> analyse_tds_expression tds t) eliste  in
          AstTds.AppelFonction(info, l)
        | _ ->
          raise (MauvaiseUtilisationIdentifiant f)
        end
      end
    | AstSyntax.Affectable (aff) -> AstTds.Affectable(fst(analyse_tds_affectable tds aff))
    | AstSyntax.Booleen (b) -> AstTds.Booleen(b)
    | AstSyntax.Entier (i) -> AstTds.Entier(i)
    | AstSyntax.Unaire (u, e1) -> AstTds.Unaire(u, analyse_tds_expression tds e1)
    | AstSyntax.Binaire (b, e1, e2) -> AstTds.Binaire (b, analyse_tds_expression tds e1, analyse_tds_expression tds e2 )
    | AstSyntax.Null ->  AstTds.Null
    | AstSyntax.NouveauType(typ) ->  AstTds.NouveauType(typ)
    | AstSyntax.Adresse(addr) ->   
      begin
      match chercherGlobalement tds addr with
      | None -> 
        raise (IdentifiantNonDeclare addr)
      | Some info -> 
        begin
        match info_ast_to_info info with 
        | InfoVar _ -> 
          AstTds.Adresse(info)
        | _ ->
          raise (MauvaiseUtilisationIdentifiant addr)
        end
      end
    | AstSyntax.ListeChamp(_) -> failwith "internal error, pas encore fait, on devrait pas rentrer dans ce cas"
          




(* analyse_tds_instruction : AstSyntax.instruction -> tds -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_tds_instruction tds i =
  match i with
  | AstSyntax.Declaration (t, n, e) ->
    begin
    match chercherLocalement tds n with
    | None ->
      begin
      (* On regarde si le type déclaré est un TypeNomme, dans ce cas,
      on remplace le type nommé par le type associé récursivement*)
      match t with 
      | TypeNomme(nom) ->   
        begin
        match chercherGlobalement tds nom with
          | Some info -> 
            begin
            match info_ast_to_info info with
            | InfoVar(_,typ,_,_) ->  
              analyse_tds_instruction tds (AstSyntax.Declaration(typ, n, e))
            | _ -> failwith "internal error, l'info aurait du etre un InfoVar"
            end
          |None  -> 
            raise (IdentifiantNonDeclare nom)
        end
      | _ ->
        (* L'identifiant n'est pas trouvé dans la tds locale, 
        il n'a donc pas été déclaré dans le bloc courant *)
        (* Vérification de la bonne utilisation des identifiants dans l'expression *)
        (* et obtention de l'expression transformée *) 
        let ne = analyse_tds_expression tds e in
        (* Création de l'information associée à l'identfiant *)
        let info = InfoVar (n,Undefined, 0, "") in
        (* Création du pointeur sur l'information *)
        let ia = info_to_info_ast info in
        (* Ajout de l'information (pointeur) dans la tds *)
        ajouter tds n ia;
        (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information 
        et l'expression remplacée par l'expression issue de l'analyse *)
        Declaration (t, ia, ne) 
      end
    | Some _ ->
      (* L'identifiant est trouvé dans la tds locale, 
      il a donc déjà été déclaré dans le bloc courant *) 
      raise (DoubleDeclaration n)
    end
  | AstSyntax.AffectationPointeur(affec,e) ->
    let (info_affec,nom) = analyse_tds_affectable tds affec in
    begin
    match info_affec with
    | AstTds.Ident(_)-> 
      let ne = analyse_tds_expression tds e in
      (* Renvoie de la nouvelle affectation où le nom a été remplacé par l'information 
      et l'expression remplacée par l'expression issue de l'analyse *)
      AffectationPointeur (info_affec, ne)
    | AstTds.Dref(_) -> 
      let ne = analyse_tds_expression tds e  in
      (* Renvoie de la nouvelle affectation où le nom a été remplacé par l'information 
      et l'expression remplacée par l'expression issue de l'analyse *)
      AffectationPointeur (info_affec, ne)
    | _ -> raise (MauvaiseUtilisationIdentifiant nom)
    end
  | AstSyntax.Constante (n,v) -> 
    begin
      match chercherLocalement tds n with
      | None -> 
        (* L'identifiant n'est pas trouvé dans la tds locale, 
        il n'a donc pas été déclaré dans le bloc courant *)
        (* Ajout dans la tds de la constante *)
        ajouter tds n (info_to_info_ast (InfoConst (n,v))); 
        (* Suppression du noeud de déclaration des constantes devenu inutile *)
      Empty
      | Some _ ->
        (* L'identifiant est trouvé dans la tds locale, 
        il a donc déjà été déclaré dans le bloc courant *) 
        raise (DoubleDeclaration n)
    end
  | AstSyntax.Affichage e -> 
    (* Vérification de la bonne utilisation des identifiants dans l'expression *)
    (* et obtention de l'expression transformée *)
    let ne = analyse_tds_expression tds e in
    (* Renvoie du nouvel affichage où l'expression remplacée par l'expression issue de l'analyse *)
    Affichage (ne)
  | AstSyntax.Conditionnelle (c,t,e) -> 
    (* Analyse de la condition *)
    let nc = analyse_tds_expression tds c in
    (* Analyse du bloc then *)
    let tast = analyse_tds_bloc tds t in
    (* Analyse du bloc else *)
    let east = analyse_tds_bloc tds e in
    (* Renvoie la nouvelle structure de la conditionnelle *)
    Conditionnelle (nc, tast, east)
  | AstSyntax.TantQue (c,b) -> 
    (* Analyse de la condition *)
    let nc = analyse_tds_expression tds c in
    (* Analyse du bloc *)
    let bast = analyse_tds_bloc tds b in
    (* Renvoie la nouvelle structure de la boucle *)
    TantQue (nc, bast)
  | AstSyntax.Retour (e) -> 
    (* Analyse de l'expression *)
    let ne = analyse_tds_expression tds e in
    Retour (ne)
  | AstSyntax.AssignationAdd (affect,e) -> 
    (* Analyse de l'affectable *)
    let (info_affec,nom) = analyse_tds_affectable tds affect in
    begin
    match info_affec with
    | AstTds.Ident(_)-> 
      let ne = analyse_tds_expression tds e in
      (* Renvoie du nouveau identificateur où le nom a été remplacé par l'information 
      et l'expression remplacée par l'expression issue de l'analyse , on 
      écrit directement l'expression comme une somme*)
      AffectationPointeur (info_affec, Binaire(Plus,AstTds.Affectable(info_affec),ne))
    | AstTds.Dref(_) -> 
      let ne = analyse_tds_expression tds e  in
      (* Renvoie du nouveau pointeur où le nom a été remplacé par l'information 
      et l'expression remplacée par l'expression issue de l'analyse, on 
      écrit directement l'expression comme une somme *)
      AffectationPointeur (info_affec, Binaire(Plus,AstTds.Affectable(info_affec),ne))
    | _ -> 
      raise (MauvaiseUtilisationIdentifiant nom)
    end
  | AstSyntax.DeclarationTypeNomme(nom,typ) -> 
    begin
    match chercherLocalement tds nom with
    | None ->
      (* Création de l'information associée à l'identfiant *)
      let info = InfoVar (nom,typ, 0, "") in
      (* Création du pointeur sur l'information *)
      let ia = info_to_info_ast info in
      (* Ajout de l'information (pointeur) dans la tds *)
      ajouter tds nom ia;
      (* Renvoie de la nouvelle déclaration où le nom a été remplacé par l'information 
      et l'expression remplacée par l'expression issue de l'analyse *)
      AstTds.Empty
    | Some _ ->
      (* L'identifiant est trouvé dans la tds locale, 
      il a donc déjà été déclaré dans le bloc courant *) 
      raise (DoubleDeclaration nom)
    end


      
(* analyse_tds_bloc : AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_tds_bloc tds li =
  (* Entrée dans un nouveau bloc, donc création d'une nouvelle tds locale 
  pointant sur la table du bloc parent *)
  let tdsbloc = creerTDSFille tds in
  (* Analyse des instructions du bloc avec la tds du nouveau bloc 
  Cette tds est modifiée par effet de bord *)
  let nli = List.map (analyse_tds_instruction tdsbloc) li in
  (* afficher_locale tdsbloc ; *) (* décommenter pour afficher la table locale *)
  nli

(* verifier_identificateur : ('a *string) list -> boolean *)
(* Paramètre : la liste des identifiants des parametres *)
(* Vérifie que chaque paramètre a un nom différent *)
(* Erreur si double déclaration des identifiants *)
let rec verifier_identificateur lp =
match lp with
| []  -> true
| (_,nom)::q -> 
  if (List.exists (function (_,nomverif) -> if nom=nomverif then (raise (DoubleDeclaration nom))  else false) q) then false 
  else verifier_identificateur q

(* convertirtypenomme :typ -> typ *)
(* Paramètre : Le type à vérifier que c'est bien un type non TypeNomme*)
(* Transforme un TypeNomme récursivement en son type de base *)
let rec convertirtypenomme tds typee=
  begin
  match typee with
  | Type.TypeNomme(nom) -> 
    begin
    (* On vérifique que le nom du type Nomme a bien été définie*)
    match chercherGlobalement tds nom with
    | Some info -> 
      begin
      match info_ast_to_info info with
      | InfoVar(_,typ,_,_) ->  
        begin
        match typ with 
        (* Dans ce cas, faut refaire l'opération avec le nouveau TypeNomme*)
        | Type.TypeNomme(nom) -> 
          convertirtypenomme tds (Type.TypeNomme(nom))
        (* On a un type qui n'est pas un TypeNomme*)
        | _ -> 
          typ
        end
      | _ -> failwith "erreur interne"
      end
    | None -> raise (IdentifiantNonDeclare nom)
    end
  | _ -> typee
  end

(* analyse_tds_fonction : AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_tds_fonction maintds (AstSyntax.Fonction(t,n,lp,li))  =

  match chercherGlobalement maintds n with
  | None -> 
    (* L'identifiant n'est pas trouvé dans la tds locale, 
    il n'a donc pas été déclaré dans le bloc global *)

    (* Création d'une TDS fille pour y stocker les informations sur les parametres de la fonction*)
    (* Verification que tous les paramètres de la fonction sont bien distincts*)
    let _= verifier_identificateur lp in
    (* On récupére tous les types des paramètres*)
    let types_variables = List.map (fun t -> fst t) lp in
    (* On récupére tous les types effectifs des paramètres,
    en convertissant les potentiels types nommés*)
    let types_convertis = List.map (fun t -> convertirtypenomme maintds t) types_variables in 
    (* On récupérer les noms des variables*)
    let noms_variables = List.map (fun t -> snd t) lp in 
    (* On récupere le type effectif du type de retour*) 
    let t_effectif = convertirtypenomme maintds t in
    (* On ajoute à la tds mère l'infoFun *)
    let _ = ajouter maintds n (info_to_info_ast (InfoFun(n,(t_effectif),types_convertis))) in
    (* On crée une Tds fille*)
    let fille = creerTDSFille maintds in
      
    (* On crée les différents infos associé à nos paramètres*)     
    let infos = List.map2 (fun nom typ -> info_to_info_ast (InfoVar(nom,typ,0,""))) noms_variables types_convertis in
      (* On les rajoute à la Tds fille*) 
    let _ = List.map2 (fun nom info_pointeur -> ajouter fille nom info_pointeur ) noms_variables infos in
    (* On analyse les instructions de la fonction*)
    let nli = analyse_tds_bloc fille li in
    let couple_info = List.map2 (fun typ pointeur -> (typ,pointeur)) types_convertis infos in 
    (* On renvoit la Fonction mise à jour*)
    AstTds.Fonction ((t_effectif),info_to_info_ast (InfoFun(n,(t_effectif),types_convertis)),couple_info,nli)

    | Some _ ->
    (* L'identifiant est trouvé dans la tds locale, 
    il a donc déjà été déclaré dans le bloc courant *) 
    raise (DoubleDeclaration n)

(* analyse_tds_type_nomme : tds * (instuction) type -> [] *)
(* Paramètre : La liste de type nommé à rajouté à la tds *)
(* Rajoute tous les types nommés à la Tds en y ajoutant en plus du nom le type *)
let rec analyse_tds_type_nomme tds types_nomme = 
  begin
  match types_nomme with
  | [] -> []
  | AstSyntax.DeclarationTypeNomme(nom,typ)::q -> 
    begin
    match chercherGlobalement tds nom with
    | None -> 
      let info = InfoVar (nom,typ, 0, "") in
      (* Création du pointeur sur l'information *)
      let ia = info_to_info_ast info in
      (* Ajout de l'information (pointeur) dans la tds *)
      ajouter tds nom ia;
      (analyse_tds_type_nomme tds q)
    | Some _ ->
      (* L'identifiant est trouvé dans la tds locale, 
      il a donc déjà été déclaré dans le bloc courant *) 
      raise (DoubleDeclaration nom)
    end
  | _ -> failwith "internal error"
     
  end
  


let analyser (AstSyntax.Programme (types_nomme,fonctions,prog)) =
  let tds = creerTDSMere () in
  (* On ajoute tous les types nommées globaux à la tds mère*)
  let _ =  analyse_tds_type_nomme tds (List.flatten types_nomme) in
  (* On vérifie les fonctions*)
  let nf = List.map (analyse_tds_fonction tds) fonctions in
  (* On vérifie le main*) 
  let nb = analyse_tds_bloc tds prog in
  (* On met à jour le Programme*)
  AstTds.Programme(nf,nb)
end

