(* Module de la passe de gestion des identifiants *)

module PasseTdsRat : Passe.Passe with type t1 = Ast.AstSyntax.programme and type t2 = Ast.AstTds.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open AstTds

  type t1 = Ast.AstSyntax.programme
  type t2 = Ast.AstTds.programme


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
                | InfoVar _ ->   (AstTds.Ident(info),identificateur)
                | InfoConst(_,v) -> 
                  (AstTds.EntierCons(v),identificateur)
                | _ ->
                  raise (MauvaiseUtilisationIdentifiant identificateur)
              end
          end
        | AstSyntax.Dref(affectable)-> let (newaff,id)=analyse_tds_affectable tds affectable in
                  (AstTds.Dref(newaff),id)
        | AstSyntax.Champ(affectable,champ1) ->  let (newaff,id)=analyse_tds_affectable tds affectable in
        (AstTds.Champ(newaff,champ1),id)
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
        | None -> raise (IdentifiantNonDeclare f)
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
    | AstSyntax.ListeChamp(liste) -> let new_list= List.map (analyse_tds_expression tds) liste in
    AstTds.ListeChamp(new_list)
          




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
            match t with 
            | TypeNomme(nom) ->   
              begin
              match chercherGlobalement tds nom with
                | Some info -> 
                    begin
                    match info_ast_to_info info with
                      | InfoVar(_,typ,_,_) -> 
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
                          Declaration (typ, ia, ne) 
                      | _ -> failwith "internal error"
                       end
                | None  -> raise (IdentifiantNonDeclare nom)
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
        | AstTds.Ident(_)-> let ne = analyse_tds_expression tds e in
           (* Renvoie de la nouvelle affectation où le nom a été remplacé par l'information 
            et l'expression remplacée par l'expression issue de l'analyse *)
            AffectationPointeur (info_affec, ne)
        | AstTds.Dref(_) -> let ne = analyse_tds_expression tds e  in
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
        | AstTds.Ident(_)-> let ne = analyse_tds_expression tds e in
           (* Renvoie de la nouvelle affectation où le nom a été remplacé par l'information 
            et l'expression remplacée par l'expression issue de l'analyse *)
            AffectationPointeur (info_affec, Binaire(Plus,AstTds.Affectable(info_affec),ne))
        | AstTds.Dref(_) -> let ne = analyse_tds_expression tds e  in
        (* Renvoie de la nouvelle affectation où le nom a été remplacé par l'information 
         et l'expression remplacée par l'expression issue de l'analyse *)
         AffectationPointeur (info_affec, Binaire(Plus,AstTds.Affectable(info_affec),ne))
        | _ -> raise (MauvaiseUtilisationIdentifiant nom)
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


let rec verifier_identificateur lp =
match lp with
  | []  -> true
  | (_,nom)::q -> if (List.exists (function (_,nomverif) -> if nom=nomverif then (raise (DoubleDeclaration nom))  else false) q) then false else verifier_identificateur q

(* analyse_tds_fonction : AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)

let convertirtypenomme tds typee=
  begin
  match typee with
    | Type.TypeNomme(nom) -> 
      begin
      match chercherGlobalement tds nom with
        | Some info -> 
          begin
          match info_ast_to_info info with
            | InfoVar(_,typ,_,_) -> typ   
            | _ -> failwith "erreur interne"
          end
        | None -> raise (IdentifiantNonDeclare nom)
      end
    | _ -> typee
  end
let analyse_tds_fonction maintds (AstSyntax.Fonction(t,n,lp,li))  =

  match chercherGlobalement maintds n with
    | None -> 
        (* L'identifiant n'est pas trouvé dans la tds locale, 
        il n'a donc pas été déclaré dans le bloc global *)

        (* Création d'une TDS fille pour y stocker les informations sur les parametres de la fonction*)

          (* Verification que tous les paramètres de la fonction sont bien distincts*)
           let _= verifier_identificateur lp in

           let types_variables = List.map (fun t -> fst t) lp in
           let types_convertis = List.map (fun t -> convertirtypenomme maintds t) types_variables in 
           let noms_variables = List.map (fun t -> snd t) lp in    
           let _ = ajouter maintds n (info_to_info_ast (InfoFun(n,(convertirtypenomme maintds t),types_convertis))) in

          let fille = creerTDSFille maintds in
          
              
          let infos = List.map2 (fun nom typ -> info_to_info_ast (InfoVar(nom,typ,0,""))) noms_variables types_convertis in
          let _ = List.map2 (fun nom info_pointeur -> ajouter fille nom info_pointeur ) noms_variables infos in
          let nli = analyse_tds_bloc fille li in
          let couple_info = List.map2 (fun typ pointeur -> (typ,pointeur)) types_convertis infos in 
          AstTds.Fonction ((convertirtypenomme maintds t),info_to_info_ast (InfoFun(n,(convertirtypenomme maintds t),types_convertis)),couple_info,nli)

     | Some _ ->
          (* L'identifiant est trouvé dans la tds locale, 
          il a donc déjà été déclaré dans le bloc courant *) 
          raise (DoubleDeclaration n)


  

let rec analyse_tds_type_nomme tds types_nomme = 
  begin
  match types_nomme with
    | [] -> []
    | AstSyntax.DeclarationTypeNomme(nom,typ)::q -> 
      begin
      match chercherGlobalement tds nom with
        | None -> let info = InfoVar (nom,typ, 0, "") in
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
  let _ =  analyse_tds_type_nomme tds (List.flatten types_nomme) in
  let nf = List.map (analyse_tds_fonction tds) fonctions in 
  let nb = analyse_tds_bloc tds prog in
  AstTds.Programme(nf,nb)
end

