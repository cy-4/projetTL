(* Module de la passe de gestion des types *)

module PasseTypeRat : Passe.Passe with type t1 = Ast.AstTds.programme and type t2 = Ast.AstType.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open Type

  type t1 = Ast.AstTds.programme
  type t2 = Ast.AstType.programme

(* analyse_type_affectable : AstTds.affectable -> AstType.affectable *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre aff : l'affectable à analyser *)
(* Vérifie la qu'on déréfencie bien un pointeur et tranforme l'affectable
en une affectable de type AstTds.affectable *)
(* Erreur si on déréfence un non pointeur *)
let rec analyse_type_affectable aff = 
  begin 
    match aff with
    | AstTds.Dref(affectable)->  let (np,tp) = analyse_type_affectable affectable in
          (
            match tp with
              | Pointeur(typ)-> (AstType.Dref(np),typ)
              | a -> raise (TypeNonPointeur(a))
          )
    | AstTds.Ident(info) -> 
    begin
      match info_ast_to_info info with
            | InfoVar(_,t,_,_) -> (AstType.Ident (info), t)
            | _ -> failwith "Internal error"
    end
    | AstTds.EntierCons(entier) -> (AstType.EntierCons(entier), Type.Int)
    | AstTds.Champ(_) -> failwith "internal error, pas encore fait, ne peut pas rentrer dans ce cas"
  end


(* analyse_type_expression : AstTds.expression -> AstType.expression *)
(* Paramètre aff : l'expression à analyser *)
(* Vérifie qu'il n'y a pas d'erreur de typage dans les opéations des expression
et transforme l'expression en Type_Expression *)
(* Erreur si on effectue une opération non autorisé sur les types fournis *)
let rec analyse_type_expression e = 
   match e with 
    | AstTds.AppelFonction (f,eliste) ->
      begin
      match info_ast_to_info f with
        | InfoFun (_,t,types_requis) ->
          (* On analyse toutes les expressions donne en parametre*)
          let analyse_eliste = List.map (function e -> (analyse_type_expression e)) eliste in
          (* On récupére les nouvelles expressions et leur types*)
          let (el, types_reels) =  List.split analyse_eliste in
          (* On regarde si ces types sont compatible avec les types demandé par la fonction*)
          if (est_compatible_list types_reels types_requis) then
            (AstType.AppelFonction(f, el), t)
          else raise (TypesParametresInattendus (types_requis,types_reels))
        | _ -> failwith "internal error"
      end
    | AstTds.Booleen (b) -> (AstType.Booleen(b), Type.Bool)
    
    | AstTds.Entier (i) -> (AstType.Entier(i), Type.Int)

    | AstTds.Affectable (aff) -> let (newaffec,typ)= analyse_type_affectable aff in
                                  (AstType.Affectable(newaffec),typ)      

    | AstTds.Unaire (u, e1) -> let (e1new,e1type) = analyse_type_expression e1 in
      begin 
      match (u,e1type) with
        | (AstSyntax.Numerateur,Type.Rat) -> (AstType.Unaire(AstType.Numerateur,e1new),Type.Int)
        | (AstSyntax.Denominateur,Type.Rat) -> (AstType.Unaire(AstType.Denominateur, e1new),Type.Int)
        | _ -> raise (TypeInattendu (e1type,Type.Rat))
      end
          
    | AstTds.Binaire (b, e1, e2) -> let (e1new,e1type) = analyse_type_expression e1 in 
                                    let (e2new,e2type) = analyse_type_expression e2 in
      (* Si l'opération n'est pas dans les types proposés ci-dessous, on renvoie une Exception*)
      begin
      match (e1type,b,e2type) with
        | (Type.Int,AstSyntax.Plus,Type.Int) -> (AstType.Binaire(PlusInt,e1new,e2new),Type.Int)
        | (Type.Rat,AstSyntax.Plus,Type.Rat) -> (AstType.Binaire(PlusRat,e1new,e2new),Type.Rat)
        | (Type.Rat,AstSyntax.Mult,Type.Rat) -> (AstType.Binaire(MultRat,e1new,e2new),Type.Rat)
        | (Type.Int,AstSyntax.Mult,Type.Int) -> (AstType.Binaire(MultInt,e1new,e2new),Type.Int)
        | (Type.Int,AstSyntax.Fraction,Type.Int) -> (AstType.Binaire(Fraction,e1new,e2new),Type.Rat)
        | (Type.Int,AstSyntax.Equ,Type.Int) -> (AstType.Binaire(EquInt,e1new,e2new),Type.Bool)
        | (Type.Bool,AstSyntax.Equ,Type.Bool) -> (AstType.Binaire(EquBool,e1new,e2new),Type.Bool)
        | (Type.Int,AstSyntax.Inf,Type.Int) -> (AstType.Binaire(Inf,e1new,e2new),Type.Bool)
        | _ -> raise  (TypeBinaireInattendu (b,e1type,e2type))  
        end    

    | AstTds.Null -> (AstType.Null,Pointeur(Undefined))

    | AstTds.NouveauType(typ) -> (AstType.NouveauType(typ),Pointeur(typ))

    | AstTds.Adresse(info_addr) -> 
    begin
        match info_ast_to_info info_addr with
          | InfoVar (_,t,_,_) -> 
              (AstType.Adresse(info_addr), Pointeur(t)) 
          | _ ->
             failwith "errur interne, cela aurait du etre un InfoVar"
    end
    | AstTds.ListeChamp(_) -> failwith "internal error, pas encore fait, ne peut pas rentrer dans ce cas"
              




(* analyse_type_instruction : AstTds.instruction -> tds -> AstType.instruction *)
(* Paramètre option : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Paramètre main : boolean pour savoir si on est dans le main ou non (retour possible ou pas) *)
(* Vérifie le bon typage des instructions et tranforme l'instruction
en une instruction de type AstType.instruction *)
(* Erreur si mauvais typage *)
let rec analyse_type_instruction option i main=
  match i with
  | AstTds.Declaration (t, info, e) ->
      
      let (ne, nt) = analyse_type_expression e in
          (* On vérifie que le type annoncé et le type réal sont compatible*)
          if (est_compatible t nt) then 
            begin
            match info_ast_to_info info with
              | InfoVar _ ->
                modifier_type_info t info;
                AstType.Declaration(info, ne)
              | _ -> failwith "Internal error, cela devait etre un info var"
            end
          else raise (TypeInattendu(nt, t))
 

  | AstTds.AffectationPointeur (aff,e) ->
      begin
          (* De meme on vérife que les 2 types de par et d'autre de l'égalité sont compatible*)
          let (aff_new,typ_aff) =  analyse_type_affectable aff in
          let (e_new,typ_e) = analyse_type_expression e in
          if (est_compatible typ_aff typ_e) then
            AffectationPointeur (aff_new,e_new)
          else
            raise (TypeInattendu (typ_e,typ_aff))
      end  

  | AstTds.Affichage e -> 
      begin
      (* On résolue la surchage, en créant des affichages différents selon le type*)
      let ne = analyse_type_expression e in
      match snd ne with 
      | Type.Rat -> AffichageRat (fst ne)
      | Type.Bool -> AffichageBool (fst ne)
      | Type.Int -> AffichageInt (fst ne)
      | _ -> failwith "Pas d'affichage pour indefined"
      end
      
  | AstTds.Conditionnelle (c,t,e) -> 
      (* Analyse de la condition *)
      let nc = analyse_type_expression c in
      (* Analyse du bloc then *)
      let tast = analyse_type_bloc option t main in
      (* Analyse du bloc else *)
      let east = analyse_type_bloc option e main in
      if (est_compatible Type.Bool (snd nc)) then
      (* Renvoie la nouvelle structure de la conditionnelle *)
        Conditionnelle ((fst nc), tast, east)
      else
        raise (TypeInattendu((snd nc), Type.Bool))

  | AstTds.TantQue (c,b) -> 
      (* Analyse de la condition *)
      let nc = analyse_type_expression c in
      (* Analyse du bloc *)
      let bast = analyse_type_bloc option b main in
      (* Renvoie la nouvelle structure de la boucle *)
      if (est_compatible Type.Bool (snd nc)) then
        TantQue ((fst nc), bast)
      else 
        raise (TypeInattendu((snd nc),Type.Bool))

  | AstTds.Retour (e) -> 
      begin
      (* Cas où on est dans le main donc pas de retour*)
      if main then raise (RetourDansMain) else
      (* Cas ou on est dans une fonction, option le type de retour attendu*)
      match option with
        | None -> failwith "pas de type retour"
        | Some t ->   
          (* On vérifie que les 2 types sont bien compatible*)
          let ne = analyse_type_expression e in
          if (est_compatible t (snd ne)) then
            Retour (fst ne)
          else 
            raise (TypeInattendu ((snd ne), t))
      end
  | AstTds.Empty -> AstType.Empty

      
(* analyse_type_bloc : AstTds.bloc -> AstType.bloc *)
(* Paramètre opt : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Paramètre main : savoir si on est dans le main ou non *)
(* Applique analyse_type_instruction à tout les instructions *)
and analyse_type_bloc opt li main =
   let nli = List.map (function t -> analyse_type_instruction opt t main) li in
   (* afficher_locale tdsbloc ; *) (* décommenter pour afficher la table locale *)
   nli



(* analyse_type_fonction : AstTds.fonction -> AstType.fonction *)
(* Paramètre : la fonction à analyser *)
(* Vérifie le bon typage dans le code et transforme la fonction en  AstType.fonction  *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyse_type_fonction (AstTds.Fonction(t,info,lp,li))  =
      (* On sépare les types et les infos*)
      let (types_param,infos_param)  = List.split lp in
      (* On met le t dans l'info de la fonctions*)
      modifier_type_fonction_info t types_param info;
      (* On analyse les instructions de la fonction*)
      let nli = analyse_type_bloc (Some t) li false in
      (* On renvoit la nouvelle fonction*)
      AstType.Fonction(info, infos_param, nli)
      
(* analyser : AstTds.Programme -> AstType.Programme *)
(* Paramètre : le programme à analyser *)
(* Vérifie le bon type des instructions dans les fonctions et le main
et renvoie le nouveau AstType.Programme *)
(* Erreur si mauvaise utilisation des identifiants *)
let analyser (AstTds.Programme (fonctions,prog)) =
  (* On analyse les fonctions*)
  let nf = List.map (analyse_type_fonction) fonctions in
  (* On analyse le main*)
  let nb = analyse_type_bloc None prog true in
  (*  On renvoie le nouveau programme*)
  AstType.Programme (nf,nb)
end

