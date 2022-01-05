(* Module de la passe de gestion des types *)

module PasseTypeRat : Passe.Passe with type t1 = Ast.AstTds.programme and type t2 = Ast.AstType.programme =
struct

  open Tds
  open Exceptions
  open Ast
  open Type

  type t1 = Ast.AstTds.programme
  type t2 = Ast.AstType.programme

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
    end


(* analyse_tds_expression : AstTds.expression -> AstType.expression *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre e : l'expression à analyser *)

let rec analyse_type_expression e = 
   match e with 
    | AstTds.AppelFonction (f,eliste) ->
      begin
      match info_ast_to_info f with
        | InfoFun (_,t,types_requis) ->
          let analyse_eliste = List.map (function e -> (analyse_type_expression e)) eliste in
          let (el, types_reels) =  List.split analyse_eliste in
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
              




(* analyse_tds_instruction : AstSyntax.instruction -> tds -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_type_instruction option i main=
  match i with
  | AstTds.Declaration (t, info, e) ->
      
      let (ne, nt) = analyse_type_expression e in

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
          let (aff_new,typ_aff) =  analyse_type_affectable aff in
          let (e_new,typ_e) = analyse_type_expression e in
          if (est_compatible typ_aff typ_e) then
            AffectationPointeur (aff_new,e_new)
          else
            raise (TypeInattendu (typ_e,typ_aff))
      end  

  | AstTds.Affichage e -> 
      begin
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
      if main then raise (RetourDansMain) else
      match option with
        | None -> failwith "pas de type retour"
        | Some t ->   
          let ne = analyse_type_expression e in
          if (est_compatible t (snd ne)) then
            Retour (fst ne)
          else 
            raise (TypeInattendu ((snd ne), t))
      end
  | AstTds.Empty -> AstType.Empty

      
(* analyse_tds_bloc : AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_type_bloc opt li main =
   let nli = List.map (function t -> analyse_type_instruction opt t main) li in
   (* afficher_locale tdsbloc ; *) (* décommenter pour afficher la table locale *)
   nli



(* analyse_tds_fonction : AstSyntax.fonction -> AstTds.fonction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre : la fonction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
  
let analyse_type_fonction (AstTds.Fonction(t,info,lp,li))  =

      
      let (types_param,infos_param)  = List.split lp in
      modifier_type_fonction_info t types_param info;
      let nli = analyse_type_bloc (Some t) li false in
      AstType.Fonction(info, infos_param, nli)
      
(* analyser : AstSyntax.ast -> AstTds.ast *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des identifiants *)

let analyser (AstTds.Programme (fonctions,prog)) =
  let nf = List.map (analyse_type_fonction) fonctions in
  let nb = analyse_type_bloc None prog true in
  AstType.Programme (nf,nb)

end

