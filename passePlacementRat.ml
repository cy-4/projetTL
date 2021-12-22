(* Module de la passe de gestion des types *)
module PassePlacementRat : Passe.Passe with type t1 = Ast.AstType.programme and type t2 = Ast.AstPlacement.programme =
struct

  open Tds
  open Ast
  open Type

  type t1 = Ast.AstType.programme
  type t2 = Ast.AstPlacement.programme


(* analyse_tds_instruction : AstSyntax.instruction -> tds -> AstTds.instruction *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre i : l'instruction à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme l'instruction
en une instruction de type AstTds.instruction *)
(* Erreur si mauvaise utilisation des identifiants *)
let rec analyse_placement_instruction i base reg =
  match i with
  | AstType.Declaration (info, _) ->
      begin
      match info_ast_to_info info with
        | InfoVar(_,t,_,_) -> let taille = getTaille t in 
                             modifier_adresse_info base reg info;
                             taille
        | _ -> failwith "Internal Error"
      end

  | AstType.Conditionnelle (_,t,e) -> 
    let _ = analyse_placement_bloc t base reg in
    let _ = analyse_placement_bloc e base reg in
    0

  | AstType.TantQue (_,b) -> 
      let _ = analyse_placement_bloc b base reg in
      0

   | _ -> 0
 

      
(* analyse_tds_bloc : AstSyntax.bloc -> AstTds.bloc *)
(* Paramètre tds : la table des symboles courante *)
(* Paramètre li : liste d'instructions à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le bloc
en un bloc de type AstTds.bloc *)
(* Erreur si mauvaise utilisation des identifiants *)
and analyse_placement_bloc li base reg =
   begin
   match li with
        | [] -> base

        | t::q -> let taille = analyse_placement_instruction t base reg in
                                analyse_placement_bloc q (base+taille) reg
    end



(* analyse_tds_fonctiobaseilisation des identifiants et tranforme la fonction
en une fonction de type AstTds.fonction *)
(* Erreur si mauvaise utilisation des identifiants *)
  
let analyse_placement_fonction _  (AstType.Fonction(info,lp,li)) =
    
    let _ = List.fold_right (
      fun pointeur reg ->
        match info_ast_to_info pointeur with
          | InfoVar(_,t,_,_) -> let taille= getTaille t in  
                                let _ =modifier_adresse_info (reg-taille) "LB" pointeur in 
                                reg-taille
          | _ -> failwith "Interne error"
    )
     lp 0 in
     let _ = analyse_placement_bloc li 3 "LB" in
     (AstPlacement.Fonction(info,lp,li)
    )
                                            
(* analyser : AstSyntax.ast -> AstTds.ast *)
(* Paramètre : le programme à analyser *)
(* Vérifie la bonne utilisation des identifiants et tranforme le programme
en un programme de type AstTds.ast *)
(* Erreur si mauvaise utilisation des identifiants *)

let analyser (AstType.Programme (fonctions,prog)) =
  let nf = List.map (analyse_placement_fonction 0) fonctions in
  let _ = analyse_placement_bloc prog 0 "SB" in
  AstPlacement.Programme(nf,prog)

end
