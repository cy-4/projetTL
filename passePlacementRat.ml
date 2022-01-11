(* Module de la passe de gestion des types *)

module PassePlacementRat : Passe.Passe with type t1 = Ast.AstType.programme and type t2 = Ast.AstPlacement.programme =
struct

  open Tds
  open Ast
  open Type

  type t1 = Ast.AstType.programme
  type t2 = Ast.AstPlacement.programme


(* analyse_placement_instruction : AstType.instruction  *)
(* Paramètre i : l'instruction à analyser *)
(* Paramètre base : à combien de registre l'instruction se trouve *)
(* Paramètre reg : savoir si c'est SB ou LB *)
(* Met dans les infos des variables leur placement mémoire et renvoie la taille que prend l'instruction *)
let rec analyse_placement_instruction i base reg =
  match i with
  | AstType.Declaration (info, _) ->
      begin
      match info_ast_to_info info with
        | InfoVar(_,t,_,_) -> let taille = getTaille t in 
                             (* On rajoute l'information du placement mémoire dans la variable*)
                             modifier_adresse_info base reg info;
                             taille
        | _ -> failwith "Internal Error"
      end

  | AstType.Conditionnelle (_,t,e) -> 
    (*On rajoute l'information du placement mémoire au variable des 2 blocs*)
    let _ = analyse_placement_bloc t base reg in
    let _ = analyse_placement_bloc e base reg in
    (* A la fin de la Conditionnelle, on a pas augmenté le registre courant*)
    0

  | AstType.TantQue (_,b) -> 
      (* On rajoute l'information du placement mémoire au variable du bloc*)
      let _ = analyse_placement_bloc b base reg in
      (* A la fin du while, on a pas augmenté le registre courant*)
      0
   | _ -> 0
 

      
(* analyse_placement_bloc : AstTds.bloc *)
(* Paramètre base : à combien de registre l'instruction se trouve *)
(* Paramètre reg : savoir si c'est SB ou LB *)
(* Paramètre li : liste d'instructions à analyser *)
(* On rajoute le placement mémoire à chaque instruction du bloc *)
and analyse_placement_bloc li base reg =
   begin
   match li with
        | [] -> base
        (* On rajoute l'information du placement mémoire à l'instrution,
        Puis on fait appel à nouveaux à la fonction suivate avec la base m-a-j*)
        | t::q -> let taille = analyse_placement_instruction t base reg in
                                analyse_placement_bloc q (base+taille) reg
    end



(* analyse_placement_fonction : AstTds.fonction *)
(* Paramètre fonction : fonction dont qu'on modifie *)
(* On rajoute le placement mémoire à chaque paramètre de la fonction et aux instructions de la fonction *) 
let analyse_placement_fonction _  (AstType.Fonction(info,lp,li)) =
    (* On rajoute l'information du placement mémoire aux arguments de la fonction*)
    let _ = List.fold_right (
      fun pointeur reg ->
        match info_ast_to_info pointeur with
          | InfoVar(_,t,_,_) -> let taille= getTaille t in  
                                let _ =modifier_adresse_info (reg-taille) "LB" pointeur in 
                                reg-taille
          | _ -> failwith "Interne error"
    )
     lp 0 in
     (*  On rajoute l'information du placement mémoire aux instructions de la fonctions*)
     let _ = analyse_placement_bloc li 3 "LB" in
     (AstPlacement.Fonction(info,lp,li)
    )
                                            

(* analyser : AstType.ast -> AstType.ast *)
(* Paramètre : le programme à analyser *)
(* Ajoute l'information du placement mémoire à chaque vériable du programme *)
let analyser (AstType.Programme (fonctions,prog)) =
  (* On joute l'information du placement mémoire aux fonctions*)
  let nf = List.map (analyse_placement_fonction 0) fonctions in
  (* On joute l'information du placement mémoire au main*)
  let _ = analyse_placement_bloc prog 0 "SB" in
  AstPlacement.Programme(nf,prog)

end

