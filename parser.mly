/* Imports. */

%{

open Type
open Ast.AstSyntax
%}


%token <int> ENTIER
%token <string> ID
%token <string> TID
%token RETURN
%token PV
%token AO
%token AF
%token PF
%token PO
%token EQUAL
%token CONST
%token PRINT
%token IF
%token ELSE
%token WHILE
%token BOOL
%token INT
%token RAT
%token CALL 
%token CO
%token CF
%token SLASH
%token NUM
%token DENOM
%token TRUE
%token FALSE
%token PLUS
%token MULT
%token INF
%token EOF
%token NULL
%token NEW
%token AND
%token TYPEDEF
%token STRUCT
%token POINT


(* Type de l'attribut synthétisé des non-terminaux *)
%type <programme> prog
%type <instruction list> bloc
%type <fonction> fonc
%type <instruction list> is
%type <instruction> i
%type <affectable> a
%type <typ> typ
%type <(typ*string) list> dp
%type <expression> e 
%type <expression list> cp

(* Type et définition de l'axiome *)
%start <Ast.AstSyntax.programme> main

%%

main : lfi = prog EOF     {lfi}

prog :
| typenomme=td lf = fonc  lfi = prog   {let (Programme (ft,f1,li))=lfi in (Programme (typenomme::ft,lf::f1,li))}
| ID li = bloc            {Programme ([],[],li)}

td : 
|                         {[]}
| TYPEDEF a=TID EQUAL t=typ PV tdbase=td {DeclarationTypeNomme(a,t)::tdbase}

fonc : t=typ n=ID PO p=dp PF AO li=is AF {Fonction(t,n,p,li)}

bloc : AO li = is AF      {li}

is :
|                         {[]}
| i1=i li=is              {i1::li}

i :
| t=typ n=ID EQUAL e1=e PV          {Declaration (t,n,e1)}
| affec=a EQUAL e1=e PV             {AffectationPointeur(affec,e1)}
| affec=a PLUS EQUAL e1=e PV        {AssignationAdd (affec,e1)}
| CONST n=ID EQUAL e=ENTIER PV      {Constante (n,e)}
| PRINT e1=e PV                     {Affichage (e1)}
| IF exp=e li1=bloc ELSE li2=bloc   {Conditionnelle (exp,li1,li2)}
| WHILE exp=e li=bloc               {TantQue (exp,li)}
| RETURN exp=e PV                   {Retour (exp)}
| TYPEDEF a=TID EQUAL t=typ PV      {DeclarationTypeNomme(a,t)}

a : | n=ID      {Ident(n)}
    | PO MULT ap=a PF {Dref(ap)}
    | PO a1=a POINT n=ID PF   {Champ(a1,n)}

dp :
|                         {[]}
| t=typ n=ID lp=dp        {(t,n)::lp}

typ :
| BOOL    {Bool}
| INT     {Int}
| RAT     {Rat}
| typee=typ MULT {Pointeur(typee)}
| nom=TID {TypeNomme(nom)}
| STRUCT AO dp1=dp AF  {Enregistrement(dp1)}

e : 
| CALL n=ID PO lp=cp PF   {AppelFonction (n,lp)}
| CO e1=e SLASH e2=e CF   {Binaire(Fraction,e1,e2)}
| TRUE                    {Booleen true}
| FALSE                   {Booleen false}
| e=ENTIER                {Entier e}
| NUM e1=e                {Unaire(Numerateur,e1)}
| DENOM e1=e              {Unaire(Denominateur,e1)}
| PO e1=e PLUS e2=e PF    {Binaire (Plus,e1,e2)}
| PO e1=e MULT e2=e PF    {Binaire (Mult,e1,e2)}
| PO e1=e EQUAL e2=e PF   {Binaire (Equ,e1,e2)}
| PO e1=e INF e2=e PF     {Binaire (Inf,e1,e2)}
| PO exp=e PF             {exp}
| affe=a                  {Affectable(affe)}
| NULL                    {Null}
| PO NEW typee=typ PF     {NouveauType(typee)}
| AND n=ID                {Adresse(n)}
| AO cp1=cp AF            {ListeChamp(cp1)}


cp :
|               {[]}
| e1=e le=cp    {e1::le}

