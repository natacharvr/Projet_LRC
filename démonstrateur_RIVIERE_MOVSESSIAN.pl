compteur(1).

premiere_etape([], [], []).
premiere_etape(Tbox, Abi, Abr) :- 
	verification_Abox(Abi, Abr),
	verification_Tbox(Tbox),
	autoref(TBox),
	traitement_Abox(),
	traitement_Tbox(TBox, TBox2).
% TODO faire en sorte que le paramètre Tbox soit modifié par traitement_Tbox
/* Vérification syntaxique et sémantique */

concept(ConceptAtom) :- cnamea(ConceptAtom).
concept(ConceptNonAtom) :- cnamena(ConceptNonAtom).

% Vérification de la grammaire de ALC
concept(not(C)) :- concept(C).
concept(and(C1,C2)) :- concept(C1), concept(C2)!.
concept(or(C1,C2)) :- concept(C1), concept(C2)!.
concept(some(R,C)) :- rname(R), concept(C)!.
concept(all(R,C)) :- rname(R), concept(C)!.

% Verification de la TBox
definition(C, C1) :- cnamea(C), concept(C1).
verification_Tbox([(C, C1) | L]) :- 
	definition(C,C1),
	verification_Tbox(L).

% Vérification de la Abox
instanceC(I,C) :- iname(I), concept(C).
instanceR(R,C) :- rname(R), concept(C).

verification_Abox(AboxC, AboxR) :- verification_AboxC(AboxC), verification_AboxR(AboxR).
verification_AboxC([]).
verification_AboxC([(I, C) | L]) :- instanceC(I, C), verification_AboxC(L).
verification_AboxR([]).
verification_AboxR([(R, C) | L]) :- instanceR(R, C), verification_AboxR(L).

/* Vérification auto référencement */
autoref([]). % On lui fournit la Tbox
autoref([(ConceptComplex, _)| L]) :- equiv(ConceptComplex, DefConceptComplex), pas_autoref(ConceptComplex, DefConceptComplex), autoref(L).

pas_autoref(C, C1) :- C \== C1, cnamea(C1).
pas_autoref(C, C1) :- C \== C1, equiv(C1, C2), pas_autoref(C, C2). % Ici on ne précise pas que C1 est un concept non atomique, car on sait qu'il n'est pas atomique (clause précédente)

pas_autoref(C, and(C1, C2)) :- pas_autoref(C, C1), pas_autoref(C, C2).
pas_autoref(C, or(C1, C2)) :- pas_autoref(C,C1), pas_autoref(C, C2).
pas_autoref(C, some(_, C1)) :- pas_autoref(C, C1). 
pas_autoref(C, all(_, C1)) :- pas_autoref(C, C1).
pas_autoref(C, not(C1)) :- pas_autoref(C,C1).

% traitement_Tbox
% developpement_atomique(C,D) est vrai si D est le développement atomique de C
developpement_atomique(C, C) :- 
	cnamea(C).

developpement_atomique(C, C1) :- 
	equiv(C, Def), 
	developpement_atomique(C, Def).

developpement_atomique(not(C1), not(C2)) :- 
	developpement_atomique(C1, C2).

developpement_atomique(and(C1, C2), and(C3, C4)) :- 
	developpement_atomique(C1, C3), 
	developpement_atomique(C2, C4).

developpement_atomique(or(C1, C2), or(C3, C4)) :- 
	developpement_atomique(C1, C3), 
	developpement_atomique(C2, C4).

developpement_atomique(some(R, C1), some(R, C2)) :- 
	developpement_atomique(C1, C2).

developpement_atomique(all(R,C1), all(R,C2)) :- 
	developpement_atomique(C1, C2).

traitement_Tbox([],[]).

traitement_Tbox([(C, DefC) | L1], [(C, DefC1) | L2]) :- 
	concept(DefC), 
	developpement_atomique(DefC, C2), 
	nnf(C2, DefC1), 
	traitement_Tbox(L1, L2).

% traitement_Abox

traitement_Abox([], []).
% TODO traitement_Abox !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!

% Programme du démonstrateur :
% Dans premiere_etape :
% Tbox est la liste représentant la Tbox
% Abi est la liste représentant les assertions de concepts de la Abox
% Abr est la liste représentant les assertions de rôles de la Abox

% J'imagine que premiere_etape doit appliquer à chaque element de la Tbox et de la Abox les prédicats définis plus haut et retourner zéro si l'un ne passe pas 

% Dans deuxieme_etape :
% Abi est la liste représentant les assertions de concepts initiales  de la Abox
% Abi1 est la liste des assertions de concepts complétée après la soumission d’une proposition à démontrer
% Tbox est la liste représentant la Tbox

% Dans troisieme_etape :
% Abi1 est la liste des assertions de concepts complétée
% Abr est la liste des assertions de rôles qui peut également évoluer lors de la démonstration
programme :- premiere_etape(Tbox, Abi, Abr),
	deuxieme_etape(Abi, Abi1, Tbox),
	troisieme_etape(Abi1, Abr).

% ------------------------------------------------------ DEUXIEME PARTIE -------------------------------------------------------- 

% Code fourni
deuxieme_etape(Abi,Abi1,Tbox) :- saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox) :- nl,
	write('Entrez le numero du type de proposition que vous voulez demontrer :'),
	nl,
	write('1 Une instance donnee appartient a un concept donne.'),
	nl,
	write('2 Deux concepts n`ont pas d`elements en commun(ils ont une intersection vide).'),
	nl, 
	read(R), 
	suite(R,Abi,Abi1,Tbox).

suite(1,Abi,Abi1,Tbox) :- acquisition_prop_type1(Abi,Abi1,Tbox),!.
suite(2,Abi,Abi1,Tbox) :- acquisition_prop_type2(Abi,Abi1,Tbox),!.
suite(R,Abi,Abi1,Tbox) :- nl,
	write('Cette reponse est incorrecte.'),
	nl,
	saisie_et_traitement_prop_a_demontrer(Abi,Abi1,Tbox).

% Code demandé
% Proposition de type 1
lecture_prop_1(I, C) :- 
	nl,
	write('Votre proposition doit être de la forme I : C')
	write('Entrez le nom de l`instance I :'),
	nl,
	read(I),
	nl,
	write('Entrez le nom du concept C :'),
	nl,
	read(C),
	verification_lecture(C, I, V).

verification_lecture(C, I, 1):- instanceC(I, C).
verification_lecture(C, I, 0) :- 
	nl,
	write('Votre entree est incorrecte, merci de recommencer.'),
	fail.

acquisition_prop_type1(Abi, [(I, NegDefC) |Abi1], TBox) :- 
	lecture_prop_1(I,C),
	developpement_atomique(not(C), DefC),
	nnf(DefC, NegDefC).

% Proposition de type 2
lecture_prop_2(C1, C2) :- 
	nl,
	write('Votre proposition doit être de la forme C1 ⊓ C2 ⊑ ⊥'),
	nl,
	write('Entrez le nom du premier concept C1 :'),
	nl,
	read(C1),
	nl,
	write('Entrez le nom du deuxième concept C2 :'),
	nl,
	read(C2),
	verification_lecture2(C1, C2, V).

verification_lecture2(C1, C2, 1):- concept(C1), concept(C2).
verification_lecture(C1, C2, 0) :- 
	nl,
	write('Votre entree est incorrecte, merci de recommencer.'),
	fail.

acquisition_prop_type2(Abi, [(Inst, NegDefC) |Abi1], _) :- 
	lecture_prop_2(C1,C2),
	genere(Inst),
	developpement_atomique(C1, DefC1),
	developpement_atomique(C2, DefC2),
	nnf(and(DefC2, DefC1), NegDefC).

% acquisition_prop_type1 réalise l'acquisition d'une proposition de type 1 ( I : C ) puis formate ( I : non C, remplacer récursivement les identificateurs de conccepts complexes par leur définition puis fnn)
% acquisition_prop_type_2 réalise l'acquisition d'une proposition de type 2 ( C1 n C2 = vide ) puis formate ( exists inst, inst : C1 and C2, remplacer récursivement les identificateurs de conccepts complexes par leur définition puis fnn)
% La liste représentant les assertions de concepts est complétée.

% ---------------------------------------------- TROISIEME PARTIE -------------------------------------------------------
% ALgorithme de résolution basée sur la méthode des tableaux 
% On doit montrer que Abe est insatisfiable

troisieme_etape(Abi,Abr) :-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	resolution(Lie,Lpt,Li,Lu,Ls,Abr),
	nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').

tri_Abox([], _, _, _, _, _).
% ---- some -----
tri_Abox([(I, some(R,C)) | Abi], [(I, some(R,C)) | Lie], Lpt, Li, Lu, Ls) :-
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls).
% ---- all ----
tri_Abox([(I, all(R,C)) | Abi], Lie, [(I, all(R,C)) | Lpt], Li, Lu, Ls) :- 
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls).
% ---- and ----
tri_Abox([(I, and(C1, C2)) | Abi], Lie, Lpt, [(I, and(C1, C2)) | Li], Lu, Ls) :- 
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls).
% ---- or ----
tri_Abox([(I, or(C1, C2)) | Abi], Lie, Lpt, Li, [(I, or(C1, C2)) | Lu], Ls) :- 
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls).
% ---- autre ----
tri_Abox([A | Abi], Lie, Lpt, Li, Lu, [A | Ls]) :- 
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls).


resolution([],[],[],[],[],[]).

resolution(Lie,Lpt,Li,Lu,Ls,Abr) :- 
	no_clash(Lie,Lpt,Li,Lu,Ls,Abr),
	complete_some(Lie,Lpt,Li,Lu,Ls,Abr),
	transformation_and(Lie,Lpt,Li,Lu,Ls,Abr),
	deduction_all(Lie,Lpt,Li,Lu,Ls,Abr),
	transformation_or(Lie,Lpt,Li,Lu,Ls,Abr).

no_clash(Lie,Lpt,Li,Lu,Ls,Abr) :- 
	no_clash(Lie),
	no_clash(Lpt),
	no_clash(Li),
	no_clash(Lu),
	no_clash(Ls).

no_clash([]).
no_clash(L) :- 
	\+ clash(L).

clash([]) :- fail.

clash([(I,C) | L]) :- 
	nnf(not(C), C1),
	member((I, C1), L).

clash([_ | L]) :- 
	clash(L).

complete_some([],Lpt,Li,Lu,Ls,Abr).
complete_some([(I, some(R,C)) | Lie],Lpt,Li,Lu,Ls,Abr) :- 
	genere(Nom),
	evolue((Nom, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
	resolution( Lie1, Lpt1, Li1, Lu1, Ls1, [(I, Nom, R) | Abr]).

transformation_and(Lie,Lpt,[],Lu,Ls,Abr).
transformation_and(Lie,Lpt,[(I, and(C1, C2)) | Li], Lu,Ls,Abr) :- 
	evolue((I, C1), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
	evolue((I, C2), Lie1, Lpt1, Li1, Lu1, Ls1, Lie2, Lpt2, Li2, Lu2, Ls2),
	resolution(Lie2, Lpt2, Li2, Lu2, Ls2, Abr).

% TODO je ne suis pas sûre que j'ai le droit de faire ce que je fais, est ce que ça fit bien dans un OU. Si ça fait partie de la liste je boucle, sinon je passe à autre chose 
deduction_all(Lie,[],Li,Lu,Ls,Abr).
deduction_all(Lie,[(I, all(R,C)) | Lpt],Li,Lu,Ls,Abr) :-
	member((I, B, R), Abr),
	evolue((B, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
	enleve((I,B,R), Abr, Abr1),
	deduction_all(Lie1, [(I, all(R,C)) | Lpt1], Li1, Lu1, Ls1, Abr1).

deduction_all(Lie,[(I, all(R,C)) | Lpt],Li,Lu,Ls,Abr) :-
	\+ member((I, B, R), Abr), % Même pas forcément nécéssaire, si on est dans cette branche c'est que le test a échoué dans le précédent
	resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr1).

transformation_or(Lie,Lpt,Li,[],Ls,Abr).
transformation_or(Lie,Lpt,Li,Lu,Ls,Abr) :- 
	evolue((I, C1), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
	evolue((I, C2), Lie, Lpt, Li, Lu, Ls, Lie2, Lpt2, Li2, Lu2, Ls2),
	resolution(Lie2, Lpt2, Li2, Lu2, Ls2, Abr),
	resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr).


% ---- evolue(A, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) ----
% A représente une nouvelle assertion de concepts à intégrer dans l’une des listes Lie, Lpt,
% Li, Lu ou Ls qui décrivent les assertions de concepts de la Abox étendue et Lie1, Lpt1,
% Li1,Lu1 et Ls1 représentent les nouvelles listes mises à jour.

% ---- some ----
evolue((I, some(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :- 
	member((I, some(R,C)), Lie).

% le test d'appartenance n'est pas nécéssaire car si la proposition ne correspond pas au prédicat précédent, c'est qu'il n'est pas dans la liste TODO vérifier
evolue((I, some(R,C)), Lie, Lpt, Li, Lu, Ls, [(I, some(R,C)) | Lie], Lpt, Li, Lu, Ls).

% ---- all ----
evolue((I, all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
	member((I, all(R,C)), Lpt).

evolue((I, all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, [(I, all(R,C)) | Lpt], Li, Lu, Ls).

% ---- and ----
evolue((I, and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :- 
	member((I, and(C1,C2)), Li).

evolue((I, and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, [(I, and(C1, C2)) | Li], Lu, Ls).

% ---- or ----
evolue((I, or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
	member((I, or(C1,C2)), Lu).

evolue((I, or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, [(I, or(C1, C2)) | Lu], Ls).

% ---- autre ----
evolue(A, Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
	member(A, Ls).

evolue(A, Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [A | Ls]).



affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2)



% ------------------------------------------------------- Utilitaires fournis ---------------------------------------------
genere(Nom) :- compteur(V),nombre(V,L1),
	concat([105,110,115,116],L1,L2),
	V1 is V+1,
	dynamic(compteur/1),
	retract(compteur(V)),
	dynamic(compteur/1),
	assert(compteur(V1)),nl,nl,nl,
	name(Nom,L2).
nombre(0,[]).
nombre(X,L1) :-
	R is (X mod 10),
	Q is ((X-R)//10),
	chiffre_car(R,R1),
	char_code(R1,R2),
	nombre(Q,L),
	concat(L,[R2],L1).

chiffre_car(0,'0').
chiffre_car(1,'1').
chiffre_car(2,'2').
chiffre_car(3,'3').
chiffre_car(4,'4').
chiffre_car(5,'5').
chiffre_car(6,'6').
chiffre_car(7,'7').
chiffre_car(8,'8').
chiffre_car(9,'9').

concat([],L1,L1).
concat([X|Y],L1,[X|L2]) :- concat(Y,L1,L2).

enleve(X,[X|L],L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X,L,L2).

% Mise sous forme normale négative
nnf(not(and(C1,C2)),or(NC1,NC2)):- nnf(not(C1),NC1), nnf(not(C2),NC2),!.
nnf(not(or(C1,C2)),and(NC1,NC2)):- nnf(not(C1),NC1),nnf(not(C2),NC2),!.
nnf(not(all(R,C)),some(R,NC)):- nnf(not(C),NC),!.
nnf(not(some(R,C)),all(R,NC)):- nnf(not(C),NC),!.
nnf(not(not(X)),Y):- nnf(X,Y),!.
nnf(not(X),not(X)):-!.
nnf(and(C1,C2),and(NC1,NC2)):- nnf(C1,NC1),nnf(C2,NC2),!.
nnf(or(C1,C2),or(NC1,NC2)):- nnf(C1,NC1), nnf(C2,NC2),!.
nnf(some(R,C),some(R,NC)):- nnf(C,NC),!.
nnf(all(R,C),all(R,NC)) :- nnf(C,NC),!.
nnf(X,X).