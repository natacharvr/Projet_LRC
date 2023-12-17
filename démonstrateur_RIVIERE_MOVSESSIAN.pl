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

verification_Abox([]).
verification_Abox([(I, C) | L]) :- instanceC(I, C), verification_Abox(L).
verification_Abox([(R, C) | L]) :- instanceR(R, C), verification_Abox(L).

/* Vérification auto référencement */
autoref([]). % On lui fournit la liste des concepts complexes
autoref([ConceptComplex| L]) :- equiv(ConceptComplex, DefConceptComplex), pas_autoref(ConceptComplex, DefConceptComplex), autoref(L).

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

% DEUXIEME PARTIE 

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

% TROISIEME PARTIE
% ALgorithme de résolution basée sur la méthode des tableaux 
% On doit montrer que Abe est insatisfiable
compteur(1).

troisieme_etape(Abi,Abr) :-
	tri_Abox(Abi,Lie,Lpt,Li,Lu,Ls),
	resolution(Lie,Lpt,Li,Lu,Ls,Abr),
	nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').



% Utilitaires fournis 
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