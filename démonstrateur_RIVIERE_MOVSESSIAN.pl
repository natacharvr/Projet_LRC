compteur(1).

premiere_etape(Tbox, Abi, Abr) :- 
	% récupération de la Tbox initiale
	setof((I1, I2), equiv(I1,I2), TboxI),
	% récupération de la Abox de concept initiale
	setof((I3, I4), inst(I3, I4), AbiI),
	% récupération de la Abox de rôles initiale
	setof((I5, I6, R1), instR(I5, I6, R1), Abr),

	verification_Abox(AbiI, Abr),
	verification_Tbox(TboxI),
	autoref(TboxI),
	traitement_Tbox(TboxI, Tbox),
	traitement_Abox(AbiI, Abi), !.

/* Vérification syntaxique et sémantique */

concept(ConceptAtom) :- cnamea(ConceptAtom), !.
concept(ConceptNonAtom) :- cnamena(ConceptNonAtom), !.

% Vérification de la grammaire de ALC
% Remarque : on ne peux pas utiliser ?- concept(X). pour énumérer tous les cas car il y en a une infinité, d'où les ! pour arrêter le traitement 
concept(not(C)) :- concept(C),!.
concept(and(C1,C2)) :- concept(C1), concept(C2),!.
concept(or(C1,C2)) :- concept(C1), concept(C2),!.
concept(some(R,C)) :- rname(R), concept(C),!.
concept(all(R,C)) :- rname(R), concept(C),!.

% Verification de la Tbox
definition(C, C1) :- cnamea(C), concept(C1).
definition(C, C1) :- cnamena(C), concept(C1),!.
verification_Tbox([]).
verification_Tbox([(C, C1) | L]) :- 
	definition(C,C1),
	verification_Tbox(L).

% Vérification de la Abox
instanceC(I,C) :- iname(I), concept(C),!.
instanceR(C1, C2, R) :- iname(C1), iname(C2),rname(R),!.

verification_Abox(AboxC, AboxR) :- verification_AboxC(AboxC), verification_AboxR(AboxR).
verification_AboxC([]).
verification_AboxC([(I, C) | L]) :- instanceC(I, C), verification_AboxC(L).
verification_AboxR([]).
verification_AboxR([(C1, C2, R) | L]) :- instanceR(C1, C2, R), verification_AboxR(L).

/* Vérification auto référencement */
% autoref renvoie true s'il n'y a pas de définition auto-référente
autoref([]). % On lui fournit la Tbox
autoref([(ConceptComplex, DefConceptComplex)| L]) :- pas_autoref(ConceptComplex, DefConceptComplex), autoref(L).

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
	cnamea(C), !.

developpement_atomique(C, C1) :- 
	equiv(C, Def), 
	developpement_atomique(Def, C1).

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
% Exactement le même traitement que pour la Tbox, fait plus de calcul que si on récupérait dans la Tbox simplifiée mais est autonome
traitement_Abox([(C, DefC) | L1], [(C, DefC1) | L2]) :- 
	concept(DefC), 
	developpement_atomique(DefC, C2), 
	nnf(C2, DefC1), 
	traitement_Abox(L1, L2).
% Programme du démonstrateur :
% Dans premiere_etape :
% Tbox est la liste représentant la Tbox
% Abi est la liste représentant les assertions de concepts de la Abox
% Abr est la liste représentant les assertions de rôles de la Abox

% Dans deuxieme_etape :
% Abi est la liste représentant les assertions de concepts initiales  de la Abox
% Abi1 est la liste des assertions de concepts complétée après la soumission d’une proposition à démontrer
% Tbox est la liste représentant la Tbox

% Dans troisieme_etape :
% Abi1 est la liste des assertions de concepts complétée
% Abr est la liste des assertions de rôles qui peut également évoluer lors de la démonstration
programme :- premiere_etape(Tbox, Abi, Abr),
	write('\t Tbox : '),
	affiche_liste(Tbox), nl,
	write('\t Abr : '),
	affiche_liste(Abr), nl,
	write('\t Abi : '),
	affiche_liste(Abi), nl,
	deuxieme_etape(Abi, Abi1, Tbox),
	% write('\t Abi1 : '),
	% affiche_liste(Abi1), nl,
	troisieme_etape(Abi1, Abr).

% ------------------------------------------------------ DEUXIEME PARTIE -------------------------------------------------------- 

% -------------------- Code fourni --------------------
deuxieme_etape(Abi, Abi1,Tbox) :- saisie_et_traitement_prop_a_demontrer(Abi, Abi1,Tbox).

saisie_et_traitement_prop_a_demontrer(Abi, Abi1,Tbox) :- nl,
	write('Entrez le numero du type de proposition que vous voulez demontrer :'),
	nl,
	write('1 Une instance donnee appartient a un concept donne.'),
	nl,
	write('2 Deux concepts n`ont pas d`elements en commun(ils ont une intersection vide).'),
	nl, 
	read(R), 
	suite(R, Abi, Abi1,Tbox).

suite(1, Abi, Abi1,Tbox) :- acquisition_prop_type1(Abi, Abi1,Tbox),!.
suite(2, Abi, Abi1,Tbox) :- acquisition_prop_type2(Abi, Abi1,Tbox),!.
suite(_, Abi, Abi1,Tbox) :- nl,
	write('Cette reponse est incorrecte.'),
	nl,
	saisie_et_traitement_prop_a_demontrer(Abi, Abi1,Tbox).

% -------------------- Code demandé --------------------
% Proposition de type 1
lecture_prop_1(I, C) :- 
	nl,
	write('Votre proposition doit etre de la forme I : C'),
	nl,
	write('Entrez le nom de l`instance I :'),
	nl,
	read(I),
	nl,
	write('Entrez le nom du concept C :'),
	nl,
	read(C),
	verification_lecture(C, I).

verification_lecture(C, I):- instanceC(I, C).
verification_lecture(_, _) :- 
	nl,
	write('Votre entree est incorrecte, merci de recommencer.'),
	fail, !.

acquisition_prop_type1(Abi, [(I, NegDefC) |Abi], _) :- 
	lecture_prop_1(I,C),
	developpement_atomique(not(C), DefC),
	nnf(DefC, NegDefC).

% Proposition de type 2
lecture_prop_2(C1, C2) :- 
	nl,
	write('Votre proposition doit etre de la forme C1 ⊓ C2 ⊑ ⊥'),
	nl,
	write('Entrez le nom du premier concept C1 :'),
	nl,
	read(C1),
	nl,
	write('Entrez le nom du deuxieme concept C2 :'),
	nl,
	read(C2),
	verification_lecture2(C1, C2).

verification_lecture2(C1, C2):- concept(C1), concept(C2).
verification_lecture2(_, _) :- 
	nl,
	write('Votre entree est incorrecte, merci de recommencer.'),
	fail.

acquisition_prop_type2(Abi, [(Inst, NegDefC) |Abi], _) :- 
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

troisieme_etape(Abi, Abr) :-
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls),
	affiche_etat_initial_Abox(Ls, Lie, Lpt, Li, Lu, Abr),
	resolution(Lie, Lpt, Li, Lu, Ls, Abr),
	nl,write('Youpiiiiii, on a demontre la proposition initiale !!!').

tri_Abox([], _, _, _, _, _).
% ---- some -----
tri_Abox([(I, some(R,C)) | Abi], [(I, some(R,C)) | Lie], Lpt, Li, Lu, Ls) :-
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls), !.
% ---- all ----
tri_Abox([(I, all(R,C)) | Abi], Lie, [(I, all(R,C)) | Lpt], Li, Lu, Ls) :- 
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls), !.
% ---- and ----
tri_Abox([(I, and(C1, C2)) | Abi], Lie, Lpt, [(I, and(C1, C2)) | Li], Lu, Ls) :- 
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls), !.
% ---- or ----
tri_Abox([(I, or(C1, C2)) | Abi], Lie, Lpt, Li, [(I, or(C1, C2)) | Lu], Ls) :- 
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls), !.
% ---- autre ----
tri_Abox([A | Abi], Lie, Lpt, Li, Lu, [A | Ls]) :- 
	tri_Abox(Abi, Lie, Lpt, Li, Lu, Ls), !.

% Donnée de test de tri_Abox
% [(a, all(r,c)), (a, and(c, c)), (a, c), (a, or(c,c)), (a, some(r,c))]

resolution(_,_,_,_,Ls,_) :- clash(Ls).

resolution([],[],[],[], Ls,_) :- nl,
	write('--------- Vérification finale de cette branche ---------'), nl,
	no_clash(Ls), fail, !.

resolution([], [], [], Lu, Ls, Abr) :- nl,
	Lu \== [],
	no_clash(Ls),
	write('--------- Application de la règle ⊔ ---------'), nl,
	transformation_or([], [], [], Lu, Ls, Abr), !.

resolution([], Lpt, [], Lu, Ls, Abr) :- nl,
	Lpt \== [],
	no_clash(Ls),
	write('--------- Application de la règle ∀ ---------'), nl,
	deduction_all([], Lpt,[], Lu, Ls, Abr), !.

resolution([], Lpt, Li, Lu, Ls, Abr) :- nl,
	Li\== [],
	no_clash(Ls),
	write('--------- Application de la règle ⊓ ---------'), nl,
	transformation_and([], Lpt, Li, Lu, Ls, Abr), !.

resolution(Lie, Lpt, Li, Lu, Ls, Abr) :- nl,
	Lie \== [],
	no_clash(Ls),
	write('--------- Application de la règle ∃ ---------'), nl,
	complete_some(Lie, Lpt, Li, Lu, Ls, Abr), !.

% Pour mieux comprendre l'ordre des cas de resolution, voir l'exemple suivant
% test([], C) :- write(2), !.
% test(L, C) :- write(1).

% test de no_clash
% no_clash([(a,b),(a,not(b))]).
% ?- no_clash([(a,and(b,c)), (a,or(not(b), not(c)))]).

% renvoie false s'il y a un clash
no_clash(L) :- 
	\+ clash(L).

clash([]) :- fail.

% renvoie true quand il y a un clash
clash([(I,C) | L]) :- 
	nnf(not(C), C1),
	member((I, C1), L), 
	write('Il y a le clash suivant : '), nl,
	affiche_instance((I,C)),nl,
	affiche_instance((I,C1)),nl,
	!.

% comme on n'est pas dans le premier cas, pas de clash, on étudie la  suite de la liste
clash([_ | L]) :- 
	clash(L).

% ------------- some -------------
% complete_some(Lie, Lpt, Li, Lu, Ls, Abr).
complete_some([(I, some(R,C)) | Lie], Lpt, Li, Lu, Ls, Abr) :-
	write('Instance étudiée : '),
	affiche_instance((I, some(R,C))),nl,nl,

	genere(Nom), !,
	evolue((Nom, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
	affiche_evolution_Abox(Ls, [(I, some(R,C)) | Lie], Lpt, Li, Lu , Abr, Ls1, Lie1, Lpt1, Li1, Lu1, [(I, Nom, R) | Abr]),
	resolution( Lie1, Lpt1, Li1, Lu1, Ls1, [(I, Nom, R) | Abr]).


% ------------- and -------------
%transformation_and(Lie, Lpt, Li, Lu, Ls, Abr).
transformation_and(Lie, Lpt,[(I, and(C1, C2)) | Li], Lu, Ls, Abr) :- 
	write('Instance étudiée : '),
	affiche_instance((I, and(C1, C2))),nl,nl,
	
	evolue((I, C1), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
	evolue((I, C2), Lie1, Lpt1, Li1, Lu1, Ls1, Lie2, Lpt2, Li2, Lu2, Ls2),
	affiche_evolution_Abox(Ls, Lie, Lpt, [(I, and(C1, C2)) | Li], Lu , Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
	resolution(Lie2, Lpt2, Li2, Lu2, Ls2, Abr).

% ------------- all -------------
% deduction_all(Lie, Lpt, Li, Lu, Ls, Abr).
deduction_all(Lie,[(I, all(R,C)) | Lpt], Li, Lu, Ls, Abr) :-
	member((I, B, R), Abr),
	write('Instance étudiée : '),
	affiche_instance((I, all(R,C)) ),nl,nl,
	evolue((B, C), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
	enleve((I,B,R), Abr, Abr1),
	affiche_evolution_Abox(Ls, Lie, [(I, all(R,C)) | Lpt], Li, Lu , Abr, Ls1, Lie1, [(I, all(R,C)) | Lpt1], Li1, Lu1, Abr1),
	deduction_all(Lie1, [(I, all(R,C)) | Lpt1], Li1, Lu1, Ls1, Abr1).

deduction_all(Lie,[(I, all(R,C)) | Lpt], Li, Lu, Ls, Abr) :-
	write('Instance étudiée : '),
	affiche_instance((I, all(R,C)) ),nl,nl,
	\+ member((I, _, R), Abr),
	affiche_evolution_Abox(Ls, Lie, [(I, all(R,C)) | Lpt], Li, Lu , Abr, Ls, Lie, Lpt, Li, Lu, Abr),
	resolution(Lie, Lpt, Li, Lu, Ls, Abr).


% ------------- or -------------
% transformation_or(Lie, Lpt, Li, Lu, Ls, Abr).
transformation_or(Lie, Lpt, Li,[(I, or(C1, C2)) | Lu], Ls, Abr) :- 
	write('Instance étudiée : '),
	affiche_instance((I, or(C1, C2))),nl,nl,

	evolue((I, C1), Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1),
	evolue((I, C2), Lie, Lpt, Li, Lu, Ls, Lie2, Lpt2, Li2, Lu2, Ls2),
	write('--------------------- Cas 1 : ---------------------'), nl,

	affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I, or(C1, C2)) | Lu] , Abr, Ls1, Lie1, Lpt1, Li1, Lu1, Abr),
	resolution(Lie1, Lpt1, Li1, Lu1, Ls1, Abr),

	write('--------------------- Cas 2 : ---------------------'), nl,
	affiche_evolution_Abox(Ls, Lie, Lpt, Li, [(I, or(C1, C2)) | Lu] , Abr, Ls2, Lie2, Lpt2, Li2, Lu2, Abr),
	resolution(Lie2, Lpt2, Li2, Lu2, Ls2, Abr).


% ---- evolue(A, Lie, Lpt, Li, Lu, Ls, Lie1, Lpt1, Li1, Lu1, Ls1) ----
% A représente une nouvelle assertion de concepts à intégrer dans l’une des listes Lie, Lpt,
% Li, Lu ou Ls qui décrivent les assertions de concepts de la Abox étendue et Lie1, Lpt1,
% Li1, Lu1 et Ls1 représentent les nouvelles listes mises à jour.

% ---- some ----
evolue((I, some(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :- 
	member((I, some(R,C)), Lie),!.

% le test d'appartenance n'est pas nécéssaire car si la proposition ne correspond pas au prédicat précédent, c'est qu'il n'est pas dans la liste
evolue((I, some(R,C)), Lie, Lpt, Li, Lu, Ls, [(I, some(R,C)) | Lie], Lpt, Li, Lu, Ls) :- !.

% ---- all ----
evolue((I, all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
	member((I, all(R,C)), Lpt), !.

evolue((I, all(R,C)), Lie, Lpt, Li, Lu, Ls, Lie, [(I, all(R,C)) | Lpt], Li, Lu, Ls) :- !.

% ---- and ----
evolue((I, and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :- 
	member((I, and(C1,C2)), Li), !.

evolue((I, and(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, [(I, and(C1, C2)) | Li], Lu, Ls) :- !.

% ---- or ----
evolue((I, or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
	member((I, or(C1,C2)), Lu), !.

evolue((I, or(C1,C2)), Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, [(I, or(C1, C2)) | Lu], Ls) :- !.

% ---- autre ----
evolue(A, Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, Ls) :-
	member(A, Ls), !.

evolue(A, Lie, Lpt, Li, Lu, Ls, Lie, Lpt, Li, Lu, [A | Ls]) :- !.


% --------------------------------------- Affichage ---------------------------------------
affiche_predicat(or(C1, C2)) :- 
	affiche_predicat(C1),
	write(' ⊔ '), 
	affiche_predicat(C2).

affiche_predicat(and(C1, C2)) :-
	affiche_predicat(C1),
	write(' ⊓ '),
	affiche_predicat(C2).

affiche_predicat(some(R, C)) :-
	write(' ∃'),
	write(R),
	write('.'),
	affiche_predicat(C).

affiche_predicat(all(R, C)) :- 
	write(' ∀'),
	write(R),
	write('.'),
	affiche_predicat(C).

affiche_predicat(not(C)) :-
	write('¬'),
	affiche_predicat(C).

affiche_predicat(C) :-
	write(C).

affiche_instance((A, B, R)) :-
	write('('),
	write('<'),
	write(A),
	write(', '),
	write(B),
	write('> :'),
	write(R),
	write(')').

affiche_instance((I, C)) :-
	write('('),
	write(I),
	write(' : '), 
	affiche_predicat(C).

affiche_suivant([]).

affiche_suivant([A | L]) :-
	write(', '),
	affiche_instance(A),
	affiche_suivant(L).

affiche_liste([]) :-
	write('[]'), !.

affiche_liste([A | L]) :- 
	write('['),
	affiche_instance(A),
	affiche_suivant(L),
	write(']'), !.

affiche_evolution_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
	write('Etape précédente : '), nl,
	write('\tLs : '), affiche_liste(Ls1), nl,
	write('\tLie : '), affiche_liste(Lie1), nl,
	write('\tLpt : '), affiche_liste(Lpt1), nl,
	write('\tLi : '), affiche_liste(Li1), nl,
	write('\tLu : '), affiche_liste(Lu1), nl,
	write('\tAbr : '), affiche_liste(Abr1), nl,
	nl,nl,
	write('Nouvelle étape : '), nl,
	write('\tLs : '), affiche_liste(Ls2), nl,
	write('\tLie : '), affiche_liste(Lie2), nl,
	write('\tLpt : '), affiche_liste(Lpt2), nl,
	write('\tLi : '), affiche_liste(Li2), nl,
	write('\tLu : '), affiche_liste(Lu2), nl,
	write('\tAbr : '), affiche_liste(Abr2), nl.

affiche_etat_initial_Abox(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1) :-
	write('Etat initial : '), nl,
	write('\tLs : '), affiche_liste(Ls1), nl,
	write('\tLie : '), affiche_liste(Lie1), nl,
	write('\tLpt : '), affiche_liste(Lpt1), nl,
	write('\tLi : '), affiche_liste(Li1), nl,
	write('\tLu : '), affiche_liste(Lu1), nl,
	write('\tAbr : '), affiche_liste(Abr1), nl,
	nl.

% Cette version existe au cas où les caractères spéciaux ne s'affichent pas correctement

affiche_predicat_special(or(C1, C2)) :- 
	affiche_predicat_special(C1),
	write(' or '), 
	affiche_predicat_special(C2), !.

affiche_predicat_special(and(C1, C2)) :-
	affiche_predicat_special(C1),
	write(' and '),
	affiche_predicat_special(C2), !.

affiche_predicat_special(some(R, C)) :-
	write(' some '),
	write(R),
	write('.'),
	affiche_predicat_special(C), !.

affiche_predicat_special(all(R, C)) :- 
	write(' all '),
	write(R),
	write('.'),
	affiche_predicat_special(C), !.

affiche_predicat_special(not(C)) :-
	write('not '),
	affiche_predicat_special(C), !.

affiche_predicat_special(C) :-
	write(C), !.

affiche_instance_special((A, B, R)) :-
	write('('),
	write('<'),
	write(A),
	write(', '),
	write(B),
	write('> :'),
	write(R),
	write(')').

affiche_instance_special((I, C)) :-
	write('('),
	write(I),
	write(' : '), 
	affiche_predicat_special(C),
	write(')').

affiche_suivant_special([]).

affiche_suivant_special([A | L]) :-
	write(', '),
	affiche_instance_special(A),
	affiche_suivant_special(L).

affiche_liste_special([]) :-
	write('[]'), !.

affiche_liste_special([A | L]) :- 
	write('['),
	affiche_instance_special(A),
	affiche_suivant_special(L),
	write(']'), !.

affiche_evolution_Abox_special(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1, Ls2, Lie2, Lpt2, Li2, Lu2, Abr2) :-
	write('Etape precedente : '), nl,
	write('\tLs : '), affiche_liste_special(Ls1), nl,
	write('\tLie : '), affiche_liste_special(Lie1), nl,
	write('\tLpt : '), affiche_liste_special(Lpt1), nl,
	write('\tLi : '), affiche_liste_special(Li1), nl,
	write('\tLu : '), affiche_liste_special(Lu1), nl,
	write('\tAbr : '), affiche_liste_special(Abr1), nl,
	nl,nl,
	write('Nouvelle etape : '), nl,
	write('\tLs : '), affiche_liste_special(Ls2), nl,
	write('\tLie : '), affiche_liste_special(Lie2), nl,
	write('\tLpt : '), affiche_liste_special(Lpt2), nl,
	write('\tLi : '), affiche_liste_special(Li2), nl,
	write('\tLu : '), affiche_liste_special(Lu2), nl,
	write('\tAbr : '), affiche_liste_special(Abr2), nl.

affiche_etat_initial_Abox_special(Ls1, Lie1, Lpt1, Li1, Lu1, Abr1) :-
	write('Etat initial : '), nl,
	write('\tLs : '), affiche_liste_special(Ls1), nl,
	write('\tLie : '), affiche_liste_special(Lie1), nl,
	write('\tLpt : '), affiche_liste_special(Lpt1), nl,
	write('\tLi : '), affiche_liste_special(Li1), nl,
	write('\tLu : '), affiche_liste_special(Lu1), nl,
	write('\tAbr : '), affiche_liste_special(Abr1), nl,
	nl.
% ------------------------------------------------------- Utilitaires fournis ---------------------------------------------
genere(Nom) :- compteur(V),nombre(V, L1),
	concat([105,110,115,116], L1, L2),
	V1 is V+1,
	dynamic(compteur/1),
	retract(compteur(V)),
	dynamic(compteur/1),
	assert(compteur(V1)),nl,nl,nl,
	name(Nom, L2).
nombre(0,[]).
nombre(X, L1) :-
	R is (X mod 10),
	Q is ((X-R)//10),
	chiffre_car(R,R1),
	char_code(R1,R2),
	nombre(Q, L),
	concat(L,[R2], L1).

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

concat([], L1, L1).
concat([X|Y], L1,[X|L2]) :- concat(Y, L1, L2).

enleve(X,[X|L], L) :-!.
enleve(X,[Y|L],[Y|L2]) :- enleve(X, L, L2).

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