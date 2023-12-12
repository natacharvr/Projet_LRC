/* Vérification sémantique */

concept(ConceptAtom) :- cnamea(ConceptAtom).
concept(ConceptNonAtom) :- cnamena(ConceptNonAtom).

% Vérification de la grammaire de ALC
concept(not(C)) :- concept(C).
concept(and(C1,C2)) :- concept(C1), concept(C2)!.
concept(or(C1,C2)) :- concept(C1), concept(C2)!.
concept(some(R,C)) :- rname(R), concept(C)!.
concept(all(R,C)) :- rname(R), concept(C)!.

/* Vérification auto référencement */
autoref([]).
autoref([C|L]) :- equiv(C, Def_C),
	pas-autoref(C, Def_C),
	autoref(L).

pas-autoref(_, C) :- cnamea(C).

pas-autoref(C, Def) :-
	C \== Def,
	cnamena(Def),
	equiv(Def, Def_developpe),
	pas-autoref(C, Def_developpe).

pas-autoref(C, and(D1,D2)) :-
	pas-autoref(C, D1),
	pas-autoref(C, D2).
	
pas-autoref(C, or(D1,D2)) :-
	pas-autoref(C, D1),
	pas-autoref(C, D2).

pas-autoref(C, all(_,D)) :-
	pas-autoref(C,D).

pas-autoref(C, some(_,D)) :-
	pas-autoref(C,D).
	
pas-autoref(C, not(D)) :-
	pas-autoref(C,D).

% Mise sous forme normale négative (fourni)
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

