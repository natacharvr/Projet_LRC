% equiv(ConceptNonAtom, ConceptGen)
% inst(Instance, ConceptGen)
% instR(Instance1, Instance2, role)
% cnamea(ConceptAtom)
% cnamena(ConceptNonAtom)
% iname(Instance)
% rname(Role)

% TBox exercice 3 TD4

%équivalences entre concepts
equiv(sculpteur,and(personne,some(aCree,sculpture))).
equiv(auteur,and(personne,some(aEcrit,livre))).
equiv(editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite, livre)))).
equiv(parent,and(personne,some(aEnfant,anything))).
% Concepts atomiques
cnamea(personne).
cnamea(livre).
cnamea(objet).
cnamea(sculpture).
cnamea(anything).
cnamea(nothing).
% Concepts non-atomiques
cnamena(auteur).
cnamena(editeur).
cnamena(sculpteur).
cnamena(parent).
% Identificateurs des instances 
iname(michelAnge).
iname(david).
iname(sonnets).
iname(vinci).
iname(joconde).
% Identificateurs des roles
rname(aCree).
rname(aEcrit).
rname(aEdite).
rname(aEnfant).
% instanciations de concepts
inst(michelAnge,personne).
inst(david,sculpture).
inst(sonnets,livre).
inst(vinci,personne).
inst(joconde,objet).
% instanciations de roles
instR(michelAnge, david, aCree).
instR(michelAnge, sonnets, aEcrit).
instR(vinci, joconde, aCree).

% Tbox
[(sculpteur,and(personne,some(aCree,sculpture))), (auteur,and(personne,some(aEcrit,livre))), (editeur,and(personne,and(not(some(aEcrit,livre)),some(aEdite,livre)))),(parent,and(personne,some(aEnfant,anything)))]
% Abox assertions de concepts
[(michelAnge,personne), (david,sculpture), (sonnets,livre), (vinci,personne), (joconde,objet)]
% ABox assertions de roles
[(michelAnge, david, aCree), (michelAnge, sonnets, aEcrit),(vinci, joconde, aCree)]