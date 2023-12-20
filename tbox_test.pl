cnamea(femme).
cnamea(homme).

cnamena(nonbinaire).
cnamena(binaire).


iname(stephane).
iname(marie).

% Tbox non auto-reférente
equiv(nonbinaire, and(not(femme), not(homme))).
equiv(binaire, or(femme, homme)).

% Tbox auto-référente
% equiv(nonbinaire, not(binaire)).
% equiv(binaire, not(nonbinaire)).

inst(stephane, nonbinaire).
inst(marie, femme).
inst(stephane, all(epouse, femme)).

rname(epouse).

instR(stephane, marie, epouse).

 Tbox : [(binaire : femme or homme), (nonbinaire : not femme and not homme)]
 Abr : [(<stephane, marie> :epouse)]
 Abi : [(marie : femme), (stephane : nonbinaire)]