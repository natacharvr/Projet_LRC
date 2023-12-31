% Natacha Rivière 28706745
% Léa Movsessian 28624266

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
inst(marie, some(epouse, not(homme))).

rname(epouse).

instR(stephane, marie, epouse).
