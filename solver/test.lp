% a :- b.
% c :- not b.
% b :- p.
% loop
q :- not p.
p :- not q.
#show t:p.