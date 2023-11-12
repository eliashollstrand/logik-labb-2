% Den vi fick i instruktionen, läs bevisfil och unifiera premisser, mål och bevis. starta verifiering
verify(InputFileName) :-
	see(InputFileName),
	read(Premises), read(Goal), read(Proof),
	seen,
	valid_proof(Premises, Goal, Proof).

% ---- valid_proof ----

% Börja verifiering mha hjälppredikatet valid_proof/4, som har en tom lista som sedan ska fyllas med validerade rader.
valid_proof(Premises, Goal, Proof) :-
	valid_proof(Premises, Goal, Proof, []).


valid_proof(Premises, Goal, [CurrRow|RestOfProof], Verified) :-
	valid_rule(Premises, CurrRow, Verified),   % Verifiera regeln
	valid_proof(Premises, Goal, RestOfProof, [CurrRow|Verified]). % Lägg till i lista och gå till nästa rad

% Vi har kommit till slutet av beviset, basfall, listan med icke-validerade rader är tom och sista raden som lagts till i Verified är Goal
valid_proof(_Premises, Goal, [], [[_Row, Goal, _Rule]|_Validate]).

% Verifiera en box
valid_proof(Premises, Goal, [[[Row, Result, assumption]|Boxtail]|Prooftail], Verified) :-
	valid_box(Premises, Goal, Boxtail, [[Row, Result, assumption]|Verified]),
	valid_proof(Premises, Goal, Prooftail, [[[Row, Result, assumption]|Boxtail]|Verified]).


% ---- valid_rule ----

% Premise - premise
valid_rule(Premises, [_Row, Result, premise], _Verified) :-
	member(Result, Premises).

% And introduction - andint
valid_rule(_Premises, [_Row, and(E1, E2), andint(Row1,Row2)], Verified) :-
	member([Row1, E1, _Rule1], Verified),
	member([Row2, E2, _Rule2], Verified).

% And elimination 1 - andel1
valid_rule(_Premises, [_Row, E, andel1(Row)], Verified) :-
	member([Row, and(E, _), _Rule], Verified).

% And elimination 2 - andel2
valid_rule(_Premises, [_Row, E, andel2(Row)], Verified) :-
	member([Row, and(_, E), _Rule], Verified).
	
% Or introduction 1 - orint1
valid_rule(_Premises, [_Row, or(E, _), orint1(Row)], Verified) :-
	member([Row, E, _Rule], Verified).

% Or introduction 2 - orint2
valid_rule(_Premises, [_Row, or(_, E), orint2(Row)], Verified) :-
	member([Row, E, _Rule], Verified).

% Or elimination - orel
valid_rule(_Premises, [_Row, Result, orel(A,B,C,D,E)], Verified) :-
	find_box(B, Verified, Box1),
	find_box(D, Verified, Box2),
	member([A, or(E1, E2), _], Verified),
	member([B, E1, _], Box1),
	member([D, E2, _], Box2),
	member([C, Result, _], Box1),
	member([E, Result, _], Box2),
	find_last_in_box(Box1, LastElement1),
	find_last_in_box(Box2, LastElement2),
	member(C, LastElement1),
	member(E, LastElement2).

% Implication introduction - impint
valid_rule(_Premises, [_Row, imp(E1, E2), impint(Row1, Row2)], Verified) :-
	find_box(Row1, Verified, Box),
	member([Row1, E1, assumption], Box),
	member([Row2, E2, _], Box), 
	find_last_in_box(Box, LastElement),
	member(Row2, LastElement).

% Implication elimination - impel
valid_rule(_Premises, [_Row, Result, impel(Row1,Row2)], Verified) :-
	member([Row1, Imppremise, _], Verified),
	member([Row2, imp(Imppremise, Result),_Rule], Verified).

% Negation Introduction - negint
valid_rule(_Premises, [_Row, neg(E), negint(Row1,Row2)], Verified) :-
	find_box(Row1, Verified, Box),
	member([Row1, E, assumption], Box),
	member([Row2, cont, _], Box),
	find_last_in_box(Box, LastElement),
	member(Row2, LastElement).

% Negation elimination - negel
valid_rule(_Premises, [_Row, cont, negel(Row1,Row2)], Verified) :-
	member([Row1, E, _], Verified),
	member([Row2, neg(E), _], Verified).

% Double negation introduction - negnegint
valid_rule(_Premises, [_Row, neg(neg(E)), negnegint(Row)], Verified) :-
	member([Row, E, _Rule], Verified).

% Double negation elimination - negnegel
valid_rule(_Premises, [_Row, E, negnegel(Row)], Verified) :-
	member([Row, neg(neg(E)), _Rule], Verified).

% Copy - copy
valid_rule(_Premises, [_Row, E, copy(Row)], Verified) :-
	member([Row, E, _Rule], Verified).

% LEM - lem
valid_rule(_Premises, [_Row, or(E, neg(E)), lem], _Verified).

% MT - mt
valid_rule(_Premises, [_Row, neg(E1), mt(Row1,Row2)], Verified) :-
	member([Row1, imp(E1, E2), _], Verified),
	member([Row2, neg(E2), _], Verified).

% Contradiction elimination - contel
valid_rule(_Premises, [_Row, _Result, contel(Row)], Verified) :-
	member([Row, cont, _], Verified).

% PBC (Proof by contradiction) - pbc
valid_rule(_Premises, [_Row, E, pbc(Row1,Row2)], Verified) :-
	find_box(Row1, Verified, Box),
	member([Row1, neg(E), assumption], Box),
	member([Row2, cont, _], Box),
	find_last_in_box(Box, LastElement),
	member(Row2, LastElement).
	

% ---- valid_box ----

% Slutet på en box, basfall
valid_box(_Premises, _Goal, [], _Verified).

valid_box(Premises, Goal, [[[Row, Result, assumption]|Boxtail]|Prooftail], Verified) :-
	valid_box(Premises, Goal, Boxtail, [[Row, Result, assumption]|Verified]),
	valid_box(Premises, Goal, Prooftail, [[[Row, Result, assumption]|Boxtail]|Verified]).

valid_box(Premises, Goal, [Proofhead|Prooftail], Verified) :-
	valid_rule(Premises, Proofhead, Verified),
	valid_box(Premises, Goal, Prooftail, [Proofhead|Verified]).

% ---- find_box ----

% Första raden är en box som innehåller eftersökt rad.
find_box(Searchfor, [Boxhead|_Verified], Boxhead) :-
	member([Searchfor, _, _], Boxhead).

% Om inte leta efter raden i svansen.
find_box(Searchfor, [_|Verified], _Box) :-
	find_box(Searchfor, Verified, _Box).

% Find the last element in a box
find_last_in_box([LastElement], LastElement). % Base case: Last element is found

find_last_in_box([_|Rest], LastElement) :-
    find_last_in_box(Rest, LastElement). % Recursively traverse the box
