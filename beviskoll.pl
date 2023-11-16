% Den vi fick i instruktionen, läs bevisfil och unifiera premisser, mål och bevis. starta verifiering
verify(InputFileName) :-
	see(InputFileName),
	read(Premises), read(Conclusion), read(Proof),
	seen,
	valid_proof(Premises, Conclusion, Proof).


% ---- verify_proof ----

% Börja verifiering mha hjälppredikatet verify_proof/4, som har en tom lista som sedan ska fyllas med verifierade rader.
valid_proof(Premises, Conclusion, Proof) :-
	verify_proof(Premises, Conclusion, Proof, []).

% Case 1 - Vi har kommit till slutet av beviset, basfall, listan med icke-verifierade rader är tom och sista raden som lagts till i Verified är Conclusion
verify_proof(_Premises, Conclusion, [], [[_Row, Conclusion, _Rule]|_Verified]).

% Case 2 - Verifiera en box
verify_proof(Premises, Conclusion, [[[Row, Result, assumption]|BoxTail]|ProofTail], Verified) :-
	verify_box(Premises, Conclusion, BoxTail, [[Row, Result, assumption]|Verified]),
	verify_proof(Premises, Conclusion, ProofTail, [[[Row, Result, assumption]|BoxTail]|Verified]).

% Case 3 - Verifiera "vanliga" rader
verify_proof(Premises, Conclusion, [CurrRow|RestOfProof], Verified) :-
	verify_rule(Premises, CurrRow, Verified),   % Verifiera regeln
	verify_proof(Premises, Conclusion, RestOfProof, [CurrRow|Verified]). % Lägg till i lista och gå till nästa rad


% ---- verify_rule ----

% Premise - premise
verify_rule(Premises, [_Row, Result, premise], _Verified) :-
	member(Result, Premises).

% And introduction - andint
verify_rule(_Premises, [_Row, and(E1, E2), andint(Row1,Row2)], Verified) :-
	member([Row1, E1, _Rule1], Verified),
	member([Row2, E2, _Rule2], Verified).

% And elimination 1 - andel1
verify_rule(_Premises, [_Row, E, andel1(Row)], Verified) :-
	member([Row, and(E, _E), _Rule], Verified).

% And elimination 2 - andel2
verify_rule(_Premises, [_Row, E, andel2(Row)], Verified) :-
	member([Row, and(_E, E), _Rule], Verified).
	
% Or introduction 1 - orint1
verify_rule(_Premises, [_Row, or(E, _E), orint1(Row)], Verified) :-
	member([Row, E, _Rule], Verified).

% Or introduction 2 - orint2
verify_rule(_Premises, [_Row, or(_E, E), orint2(Row)], Verified) :-
	member([Row, E, _Rule], Verified).

% Or elimination - orel
verify_rule(_Premises, [_Row, Result, orel(A,B,C,D,E)], Verified) :-
	search_for_box(B, Verified, Box1),
	search_for_box(D, Verified, Box2),
	member([A, or(E1, E2), _RuleA], Verified),
	member([B, E1, _RuleB], Box1),
	member([D, E2, _RuleC], Box2),
	member([C, Result, _RuleD], Box1),
	member([E, Result, _RuleE], Box2),
	find_last_in_box(Box1, LastElement1),
	find_last_in_box(Box2, LastElement2),
	member(C, LastElement1),
	member(E, LastElement2).

% Implication introduction - impint
verify_rule(_Premises, [_Row, imp(E1, E2), impint(Row1, Row2)], Verified) :-
	search_for_box(Row1, Verified, Box),
	member([Row1, E1, assumption], Box),
	member([Row2, E2, _Rule], Box), 
	find_last_in_box(Box, LastElement),
	member(Row2, LastElement).

% Implication elimination - impel
verify_rule(_Premises, [_Row, Result, impel(Row1,Row2)], Verified) :-
	member([Row1, Imppremise, _Rule1], Verified),
	member([Row2, imp(Imppremise, Result), _Rule2], Verified).

% Negation Introduction - negint
verify_rule(_Premises, [_Row, neg(E), negint(Row1,Row2)], Verified) :-
	search_for_box(Row1, Verified, Box),
	member([Row1, E, assumption], Box),
	member([Row2, cont, _Rule], Box),
	find_last_in_box(Box, LastElement),
	member(Row2, LastElement).

% Negation elimination - negel
verify_rule(_Premises, [_Row, cont, negel(Row1,Row2)], Verified) :-
	member([Row1, E, _Rule1], Verified),
	member([Row2, neg(E), _Rule2], Verified).

% Double negation introduction - negnegint
verify_rule(_Premises, [_Row, neg(neg(E)), negnegint(Row)], Verified) :-
	member([Row, E, _Rule], Verified).

% Double negation elimination - negnegel
verify_rule(_Premises, [_Row, E, negnegel(Row)], Verified) :-
	member([Row, neg(neg(E)), _Rule], Verified).

% Copy - copy
verify_rule(_Premises, [_Row, E, copy(Row)], Verified) :-
	member([Row, E, _Rule], Verified).

% LEM - lem
verify_rule(_Premises, [_Row, or(E, neg(E)), lem], _Verified).

% MT - mt
verify_rule(_Premises, [_Row, neg(E1), mt(Row1,Row2)], Verified) :-
	member([Row1, imp(E1, E2), _Rule1], Verified),
	member([Row2, neg(E2), _Rule2], Verified).

% Contradiction elimination - contel
verify_rule(_Premises, [_Row, _Result, contel(Row)], Verified) :-
	member([Row, cont, _Rule], Verified).

% PBC (Proof by contradiction) - pbc
verify_rule(_Premises, [_Row, E, pbc(Row1,Row2)], Verified) :-
	search_for_box(Row1, Verified, Box),
	member([Row1, neg(E), assumption], Box),
	member([Row2, cont, _Rule], Box),
	find_last_in_box(Box, LastElement),
	member(Row2, LastElement).
	

% ---- verify_box ----

% Case 1 - Slutet på en box, basfall
verify_box(_Premises, _Conclusion, [], _Verified).

% Case 2 - En box med assumption på första raden hittas. Nödvändig för nästlade boxar.
verify_box(Premises, Conclusion, [[[Row, Result, assumption]|BoxTail]|ProofTail], Verified) :-
	% Verifiera resten av inre boxen. Lägg till assumptionrad i Verified. 
	verify_box(Premises, Conclusion, BoxTail, [[Row, Result, assumption]|Verified]),
	% Verifiera resten av boxen utanför. Lägg till inre box i Verified. 
	verify_box(Premises, Conclusion, ProofTail, [[[Row, Result, assumption]|BoxTail]|Verified]).

% Case 3 - Verifiera rader i boxen eller i box utanför om kallad från inre box
verify_box(Premises, Conclusion, [ProofHead|ProofTail], Verified) :-
	verify_rule(Premises, ProofHead, Verified),
	verify_box(Premises, Conclusion, ProofTail, [ProofHead|Verified]).

% ---- search_for_box ----

% Search for a box that begins at row RowNr at head of Verified
search_for_box(RowNr, [FirstElem|_Verified], FirstElem) :-
	member([RowNr, _Result, _Rule], FirstElem).

% Search for box that begins at row RowNr in the tail of Verified
search_for_box(RowNr, [_FirstElem|Verified], _Box) :-
	search_for_box(RowNr, Verified, _Box).

% Find the last element in a box
% Base case: Last element is found
find_last_in_box([LastElement], LastElement). 

% Recursively traverse the box
find_last_in_box([_FirstElem|Rest], LastElement) :-
    find_last_in_box(Rest, LastElement).
