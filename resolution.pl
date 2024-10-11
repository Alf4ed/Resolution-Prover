/*
1. YES
2. YES
3. YES
4. NO
5. YES
6. YES
7. YES
8. NO
9. NO
10. YES
*/

/*
 * A Resolution prover by Alfred Carpenter
 * Converts a propositional formula into CNF form.
 * Applies a finite number of resolution rules.
 * Outputs whether the formula is a Tautology.
*/

% Propositional operators are: neg, and, or, imp, revimp, uparrow, downarrow, notimp and notrevimp.
?-op(500, fy, neg).
?-op(600, xfy, [and, downarrow, notimp, notrevimp]).
?-op(700, xfy, [or, imp, revimp, uparrow]).
?-op(800, xfy, [equiv, notequiv]).

% member(Item, List) :- Item occurs in List.
member(X, [X|_]).
member(X, [_|Tail]) :- member(X, Tail).

% remove(Item, List, Newlist) :- Newlist is the result of removing all occurrences of Item from List.
remove(_, [], []).
remove(X, [X|Tail], Newtail) :- !, remove(X, Tail, Newtail).
remove(X, [Head|Tail], [Head|Newtail]) :- remove(X, Tail, Newtail).

% append(X, Y, Z) :- List Z is the result of appending Y to X
append([], X, X).
append([X|Tail], Y, [X|Z]) :- append(Tail, Y, Z).

% conjunctive(X) :- X is an alpha formula.
conjunctive(_ and _).
conjunctive(neg(_ or _)).
conjunctive(neg(_ imp _)).
conjunctive(neg(_ revimp _)).
conjunctive(neg(_ uparrow _)).
conjunctive(_ downarrow _).
conjunctive(_ notimp _).
conjunctive(_ notrevimp _).

% disjunctive(X) :- X is a beta formula.
disjunctive(neg(_ and _)).
disjunctive(_ or _).
disjunctive(_ imp _).
disjunctive(_ revimp _).
disjunctive(_ uparrow _).
disjunctive(neg(_ downarrow _)).
disjunctive(neg(_ notimp _)).
disjunctive(neg(_ notrevimp _)).

disjunctive(_ equiv _).
disjunctive(_ notequiv _).
disjunctive(neg(_ equiv _)).
disjunctive(neg(_ notequiv _)).

% unary(X) :- X is a double negation, or a negated constant.
unary(neg neg _).
unary(neg true).
unary(neg false).

% components(X, Y, Z) :- Y and Z are the components of the formula X, as defined in the alpha and beta table.
components(X and Y, X, Y).
components(neg(X and Y), neg X, neg Y).
components(X or Y, X, Y).
components(neg(X or Y), neg X, neg Y).
components(X imp Y, neg X, Y).
components(neg(X imp Y), X, neg Y).
components(X revimp Y, X, neg Y).
components(neg(X revimp Y), neg X, Y).
components(X uparrow Y, neg X, neg Y).
components(neg(X uparrow Y), X, Y).
components(X downarrow Y, neg X, neg Y).
components(neg(X downarrow Y), X, Y).
components(X notimp Y, X, neg Y).
components(neg(X notimp Y), neg X, Y).
components(X notrevimp Y, neg X, Y).
components(neg(X notrevimp Y), X, neg Y).

components(X equiv Y, (X and Y), (neg X and neg Y)).
components(X notequiv Y, (X and neg Y), (neg X and Y)).
components(neg(X equiv Y), (X and neg Y), (neg X and Y)).
components(neg(X notequiv Y), (X and Y), (neg X and neg Y)).

% component(X, Y) :- Y is the component of the unary formula X.
component(neg neg X, X).
component(neg true, false).
component(neg false, true).

% singlestep(Old, New) :- New is the result of applying a single step of the expansion process to Old.
singlestep([Disjunction|Rest], New) :-
    member(Formula, Disjunction),
    unary(Formula),
    component(Formula, Newformula),
    remove(Formula, Disjunction, Temporary),
    Newdis = [Newformula|Temporary],
    New = [Newdis|Rest].

singlestep([Disjunction|Rest], New) :-
    member(Alpha, Disjunction),
    conjunctive(Alpha),
    components(Alpha, Alphaone, Alphatwo),
    remove(Alpha, Disjunction, Temporary),
    Newdisone = [Alphaone|Temporary],
    Newdistwo = [Alphatwo|Temporary],
    New = [Newdisone, Newdistwo|Rest].

singlestep([Disjunction|Rest], New) :-
    member(Beta, Disjunction),
    disjunctive(Beta),
    components(Beta, Betaone, Betatwo),
    remove(Beta, Disjunction, Temporary),
    Newdis = [Betaone, Betatwo|Temporary],
    New = [Newdis|Rest].

singlestep([Disjunction|Rest], [Disjunction|Newrest]) :-
    singlestep(Rest, Newrest).

% expand(Old, New) :- New is the result of applying singlestep as many times as possible, starting with Old.
expand(Con, Newcon) :-
    singlestep(Con, TempA),
    simplify(TempA, TempB),
    removetrivial(TempB, Temp),
    expand(Temp, Newcon).

expand(Con, Con).

% clauseform(X, Y) :- Y is the clause form of X.
clauseform(X, Y) :- expand([[X]], Y).

% true if list X contains an element and its negation
trivial(X) :-
    member(A, X),
    member(neg A, X).

% resolutionstep(Old, New) :- New is the result of applying a single resolution rule to Old
resolutionstep(Old, New) :-
    member(X, Old),
    member(Y, Old),
    X \= Y,
    member(A, X),
    remove(A, X, TempA),
    member(neg A, Y),
    remove(neg A, Y, TempB),
    append(TempA, TempB, Resolved),
    sort(Resolved, TempOne),
    \+ trivial(TempOne),
    \+ member(TempOne, Old),
    New = [TempOne|Old].

% Checks if the partially expaned CNF formula is already closed
resolution(Con, Newcon) :-
    closed(Con),
    Newcon = Con.

% resolution(Old, New) :- New is the result of applying the resolution rule as many times as possible
resolution(Con, Newcon) :-
    resolutionstep(Con, Temp), !,
    resolution(Temp, Newcon).

resolution(Con, Con).

% removetrivial(X, Y) :- Y is the result of deleting all trivially true clauses (ones containing A and neg A) from the CNF, X
removetrivial(X, Y) :-
    [Head|Tail] = X,
    trivial(Head),
    removetrivial(Tail, Z),
    Y = Z.

removetrivial(X, Y) :-
    [Head|Tail] = X,
    removetrivial(Tail, Z),
    Y = [Head|Z].

removetrivial(X, X).

% simplify(X, Y) :- Y is the result of removing duplicate elements from the disjunctions contained within the CNF, X
simplify(X, Y) :-
    [Head|Tail] = X,
    sort(Head, Z),
    simplify(Tail, R),
    Y = [Z|R].

simplify(X, X).

% closed(Resolution) :- The CNF contains the empty clause, [].
closed(Resolution) :-
    member([], Resolution).

% test(X) :- create a complete resolution expansion for neg X, and see if it is closed.
test(X) :-
    expand([[neg X]], Y),
    resolution(Y, Result),
    if_then_else(closed(Result), yes, no).

yes :- write('YES').
no :- write('NO').

%  if_then_else(P, Q, R) :- either P and Q, or not P and R.
if_then_else(P, Q, _) :- P, !, Q.
if_then_else(_, _, R) :- R.