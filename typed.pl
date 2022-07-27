% normal lambda calculus

% name()

%keep variables finite to make backwards work better
variable(X) :- member(X, [p,q,r,s,t,x,y,z,a,b,c]).

isTerm(var(X)) :- variable(X).
isTerm(app(X,Y)) :- isTerm(X), isTerm(Y).
isTerm(abs(X, Y)) :- variable(X), isTerm(Y).

rm([], _, []).
rm([X|Y], X, Y).
rm([A|B], C, [A|D]) :- rm(B, C, D).

fv(var(X), [X]).
fv(app(X,Y), Z) :- 
    fv(X, FX),
    fv(Y, FY),
    append(FX,FY,Z).
fv(abs(X,Y), Z) :- 
    fv(Y,FY),
    rm(FY, X, Z).

% freshVar Term X Variable
freshVar(X, Y) :- 
    variable(Y),
    fv(X, FV),
    not(member(Y, FV)).

%subst : PreSubst Term X Var X substVal X PostSubst Term
%not equals doesn't specify domain hence this doesn't work backwards.
    %if the need for backwards comes in then define a set of variables
subst(var(X), X, Y, Y) :- isTerm(Y). %making backwards half work
subst(var(X), Y, _, var(X)) :- X \== Y.
subst(app(X,Y), Var, Val, app(Xsub,Ysub)) :- subst(X,Var,Val,Xsub), subst(Y,Var,Val,Ysub).
subst(abs(X,Y), X, _, abs(X, Y)).
subst(abs(X,Y), Var, Val, O2) :-
    not(X = Var),
    fv(Val, L),
    member(X, L),
    freshVar(app(Y,Val), F), %idea taken from "alpha-conversion is easy by Thorsten altenkirch"
    subst(Y, X, F, O1), 
    subst(abs(F,O1), Var, Val, O2).
subst(abs(X,Y), Var, Val, abs(X,O)) :-
    not(X = Var),
    fv(Val, L),
    not(member(X, L)),
    subst(Y, Var, Val, O).

%bruh I hsould test substitution but I can't be bothered lmaooooo
betaStep(var(X), var(X)).
betaStep(abs(X,Y), abs(X,Z)) :- beta(Y, Z).
betaStep(app(abs(X,Y), Z), O2) :-
    subst(Y, X, Z, O1),
    betaStep(O1, O2).
betaStep(app(X,Y), app(O1,O2)) :- 
    not(abs(_, _) = X),
    betaStep(X, O1),
    betaStep(Y, O2).

beta(X, X) :- betaStep(X, X).
beta(X, Y) :- 
    betaStep(X, Z),
    not(X = Z),
    beta(Z, Y).

tests() :-
    beta(app(abs(x, var(x)), abs(x, var(x))), abs(x, var(x))),
    beta(app(app(
        abs(x, abs(y, var(x))), 
        var(y)), var(x)), 
    var(y)).

inf() :- beta(app(
    abs(x, app(var(x), var(x))),
    abs(x, app(var(x), var(x)))
    ), _).
