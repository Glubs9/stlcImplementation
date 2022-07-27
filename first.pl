% normal lambda calculus

% name()

%keep variables finite to make backwards work better
variable(X) :- list_member(X, [p,q,r,s,t,x,y,z,a,b,c]).

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
    not(list_member(FV, Y)).

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
    list_member(L, X),
    freshVar(app(Y,Val), F), %idea taken from "alpha-conversion is easy by Thorsten altenkirch"
    subst(Y, X, F, O1), 
    subst(abs(F,O1), Var, Val, O2).
subst(abs(X,Y), Var, Val, abs(X,O)) :-
    not(X = Var),
    fv(Val, L),
    not(list_member(L, X)),
    subst(Y, Var, Val, O).

%bruh I hsould test substitution but I can't be bothered lmaooooo


%left is unreduced, right is reduced
%oneStep(var(X), var(X)).
%oneStep(abs(var(_), X), abs(var(_), Y)) :- oneStep(X,Y).
%oneStep(app(X,Y))
