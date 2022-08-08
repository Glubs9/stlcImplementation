open import Agda.Primitive

-- standard lib
-- TODO: add pairs
-- TODO: add unit
-- TODO: add eq
-- TODO: add bottom


-- defining stlc

-- agda stdlib is giving me trouble so this will do for now
-- note: this isn't de bruijn, this is just the first thing
-- I thought of
data Id : Set where
    n : Id
    s : Id -> Id

-- need to define equality on Id, but only need for cases anyway
case-eq : {n : Level} {b : Set n} -> Id -> Id -> b -> b -> b
case-eq n n b _ = b
case-eq (s n1) (s n2) b1 b2 = case-eq n1 n2 b1 b2 
case-eq _ _ _ b = b

infix 5 l_a_
infix 7 _*_
infix 9 `_

data Term : Set where
  `_ : Id -> Term
  l_a_ : Id -> Term -> Term
  _*_ : Term -> Term -> Term

infix 9 _[_:=_]

-- note: to try to get as much of this done as possible I am
-- ignoring variable capture (plfa also does this, but probs,
-- (cause they are switching to de bruijn shortly which does
-- not suffer this issue)
_[_:=_] : Term -> Id -> Term -> Term
(` x)   [ y := V ] = case-eq x y V (` x)
(A * B) [ y := V ] = A [ y := V ] * B [ y := V ]
(l x a B) [ y := V ] = case-eq x y (l x a B) (l x a (B [ y := V ]))


-- maybe add alpha-equiv and a real substitution


infix 4 _reduces_

-- non-deterministic operational semantics for fun :)
data _reduces_ : Term -> Term -> Set where
    appl : forall {L L' M} -> --plfa calls them eta rules but app makes more sense to me
           L reduces L' ->
           L * M reduces L' * M
    appr : forall {V M M'} ->
           M reduces M' ->
           V * M reduces V * M'
    beta : forall {x N V} ->
           (l x a N) * V reduces N [ x := V ]


infix 2 _reducesto_
infix 1 begin_
infix 2 _reduces_to_

data _reducesto_ : Term -> Term -> Set where
    _end : forall M -> M reducesto M
    _reduces_to_ : forall L {M N}
           -> L reduces M
           -> M reducesto N
           -> L reducesto N

-- something really weird is going on in the definition from plfa here
-- it's pattern matching on a type or something????
begin_ : forall {M N} -> M reducesto N -> M reducesto N
begin x = x

-- reflexive transitive closure (I like this definition better tbh)
infix 2 _reducesto'_
data _reducesto'_ : Term -> Term -> Set where
    step' : forall {M N}
        -> M reduces N
        -> M reducesto' N
    refl' : forall {M}
        -> M reducesto' M
    trans' : forall {L M N}
        -> L reducesto' M
        -> M reducesto' N
        -> L reducesto' N


-- need to get pair type first
-- postulate
--    confluence : forall {L M N}
--      -> ((L reducesto M), (L reducesto N))
--      -> ((P : Term), ((M reducesto P), (N reducesto P)))


-- types adding below here

infixr 7 _arrow_

-- plfa doesn't include var type which i feel could introduce some issues
data Type : Set where
    _arrow_ : Type -> Type -> Type
    Var : Id -> Type

data Context : Set where
    empty : Context
    _,_type_ : Context -> Id -> Type -> Context


infix 4 _ni_type_

-- have to add not equal to here after
data _ni_type_ : Context -> Id -> Type -> Set where
    Z : forall {G x A}
        -> G , x type A ni x type A
    S : forall {G x y A B}
        -> G ni x type A
        -> G , y type B ni x type A

infix 4 _impl_type_

data _impl_type_ : Context -> Term -> Type -> Set where
    refl : forall {G x A}
        -> G ni x type A
        -> G impl ` x type A

    lam-i : forall {G x N A B}
        -> G , x type A impl N type B
        -> G impl (l x a N) type (A arrow B)

    app-e : forall {G L M A B}
        -> G impl L type (A arrow B)
        -> G impl M type A
        -> G impl (L * M) type B


-- ni-functional

-- custom functions

-- as we don't have a notion of "value" we need an is-normalform

data is-normalform : Term -> Set where
    varNF : forall {x} ->
       is-normalform (` x)
    lamNF : forall {x V} ->
       is-normalform V ->
       is-normalform (l x a V)
    appNF : forall {x V} ->
       is-normalform V ->
       is-normalform ((` x) * V)



-- properties of stlc

-- progress now becomes, if e impl m type A then either is-normalForm M 
-- or \exists N s.t M reduces N

-- preservation is the same

-- import equality and values not reducing becomes easy
