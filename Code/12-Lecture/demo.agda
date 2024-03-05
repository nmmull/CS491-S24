open import CS400-Lib

Var : Set
Var = Nat

x : Var
x = 0

y : Var
y = 1

-- data LTerm : Set where
--   var : Var -> LTerm
--   abs : Var -> LTerm -> LTerm
--   app : LTerm -> LTerm -> LTerm

-- x : Var
-- x = 0

-- y : Var
-- y = 1

-- -- λ x . λ y . x
-- k : LTerm
-- k = abs x (abs y (var x))

data LTerm : Set where
  bvar : Var -> LTerm
  fvar : Var -> LTerm
  abs : LTerm -> LTerm
  app : LTerm -> LTerm -> LTerm

k : LTerm
k = abs (abs (bvar 1))

-- λ x . y
c : LTerm
c = abs (fvar y)

-- m [ n / x ]
_[_/_] : LTerm -> LTerm -> Var -> LTerm
bvar y [ n / x ] = bvar y
fvar y [ n / x ] with y == x
... | true = n
... | false = fvar y
abs m [ n / x ] = abs (m [ n / x ])
app p q [ n / x ] = app (p [ n / x ]) (q [ n / x ])
