open import CS400-Lib

infixr 5 _=>_

data SType : Set where
  B : SType
  _=>_ : SType -> SType -> SType

e1 : SType
e1 = B => B

e2 : SType
e2 = (B => B) => (B => (B => B))

Var : Set
Var = Nat

data LTerm : Set where
  f[_] : Var -> LTerm
  b[_] : Var -> LTerm
  Lam : LTerm -> LTerm
  _$_ : LTerm -> LTerm -> LTerm

e3 : LTerm
e3 = Lam b[ 0 ]

_[_/_] : LTerm -> LTerm -> Var -> LTerm
f[ y ] [ n / x ] with y == x
... | true = n
... | false = f[ y ]
b[ y ] [ n / x ] = b[ y ]
Lam m [ n / x ] = Lam (m [ n / x ])
(m1 $ m2) [ n / x ] = (m1 [ n / x ]) $ (m2 [ n / x ])

-- λ x . y
e4 : LTerm
e4 = Lam f[ 1 ]

k : {A B : Set} -> A -> B -> A
k x y = x

