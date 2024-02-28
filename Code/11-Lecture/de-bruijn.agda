module De-Bruijn where

open import CS400-Lib

Var : Set
Var = Nat

data LTerm : Set where
  var : Var -> LTerm
  app : LTerm -> LTerm -> LTerm
  abs : Var -> LTerm -> LTerm

data LNTerm : Set where
  bvar : Var -> LNTerm
  fvar : Var -> LNTerm
  app : LNTerm -> LNTerm -> LNTerm
  abs : LNTerm -> LNTerm

subst : LNTerm -> LNTerm -> Var -> LNTerm
subst (bvar y) n x = bvar y
subst (fvar y) n x with y == x
subst (fvar y) n x | true = n
subst (fvar y) n x | false = fvar y
subst (app m1 m2) n x = app (subst m1 n x) (subst m2 n x)
subst (abs m) n x = abs (subst m n x)

to-LN : LTerm -> LNTerm
to-LN = go where
  replace : LNTerm -> Var -> Var -> LNTerm
  replace (bvar y) _ _ = (bvar y)
  replace (fvar y) i x with x == y
  ... | true = bvar i
  ... | false = fvar y
  replace (app m n) i x = app (replace m i x) (replace n i x)
  replace (abs m) i x = abs (replace m (i + 1) x)

  go : LTerm -> LNTerm
  go (var x) = fvar x
  go (app m n) = app (to-LN m) (to-LN n)
  go (abs x m) = abs (replace (go m) 0 x)

x = 0
y = 1

k : LTerm
k = abs x (abs y (var x))
