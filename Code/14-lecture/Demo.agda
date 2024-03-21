module Demo where

open import CS400-Lib

-- A and B -> not (not A or Not B)
-- (A & B) -> Or (A -> Empty) (B -> Empty) -> Empty
-- (A /\ B) -> Not ((Not A) \/ (Not B))
de-morgan : {A B : Set} -> (A /\ B) -> Not ((Not A) \/ (Not B))
de-morgan (x , y) (left na) = na x
de-morgan (x , y) (right nb) = nb y

de-morgan' : {A B : Set} -> (A /\ B) -> Not ((Not A) \/ (Not B))
de-morgan' =
  \p -> \q ->
  case q
    (\na -> na (fst p))
    (\nb -> nb (snd p))

-- de-morgan-2 : {A B : Set} -> ((A -> Empty) \/ (B -> Empty) -> Empty) -> A /\ B
-- de-morgan-2 not-na-or-na = {!   !}

IsEven : Nat -> Set
IsEven zero = Unit
IsEven (suc zero) = Empty
IsEven (suc (suc n)) = IsEven n

data Even : Nat -> Set where
  zero-is-even : Even 0
  suc-suc-is-even : (n : Nat) -> Even n -> Even (suc (suc n))

test : IsEven 8
test = unit

test-2 : IsEven 7 -> Empty
test-2 prf = prf

test-3 : Even 8
test-3 =
  suc-suc-is-even 6
    (suc-suc-is-even 4
      (suc-suc-is-even 2
        (suc-suc-is-even 0 zero-is-even)))

even : Nat -> Bool
even 0 = true
even 1 = false
even (suc (suc k)) = even k

test-4 : IsTrue (even 8)
test-4 = unit

-- exists k . k * 2 = n

ind-Nat :
  (P : Nat -> Set) ->
  (base : P 0) ->
  (ind-hyp : (k : Nat) -> P k -> P (suc k)) ->
  (n : Nat) -> P n
ind-Nat P base ind-hyp zero = base
ind-Nat P base ind-hyp (suc n) = ind-hyp n (ind-Nat P base ind-hyp n)

n+0=n : (n : Nat) -> n + 0 =P n
n+0=n = qed where

  P : Nat -> Set
  P k = k + 0 =P k

  base : 0 + 0 =P 0
  base = refl

  ind-step : (k : Nat) -> k + 0 =P k -> suc k + 0 =P suc k
  ind-step k k+0=k = cong suc k+0=k

  qed : (n : Nat) -> n + 0 =P n
  qed = ind-Nat P base ind-step