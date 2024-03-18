module Slides where

open import CS400-Lib

Int : Set
Int = Nat & Nat

IsZero : Nat -> Set
IsZero zero = Unit
IsZero _ = Empty

IsNonEmpty : {A : Set} -> (l : List A) -> Set
IsNonEmpty [] = Empty
IsNonEmpty (x :: xs) = Unit

data NonEmpty A : List A -> Set where
  has-head :
    (x : A) -> (xs : List A) -> NonEmpty A (x :: xs)


head : {A : Set} -> (l : List A) -> (l-has-head : IsNonEmpty l) -> A
head (x :: xs) l-has-head = x

prop : {A B : Set} -> A & B -> B & A
prop (x , y) = (y , x)

de-morgan : {A B C : Set} -> A & B -> ((A -> C) \/ (B -> C)) -> C
de-morgan (a , b) (left a-imp-c) = a-imp-c a
de-morgan (a , b) (right b-imp-c) = b-imp-c b

de-morgan-again : {A B C : Set} -> A /\ B -> ((A -> C) \/ (B -> C)) -> C
de-morgan-again =
  \p ->
  \q ->
  case
    q
    (\f -> f (fst p))
    (\g -> g (snd p))

de-morgan-2 : {A B C : Set} -> (((A -> C) \/ (B -> C)) -> C) -> A /\ B
de-morgan-2 prf = {!   !}

de-morgan-3 : {A B C : Set} -> A \/ B -> ((A -> C) /\ (B -> C)) -> C
de-morgan-3 (left a) (ac , bc) = ac a
de-morgan-3 (right b) (ac , bc) = bc b

de-morgan-4 : {A B C : Set} -> (((A -> Empty) /\ (B -> Empty)) -> Empty) -> A \/ B
de-morgan-4 = {!   !}

even : Nat -> Set
even zero = True
even (suc zero) = False
even (suc (suc n)) = even n

odd : Nat -> Set
odd zero = False
odd (suc zero) = True
odd (suc (suc n)) = odd n

even-or-odd : (n : Nat) -> even n \/ odd n
even-or-odd = {!   !}

n-even-implies-sn-odd : (n : Nat) -> even n -> odd (suc n)
n-even-implies-sn-odd zero _ = unit
n-even-implies-sn-odd (suc zero) f = f
n-even-implies-sn-odd (suc (suc n)) n-is-even = n-even-implies-sn-odd n n-is-even

ind-Nat :
  (P : Nat -> Set)
  (p0 : P zero)
  (ind-hyp : (k : Nat) -> P k -> P (suc k))
  (n : Nat) -> P n
ind-Nat P p0 ind-hyp zero = p0
ind-Nat P p0 ind-hyp (suc n) = ind-hyp n (ind-Nat P p0 ind-hyp n)

n+0=n : (n : Nat) -> n + 0 =P n
n+0=n = qed where
  P : Nat -> Set
  P k = (k + 0) =P k

  base-case : (0 + 0) =P 0
  base-case = refl

  ind-step : (k : Nat) -> (pk : k + 0 =P k)-> (suc k) + 0 =P suc k
  ind-step k pk = cong suc pk

  qed = ind-Nat P base-case ind-step

n+0=n' : (n : Nat) -> (n + 0) =P n
n+0=n' zero = refl
n+0=n' (suc n) = cong suc (n+0=n n)

f : {A : Set} -> A -> A
f x = x

-- even-lem : (n : Nat) -> even n -> (n =P 0) \/ (Exists (\k -> 2 + k =P n))
even-lem : (n : Nat) -> even n -> n =P 0 \/ [ k ] (2 + k =P n)
even-lem zero prf = left refl
even-lem (suc (suc n)) prf = right (wit n refl)

data Even : Nat -> Set where
  zero-is-even : Even 0
  2+n-is-even : (n : Nat) -> Even n -> Even (suc (suc n))

is-even : Nat -> Bool
is-even zero = true
is-even (suc zero) = false
is-even (suc (suc n)) = is-even n

same-even-1 : (n : Nat) -> IsTrue (is-even n) -> even n
same-even-1 zero unit = unit
same-even-1 (suc (suc n)) prf = same-even-1 n prf

same-even-2 : (n : Nat) -> even n -> Even n
same-even-2 zero prf = zero-is-even
same-even-2 (suc (suc n)) prf = 2+n-is-even n (same-even-2 n prf)

same-even-3 : (n : Nat) -> Even n -> IsTrue (is-even n)
same-even-3 0 zero-is-even = unit
same-even-3 (suc (suc n)) (2+n-is-even n prf) = same-even-3 n prf

data LTE : Nat -> Nat -> Set where
  zero-case : (n : Nat) -> LTE 0 n
  suc-case : (n m : Nat) -> LTE n m -> LTE (suc n) (suc m)

data LTE2 : Nat -> Nat -> Set where
  refl-case-2 : (n : Nat) -> LTE2 n n
  suc-right-case-2 : (n m : Nat) -> LTE2 n m -> LTE2 n (suc m)

refl-LTE : (n : Nat) -> LTE n n
refl-LTE zero = zero-case zero
refl-LTE (suc n) = suc-case n n (refl-LTE n)

suc-right-LTE : (n m : Nat) -> LTE n m -> LTE n (suc m)
suc-right-LTE zero m prf = zero-case (suc m)
suc-right-LTE (suc n) (suc m) (suc-case .n .m prf) = suc-case n (suc m) (suc-right-LTE n m prf)

lte2-implies-lte : (m n : Nat) -> LTE2 m n -> LTE m n
lte2-implies-lte m .m (refl-case-2 .m) = refl-LTE m
lte2-implies-lte m .(suc n) (suc-right-case-2 .m n prf) =
  suc-right-LTE m n (lte2-implies-lte m n prf)






