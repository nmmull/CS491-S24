module Lecture where

module Equlity where
  data Equal {A : Set} (x : A) : A -> Set where
    refl : Equal x x

  sym : {A : Set} {x y : A} -> Equal x y -> Equal y x
  sym refl = refl

  trans : {A : Set} {x y z : A} -> Equal x y -> Equal y z -> Equal x z
  trans refl refl = refl

  cong : {A B : Set} {x y : A} -> (f : A -> B) -> Equal x y -> Equal (f x) (f y)
  cong f refl = refl

open import CS400-Lib

----------------------------------------------------------------------
-- Reflection

even : Nat -> Bool
even 0 = true
even 1 = false
even (suc (suc n)) = even n

test : IsTrue (even 10)
test = unit

IsEven : Nat -> Set
IsEven 0 = Unit
IsEven 1 = Empty
IsEven (suc (suc n)) = IsEven n

lem : (n : Nat) -> IsTrue (even n) -> IsEven n
lem zero _ = unit
lem (suc zero) fls = fls
lem (suc (suc n)) prf = lem n prf

data Even : Nat -> Set where
  z-even : Even 0
  2+even : (n : Nat) -> Even n -> Even (2 + n)

example : Even 4
example = 2+even 2 (2+even 0 z-even)

even-refl : (n : Nat) -> IsTrue (even n) -> Even n
even-refl zero _ = z-even
even-refl (suc zero) ()
even-refl (suc (suc n)) n-is-even = 2+even n (even-refl n n-is-even )

example2 : Even 1000
example2 = even-refl 1000 unit

-- n is even if there is a k s.t. k + k = n

even-split : (n : Nat) -> Even n -> [ k ] (k + k =P n)
even-split zero is-even = wit zero refl
even-split (suc (suc n)) (2+even n n-is-even) with even-split n n-is-even
... | wit k k+k=n = wit (suc k) {!!}

----------------------------------------------------------------------
-- Arithmetic Equalities

n+0=n : (n : Nat) -> n + 0 =P n
n+0=n zero = qed where
  qed : 0 + 0 =P 0 -- definition of +
  qed = refl
n+0=n (suc n) = qed where
  eq1 : (suc n) + 0 =P suc (n + 0)
  eq1 = refl -- by def. of +

  eq2 : suc (n + 0) =P suc n
  eq2 = =P-cong suc (n+0=n n)  -- by ind. hyp.

  qed : suc n + 0 =P suc n
  qed = eq1 =P= eq2

sm+n=m+sn : (m n : Nat) -> suc m + n =P m + suc n
sm+n=m+sn zero n =
  suc 0 + n =P suc (0 + n) by[ refl ] -- by def.
            &= suc n       by[ refl ] -- by def.
            &= 0 + suc n   by[ refl ] -- by def.
sm+n=m+sn (suc m) n =
  suc (suc m) + n =P suc (suc m + n) by[ refl ] -- by def.
                  &= suc (m + suc n) by[ =P-cong suc (sm+n=m+sn m n) ] -- by IH
                  &= suc m + suc n   by[ refl ] -- by def.

+-sym : (n m : Nat) -> n + m =P m + n
+-sym zero m = qed where
  eq1 : 0 + m =P m -- by def.
  eq1 = refl

  eq2 : m =P m + 0 -- by prev. lem.
  eq2 = =P-sym (n+0=n m)

  qed : 0 + m =P m + 0
  qed = eq1 =P= eq2
+-sym (suc n) m =
  (suc n) + m =P suc (n + m) by[ refl ] -- by def.
              &= suc (m + n) by[ =P-cong suc (+-sym n m) ] -- by IH
              &= suc m + n   by[ refl ] -- by def.
              &= m + suc n   by[ sm+n=m+sn m n ] -- lem.

----------------------------------------------------------------------
-- List Equality

rev : {A : Set} -> (l : List A) -> List A
rev [] = []
rev (x :: l) = rev l ++ (x :: [])

rev-++ : {A : Set} -> (l r : List A) -> rev (l ++ r) =P rev r ++ rev l
rev-++ = {!!}

rev-rev : {A : Set} -> (l : List A) -> rev (rev l) =P l
rev-rev [] =
  rev (rev []) =P rev [] by[ refl ] -- by def.
               &= []     by[ refl ] -- by def.
rev-rev (x :: l) =
  rev (rev (x :: l)) =P rev (rev l ++ (x :: []))     by[ refl ] -- by def.
                     &= rev (x :: []) ++ rev (rev l) by[ rev-++ (rev l) (x :: []) ] -- by ???
                     &= (x :: []) ++ rev (rev l)     by[ refl ] -- by def.
                     &= (x :: []) ++ l               by[ =P-cong (\l -> (x :: []) ++ l) (rev-rev l) ] -- by IH
                     &= x :: ([] ++ l)               by[ refl ] -- by def.
                     &= x :: l                       by[ refl ] -- by def.
