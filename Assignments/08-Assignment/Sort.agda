module Sort where

----------------------------------------------------------------------
-- Verified Sorting
--
-- You will be filling in a bit more of the of the proof that our
-- insertion sort implementation is correct.  See below for the holes
-- you need to fill in.
--
-- In addition to finishing the proof of orderedness, you will also
-- prove that sorted lists don't drop elements.
--
----------------------------------------------------------------------

open import CS400-Lib

data Lt : Nat -> Nat -> Set where
  zero-suc : {n : Nat} -> Lt zero (suc n)
  suc-suc : {m n : Nat} -> Lt m n -> Lt (suc m) (suc n)

Gt : Nat -> Nat -> Set
Gt m n = Lt n m

data Compare : Nat -> Nat -> Set where
  lt-case : {m n : Nat} -> Lt m n -> Compare m n
  eq-case : {m n : Nat} -> m =P n -> Compare m n
  gt-case : {m n : Nat} -> Gt m n -> Compare m n

compare : (m n : Nat) -> Compare m n
compare zero zero = eq-case refl
compare zero (suc n) = lt-case zero-suc
compare (suc m) zero = gt-case zero-suc
compare (suc m) (suc n) with compare m n
... | lt-case m<n = lt-case (suc-suc m<n)
... | eq-case m=n = eq-case (=P-cong suc m=n)
... | gt-case m>n = gt-case (suc-suc m>n)

insert : Nat -> List Nat -> List Nat
insert n [] = (n :: [])
insert n (x :: l) with compare n x
... | lt-case _ = n :: x :: l
... | eq-case _ = x :: l
... | gt-case _ = x :: insert n l

sort : List Nat -> List Nat
sort [] = []
sort (x :: l) = insert x (sort l)

test : Lt 3 5
test = suc-suc (suc-suc (suc-suc zero-suc))

data CanAdd : Nat -> List Nat -> Set where
  []-add : {x : Nat} -> CanAdd x []
  ::-add : {x y : Nat} -> {l : List Nat} -> Lt x y -> CanAdd y l -> CanAdd x (y :: l)

data Ordered : List Nat -> Set where
  []-ordered : Ordered []
  ::-ordered : {x : Nat} -> {l : List Nat} -> Ordered l -> CanAdd x l -> Ordered (x :: l)

-- Recall that we can read `CanAdd x l` as "x is less than every
-- element of l".  Prove that if x < y and x is less then every
-- element of l, then x is less than every element of (insert y l).
-- Then use this to finish the prove that `insert` preserves order
-- below.
can-add-insert :
  {x y : Nat} ->
  {l : List Nat} ->
  Lt x y ->
  CanAdd x l ->
  CanAdd x (insert y l)
can-add-insert = {!!}

-- Note the use of as-patterns.  This allows use to pattern match and
-- use a name See more at:
-- https://agda.readthedocs.io/en/v2.6.4.3/language/function-definitions.html#as-patterns
insert-ordered :
  {x : Nat} ->
  {l : List Nat} ->
  Ordered l ->
  Ordered (insert x l)
insert-ordered []-ordered = ::-ordered []-ordered []-add
insert-ordered {x} y::l-ordered@(::-ordered {y} l-ordered can-add-y) with compare x y
... | lt-case x<y = ::-ordered y::l-ordered (::-add x<y can-add-y)
... | eq-case x=y = y::l-ordered
... | gt-case y<x = {!!}

sort-ordered : (l : List Nat) -> Ordered (sort l)
sort-ordered [] = []-ordered
sort-ordered (x :: l) = insert-ordered (sort-ordered l)

-- This is an ADT represent that an element x is a member of a list l,
-- written x ∈ l.
data Elem {A : Set} : A -> List A -> Set where
  -- x ∈ x :: l
  here-it-is : {x : A} -> {l : List A} -> Elem x (x :: l)
  -- if x ∈ l then x ∈ y :: l
  keep-looking : {x y : A} -> {l : List A} -> Elem x l -> Elem x (y :: l)

-- The names of the constructors come from the fact that building a
-- proof that x∈l "simulates" a linear search.
test-elem : Elem 3 (2 :: 1 :: 3 :: [])
test-elem = keep-looking (keep-looking here-it-is)

-- If x ∈ l then x ∈ sort l. That is, sort does not drop elements
-- (this doesn't imply it don't introduce new elements).
--
-- Hint. Pattern match on `Elem x l`, then turn the two cases into two
-- lemmas you can prove separately.
sort-elem :
  {x : Nat} ->
  {l : List Nat} ->
  Elem x l ->
  Elem x (sort l)
sort-elem = {!!}
