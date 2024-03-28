module Demo where

-- Simplifying assumptions:
-- + work over Nats
-- + really define sort+remove-duplicates function

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

lemma :
  {x y : Nat} ->
  {l : List Nat} ->
  Lt x y ->
  CanAdd x l ->
  CanAdd x (insert y l)
lemma = {!!}

insert-ordered :
  {x : Nat} ->
  {l : List Nat} ->
  Ordered l ->
  Ordered (insert x l)
insert-ordered {x} {[]} l-ordered = ::-ordered []-ordered []-add
insert-ordered {x} {y :: l} l-ordered with compare x y
insert-ordered {x} {y :: l} (::-ordered l-ordered can-add-y) | lt-case x<y = ::-ordered (::-ordered l-ordered can-add-y) (::-add x<y can-add-y)
... | eq-case x=y = l-ordered
insert-ordered {x} {y :: l} (::-ordered l-ordered can-add-y) | gt-case x>y = ::-ordered (insert-ordered l-ordered) (lemma x>y can-add-y)

sort-ordered : (l : List Nat) -> Ordered (sort l)
sort-ordered [] = []-ordered
sort-ordered (x :: l) = insert-ordered (sort-ordered l)
