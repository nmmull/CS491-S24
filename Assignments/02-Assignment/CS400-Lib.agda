module CS400-Lib where

----------------------------------------------------------------------
-- Booleans

data Bool : Set where
  true : Bool
  false : Bool

notb : Bool -> Bool
notb true = false
notb false = true

andb : Bool -> Bool -> Bool
andb false _ = false
andb true true = true
andb true false = false

infixr 6 _&&_

_&&_ : Bool -> Bool -> Bool
b && c = andb b c

infixr 5 _orb_

_orb_ : Bool -> Bool -> Bool
_orb_ true _ = true
_orb_ false true = true
_orb_ false false = false

----------------------------------------------------------------------
-- Natural Numbers

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

infix 4 _<_ _<=_ _==_

_<=_ : Nat -> Nat -> Bool
zero <= n = true
suc m <= zero = false
suc m <= suc n = m <= n

_==_ : Nat -> Nat -> Bool
zero == zero = true
zero == suc n = false
suc m == zero = false
suc m == suc n = m == n

_<_ : Nat -> Nat -> Bool
m < n = (m <= n) && (notb (m == n))

max : Nat -> Nat -> Nat
max zero n = n
max m zero = m
max (suc m) (suc n) = suc (max m n)

min : Nat -> Nat -> Nat
min m zero = zero
min zero n = zero
min (suc m) (suc n) = suc (min m n)

infixl 6 _+_ _-_
infixl 7 _*_

_+_ : Nat -> Nat -> Nat
zero + n = n
suc m + n = suc (m + n)

_*_ : Nat -> Nat -> Nat
zero * n = zero
suc m * n = n + m * n

_-_ : Nat -> Nat -> Nat
zero - _ = zero
m - zero = m
suc m - suc n = m - n

----------------------------------------------------------------------
-- List

data List A : Set where
  [] : List A
  _::_ : A -> List A -> List A

all : {A : Set} -> (A -> Bool) -> List A -> Bool
all f [] = true
all f (x :: l) = andb (f x) (all f l)

----------------------------------------------------------------------
-- Products

data And A B : Set where
  _,_ : A -> B -> And A B

_&_ : Set -> Set -> Set
A & B = And A B

----------------------------------------------------------------------
-- Fins

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

toNat : {n : Nat} -> Fin n -> Nat
toNat zero = zero
toNat (suc f) = suc (toNat f)

----------------------------------------------------------------------
-- Vectors

infixr 5 _::_

data Vec A : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

lookup : {A : Set} -> {n : Nat} -> Vec A n -> Fin n -> A
lookup (x :: _) zero = x
lookup (_ :: xs) (suc i) = lookup xs i

----------------------------------------------------------------------
-- Eithers (Unions)

data Or A B : Set where
  left : A -> Or A B
  right : B -> Or A B

----------------------------------------------------------------------
-- Propositional Equality

data _=P_ {A : Set} (x : A) : A -> Set where
  instance refl : x =P x

----------------------------------------------------------------------
-- Empty

data Empty : Set where

----------------------------------------------------------------------
-- Unit

record Unit : Set where
  instance constructor unit

----------------------------------------------------------------------
-- Decidability

isTrue : Bool -> Set
isTrue true = Unit
isTrue false = Empty

isFalse : Bool -> Set
isFalse true = Empty
isFalse false = Unit
