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

orb : Bool -> Bool -> Bool
orb true _ = true
orb false true = true
orb false false = false

----------------------------------------------------------------------
-- Natural Numbers

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

max : Nat -> Nat -> Nat
max zero n = n
max m zero = m
max (suc m) (suc n) = suc (max m n)

_-_ : Nat -> Nat -> Nat
zero - _ = zero
m - zero = m
suc m - suc n = m - n

----------------------------------------------------------------------
-- Products

data _*_ A B : Set where
  _,_ : A -> B -> A * B

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

data Either A B : Set where
  left : A -> Either A B
  right : B -> Either A B

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

----------------------------------------------------------------------
-- List

data List A : Set where
  [] : List A
  _::_ : A -> List A -> List A

all : {A : Set} -> (A -> Bool) -> List A -> Bool
all f [] = true
all f (x :: l) = andb (f x) (all f l)
