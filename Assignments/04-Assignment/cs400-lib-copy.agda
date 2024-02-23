module CS400-Lib-Copy where

----------------------------------------------------------------------
-- Booleans

data Bool : Set where
  true : Bool
  false : Bool

module Bools where
  not : Bool -> Bool
  not true = false
  not false = true

  and : Bool -> Bool -> Bool
  and false _ = false
  and true true = true
  and true false = false

  or : Bool -> Bool -> Bool
  or true _ = true
  or false true = true
  or false false = false

  eq : Bool -> Bool -> Bool
  eq true true = true
  eq false false = true
  eq _ _ = false

  xor : Bool -> Bool -> Bool
  xor true true = false
  xor true false = true
  xor false true = true
  xor false false = false

  infix 4 _==_
  _==_ = eq

notb = Bools.not
andb = Bools.and
orb = Bools.or
eqb = Bools.eq
xorb = Bools.xor

infixr 5 _OR_
infixr 6 _&&_
infixr 4 _==b_

_&&_ = Bools.and
_OR_ = Bools.or
_==b_ = Bools.eq

----------------------------------------------------------------------
-- Natural Numbers

data Nat : Set where
  zero : Nat
  suc : Nat -> Nat
{-# BUILTIN NATURAL Nat #-}

module Nats where
  eq : Nat -> Nat -> Bool
  eq zero zero = true
  eq zero (suc n) = false
  eq (suc n) zero = false
  eq (suc m) (suc n) = eq m n

  neq : Nat -> Nat -> Bool
  neq m n = notb (eq m n)

  leq : Nat -> Nat -> Bool
  leq zero n = true
  leq (suc m) zero = false
  leq (suc m) (suc n) = leq m n

  lt : Nat -> Nat -> Bool
  lt m n = leq m n && neq m n

  max : Nat -> Nat -> Nat
  max zero n = n
  max (suc m) zero = (suc m)
  max (suc m) (suc n) = suc (max m n)

  min : Nat -> Nat -> Nat
  min m zero = zero
  min zero (suc _) = zero
  min (suc m) (suc n) = suc (min m n)

  add : Nat -> Nat -> Nat
  add zero n = n
  add (suc m) n = suc (add m n)

  mul : Nat -> Nat -> Nat
  mul zero n = zero
  mul (suc m) n = add n (mul m n)

  sub : Nat -> Nat -> Nat
  sub zero _ = zero
  sub (suc m) zero = (suc m)
  sub (suc m) (suc n) = sub m n

infix 4 _<_ _<=_ _==_

_==_ = Nats.eq
_<=_ = Nats.leq
_<_ = Nats.lt

max = Nats.max
min = Nats.min

infixl 6 _+_ _-_
infixl 7 _*_

_+_ = Nats.add
_*_ = Nats.mul
_-_ = Nats.sub

----------------------------------------------------------------------
-- List

infixr 5 _::_

data List A : Set where
  [] : List A
  _::_ : A -> List A -> List A

module Lists where
  map : {A : Set} -> {B : Set} -> (A -> B) -> List A -> List B
  map f [] = []
  map f (x :: xs) = f x :: map f xs

  all : {A : Set} -> (A -> Bool) -> List A -> Bool
  all f [] = true
  all f (x :: l) = (f x) && (all f l)

  any : {A : Set} -> (A -> Bool) -> List A -> Bool
  any f [] = false
  any f (x :: xs) = (f x) OR (any f xs)

  append : {A : Set} -> List A -> List A -> List A
  append [] l = l
  append (x :: xs) l = x :: append xs l

mapL = Lists.map
allL = Lists.all
anyL = Lists.any

infixr 5 _++_
_++_ = Lists.append

----------------------------------------------------------------------
-- Maybe

data Maybe A : Set where
  Nothing : Maybe A
  Just : A -> Maybe A

module Maybes where
  map : {A : Set} -> {B : Set} -> (A -> B) -> Maybe A -> Maybe B
  map f Nothing = Nothing
  map f (Just x) = Just (f x)

mapM = Maybes.map

----------------------------------------------------------------------
-- Products

data And A B : Set where
  _,_ : A -> B -> And A B

infixr 2 _&_
_&_ : Set -> Set -> Set
A & B = And A B

fst : {A : Set} -> {B : Set} -> And A B -> A
fst (a , b) = a

snd : {A : Set} -> {B : Set} -> And A B -> B
snd (a , b) = b

----------------------------------------------------------------------
-- Fins

data Fin : Nat -> Set where
  zero : {n : Nat} -> Fin (suc n)
  suc : {n : Nat} -> Fin n -> Fin (suc n)

module Fins where
  toNat : {n : Nat} -> Fin n -> Nat
  toNat zero = zero
  toNat (suc f) = suc (toNat f)

toNatF = Fins.toNat

----------------------------------------------------------------------
-- Vectors

data Vec A : Nat -> Set where
  [] : Vec A zero
  _::_ : {n : Nat} -> A -> Vec A n -> Vec A (suc n)

module Vecs where
  lookup : {A : Set} -> {n : Nat} -> Vec A n -> Fin n -> A
  lookup (x :: _) zero = x
  lookup (_ :: xs) (suc i) = lookup xs i

----------------------------------------------------------------------
-- Eithers (Unions)

data Or A B : Set where
  left : A -> Or A B
  right : B -> Or A B

Either : Set -> Set -> Set
Either = Or

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

IsTrue : Bool -> Set
IsTrue true = Unit
IsTrue false = Empty

IsFalse : Bool -> Set
IsFalse true = Empty
IsFalse false = Unit
