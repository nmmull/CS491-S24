----------------------------------------------------------------------
-- Splitting Vectors
--
-- In lecture we saw that we could split a vector into two lists.  It
-- would be more satsifying we could split it into two vectors, but
-- this requires knowing the sizes of the vectors after splitting.
-- With dependent types, this is possible.
--
-- Implement a function `split` which given a vector `v` and an index
-- `i`, returns two vectors gotten by splitting `v` at `i`.
--
-- Note the type. It expresses, the length of each part of the split
-- vector.
--
-- Please try to use with-abstraction when you define this function.
----------------------------------------------------------------------

module Split-Standalone where

module CS400-Lib-Copy where

  ----------------------------------------------------------------------
  -- Natural Numbers

  data Nat : Set where
    zero : Nat
    suc : Nat -> Nat
  {-# BUILTIN NATURAL Nat #-}

  module Nats where
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

  infixl 6 _+_ _-_
  infixl 7 _*_

  _+_ = Nats.add
  _*_ = Nats.mul
  _-_ = Nats.sub

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

  lookupV = Vecs.lookup

  ----------------------------------------------------------------------
  -- Products

  infixr 4 _,_

  data And A B : Set where
    _,_ : A -> B -> And A B

  infixr 2 _&_
  _&_ : Set -> Set -> Set
  A & B = And A B

open CS400-Lib-Copy

----------------------------------------------------------------------
----------------------------------------------------------------------
----------------------------------------------------------------------
-- START OF ASSIGNMENT

split : {A : Set} -> {n : Nat} -> Vec A n -> (i : Fin n) -> (Vec A (toNatF i)) & (Vec A (n - toNatF i))
split = {!!}
