{-

Practice with Agda: Integers

This week you will have a chance to work with Agda as a functional
programming language by building a small interface for integers.

In this exercise, we are imagining that we are building a calculator
for integers in Agda.  This means we have to write an abstract
representation for integers, as well as an abstract representation
for expressions we could type into our calculator.  The part we won't
worry about (for now) is parsing.

We represent an integer as a pair of natural numbers so that (a , b)
represents the integer a - b.  Note that there are multiple ways of
representing an integer : (3, 1) == (2, 0) == (100, 98).

For expressions, we use the neat GADT trick we talked about on Monday:
we /index/ expressions by the type it should evaluate to. This makes
the evaluation function /much/ easier to write (as you will hopefully
see).

As far as what you need to implement, you need to fill in the
definitions of the standard operations, and the evaluation functions.
This just means filling in the holes below.  I recommend trying to use
the interactive programming tools available in Agda.

-}

module Integers where

open import CS400-Lib

-- Integer representation

Int : Set
Int = Nat & Nat

-- A couple helper functions

fromNat : Nat -> Int
fromNat n = (n , 0)

abs : Int -> Nat
abs (a , b) = max (a - b) (b - a)

is-neg : Int -> Bool
is-neg (a , b) = a < b

-- `normalize` converts an int of the form (a , b) to an integer of
-- the form (c , 0) or (0 , c) which represents the same value.

normalize : Int -> Int
normalize = {!!}

-- Standard operations

_+Z_ : Int -> Int -> Int
(a , b) +Z (c , d) = {!!}

_-Z_ : Int -> Int -> Int
x -Z (c , d) = {!!}

_*Z_ : Int -> Int -> Int
(a , b) *Z (c , d) = {!!}

_==Z_ : Int -> Int -> Bool
x ==Z y = {!!}

_<Z_ : Int -> Int -> Bool
x <Z y = {!!}

-- Well-typed expressions: n `Expr a` is an expression which should
-- evaluate to an `a`

data Expr : Set -> Set where
  val : Int -> Expr Int
  add : Expr Int -> Expr Int -> Expr Int
  sub : Expr Int -> Expr Int -> Expr Int
  mul : Expr Int -> Expr Int -> Expr Int
  eq : Expr Int -> Expr Int -> Expr Bool
  lt : Expr Int -> Expr Int -> Expr Bool
  itt : Expr Bool -> Expr Int -> Expr Int -> Expr Int

-- Well-typed evaluation: `eval` evaluates an expression to its specified
-- type. You should return the value in normalized form

eval : {a : Set} -> Expr a -> a
eval = {!!}

basic : Expr Int
basic = -- (10 * 2) * (-5)
  add
    (mul
      (val (fromNat 10))
      (val (fromNat 2)))
    (sub
      (val (fromNat 0))
      (val (fromNat 5)))

less-basic : Expr Int
less-basic = -- if (12 - 13) < (10 + 11) then 2 * 3 else basic
  itt
    (lt
      (sub (val (fromNat 12)) (val (fromNat 13)))
      (add (val (fromNat 10)) (val (fromNat 11))))
    (mul (val (fromNat 2)) (val (fromNat 3)))
    basic

-- type C-c C-n followed by "eval basic" or "eval less-basic" to test
-- your evaluation function
