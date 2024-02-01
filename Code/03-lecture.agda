module 03-Lecture where

module Basics where

  -- example of an inductive data type
  data Nat : Set where
    zero : Nat
    suc : Nat -> Nat

  -- example of using constructors
  three : Nat
  three = suc (suc (suc zero))

  -- another example of an inductive data type
  data Bool : Set where
    true : Bool
    false : Bool

  -- example of a polymorphic function using implicits
  id : {a : Set} → a → a
  id x = x

  -- polymorphic function instantiation
  id-Nat : Nat → Nat
  id-Nat = id

  -- polymorphic function instantiation
  id-Bool : Bool → Bool
  id-Bool = id

  -- (parametrized) polymorphic data type
  data List a : Set where
    nil : List a
    cons : a → List a → List a

  -- indexed data type
  -- data Listt : Set → Set where
  --   nil : {a : Set} → Listt a
  --   cons : {a : Set} → a → Listt a → Listt a
  --   cons-Nat : Nat → Listt Nat → Listt Nat

  -- example of infix operator (for a constructor)
  data Pair a b : Set where
   _,_ : a → b → Pair a b

  -- infix operators must have spaces around them
  test : Pair Nat Nat
  test = (zero , zero)

  -- we cannot write infinite loops, all functions are total
  -- bar : Nat → Nat
  -- bar x = bar x

open import Data.Nat
open import Data.Bool

module Non-Well-Typed-Expressions where
  data Expr : Set where
    NumExp : ℕ → Expr
    BoolExp : Bool → Expr
    AddExp : Expr → Expr → Expr
    iteExp : Expr → Expr → Expr → Expr

  -- if true then 1 else 0 + 1
  test : Expr
  test = iteExp (BoolExp true) (NumExp 0) (AddExp (NumExp 0) (NumExp 1))

  -- eval : Expr → ???

module Well-Typed-Expressions where
  data Expr : Set → Set where
    NumExp : ℕ → Expr ℕ
    BoolExp : Bool → Expr Bool
    AddExp : Expr ℕ → Expr ℕ → Expr ℕ
    iteExp : {a : Set} → Expr Bool → Expr a → Expr a → Expr a

  eval : {a : Set} → Expr a → a
  eval (NumExp n) = n
  eval (BoolExp b) = b
  eval (AddExp x y) = eval x + eval y
  eval (iteExp b x y) = if eval b then eval x else eval y
