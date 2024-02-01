
{- Set is the TYPE of types -}

-- \bN Nat
-- \-> arrow

module 04-Lecture where

module Intro where

  open import Data.Nat

  indexType : Set
  indexType = ℕ

  two : ℕ
  two = 2

  id : (a : Set) → a → a
  id _ x = x

  two-again : ℕ
  two-again = id ℕ 2

  poly-id : {a : Set} → a → a
  poly-id x = x

  two-again-again : ℕ
  two-again-again = poly-id 2

module PracticeProblem where

  open import Data.Product
  open import Data.Bool
  open import Data.String

  -- \times \x ==> ×

  TypeWithMsg : Set → Bool → Set
  TypeWithMsg a true = a × String
  TypeWithMsg a false = a

  -- C-c , C-, Check the type of a hole
  -- C-c , C-c Pattern match on an input

  addMessage :
    {a : Set} →
    {b : Set} →
    (a → b) →
    (flag : Bool) →
    a → TypeWithMsg b flag
  addMessage f false x = f x
  addMessage f true x = (f x , "Nathan was here")

module NonEmptyDemo where

  open import Data.List
  open import Data.Nat

  -- \:: ===> ∷

  data NonEmpty : {a : Set} → List a → Set where
    hasFirst :
      {a : Set} →
      {x : a} →
      {xs : List a} →
      NonEmpty (x ∷ xs)

  head_ : {a : Set} → (l : List a) → {NonEmpty l} → a
  head_ (x ∷ xs) = x

  test : ℕ
  test = head_ (1 ∷ 2 ∷ []) {hasFirst}

module VectorDemo where

  open import Data.Vec
  open import Data.List
  open import Data.Nat

  l : List ℕ
  l = 1 ∷ 2 ∷ 3 ∷ []

  v : Vec ℕ _
  v = 1 ∷ 2 ∷ 3 ∷ 4 ∷ []

  -- C-c C-d

  add : {n : ℕ} → Vec ℕ n → Vec ℕ n → Vec ℕ n
  add [] [] = []
  add (x ∷ xs) (y ∷ ys) = (x + y) ∷ add xs ys

module VectorByHand where

  open import Data.Nat

  data List a : Set where
    [] : List a
    _∷_ : a → List a → List a

  data Vec a : ℕ → Set where
    [] : Vec a 0
    _∷_ : {n : ℕ} → a → Vec a n → Vec a (suc n)

  head : {a : Set} → {n : ℕ} → Vec a (suc n) → a
  head (x ∷ _) = x

  data Fin : ℕ → Set where
    zero : {n : ℕ} → Fin (suc n)
    suc : {n : ℕ} → Fin n → Fin (suc n)

  lookup : {a : Set} {n : ℕ} → Vec a n → Fin n → a
  lookup (x ∷ _) zero = x
  lookup (_ ∷ xs) (suc k) = lookup xs k

open import Data.Nat

P : ℕ → Set
P = {!!}
