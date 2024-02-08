module Combine where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.Sum
open import Function.Base

foo : ℕ ⊎ Bool
foo = inj₂ true

data Either a b : Set where
  left : a → Either a b
  right : b → Either a b

combine : {a b : Set} → List (Either a b) → List (Either (List a) (List b))
combine [] = []
combine (x ∷ xs) with combine xs
combine (left x ∷ xs) | left y ∷ ys = left (x ∷ y) ∷ ys
combine (right x ∷ xs) | right y ∷ ys = right (x ∷ y) ∷ ys
combine (left x ∷ xs) | l = left (x ∷ []) ∷ l
combine (right x ∷ xs) | l = right (x ∷ []) ∷ l

test : List (Either ℕ Bool)
test = left 0 ∷ left 1 ∷ right true ∷ right false ∷ left 2 ∷ []