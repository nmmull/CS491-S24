module Combine where

open import Data.List
open import Data.Nat
open import Data.Bool
open import Data.Sum
open import Function.Base

data Either a b : Set where
  left : a → Either a b
  right : b → Either a b

combine : {a b : Set} → List (Either a b) → List (Either (List a) (List b))
combine = {!   !}

test : List (Either ℕ Bool)
test = left 0 ∷ left 1 ∷ right true ∷ right false ∷ left 2 ∷ []