module With where

open import Data.Bool
open import Data.Nat
open import Data.List hiding (filter)
open import Data.Vec hiding (filter; split)
open import Data.Fin
open import Data.Product

filter : {A : Set} → (A → Bool) → List A → List A
filter p [] = []
filter p (x ∷ xs) with p x
filter p (x ∷ xs)    | true  = x ∷ filter p xs
filter p (x ∷ xs)    | false = filter p xs

split : {A : Set} → {n : ℕ} → Vec A n → Fin n → List A × List A
split v = {!   !}