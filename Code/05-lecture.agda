module Demo where

open import Data.Nat
open import Data.Vec
open import Data.String
open import Data.Bool

down : (n : ℕ) → Vec ℕ n
down zero = []
down (suc k) = (suc k) ∷ down k

up : (n : ℕ) → Vec ℕ n
up = go 1 where
  go : (start : ℕ) → (n : ℕ) → Vec ℕ n
  go k zero = []
  go k (suc n) = k ∷ go (suc k) n

PropVar : Set
PropVar = String

data Form : Set where
  var : PropVar → Form
  notp : Form → Form  -- named so it doesn't clash with Data.Bool.not
  and : Form → Form → Form
  or : Form → Form → Form
  implies : Form → Form → Form

r : Form
r = var "It's raining"

c : Form
c = var "It's cold"

example : Form
example = implies (and r c) r  -- r ∧ c → r

depth : Form → ℕ
depth (var x) = 0
depth (notp f) = 1 + depth f
depth (and f g) = 1 + (depth f) ⊔ (depth g)  -- \sqcup for ℕ-max function
depth (or f g) = 1 + (depth f) ⊔ (depth g)
depth (implies f g) = 1 + (depth f) ⊔ (depth g)

Valuation : Set
Valuation = PropVar → Bool

eval : Valuation → Form → Bool
eval v (var x) = v x
eval v (notp f) = Data.Bool.not (eval v f)
eval v (and f g) = (eval v f) ∧ (eval v g)
eval v (or f g) = (eval v f) ∨ (eval v g)
eval v (implies f g) = Data.Bool.not (eval v f) ∨ (eval v g)
