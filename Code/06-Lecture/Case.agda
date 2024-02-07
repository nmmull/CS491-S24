module case where

open import Data.Nat

case_of_ : {A B : Set} → A → (A → B) → B
case x of f = f x

my-pred : ℕ → ℕ
my-pred n = case n of λ
  { zero → zero
  ; (suc n) → n }