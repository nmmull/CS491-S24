module Anon-Functions where

open import Data.List
open import Data.Nat

foo : List ℕ
foo = map (λ { x → x * 10 }) (1 ∷ 2 ∷ 3 ∷ [])

my-pred : ℕ → ℕ
my-pred = λ { zero → zero
            ; (suc n) → n }
