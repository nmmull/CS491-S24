module Demo where

open import Data.Bool renaming (not to notb)
open import Data.String

data Form : Set where
  var : String → Form
  not : Form → Form
  and : Form → Form → Form
  or : Form → Form → Form
  implies : Form → Form → Form

Valuation : Set
Valuation = String → Bool

evaluate : Valuation → Form → Bool
evaluate v (var x) = v x
evaluate v (not f) = notb (evaluate v f)
evaluate v (and f g) = (evaluate v f) ∧ (evaluate v f)
evaluate v (or f g) = {!   !}
evaluate v (implies f g) = {!   !}

