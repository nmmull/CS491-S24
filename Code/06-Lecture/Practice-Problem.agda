module Practice-Problem where

open import Data.Bool renaming (not to notb)
open import Data.String

data Form : Set where
  var : String → Form
  not : Form → Form
  and : Form → Form → Form
  or : Form → Form → Form
  implies : Form → Form → Form

-- replaces "a → b" with "¬a ∨ b" recursively throughout a formula
replace-implies : Form → Form
replace-implies (var x) = (var x)
replace-implies (not f) = not (replace-implies f)        -- e.g., ¬ (A → B)
replace-implies (and f g) = and (replace-implies f) (replace-implies g)
replace-implies (or f g) = or (replace-implies f) (replace-implies g)
replace-implies (implies f g) = or (not (replace-implies f)) (replace-implies g)

example : Form  {-   P → (Q → W)   -}
example = implies (var "P") (implies (var "Q") (var "W"))

