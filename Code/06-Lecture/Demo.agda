module Demo where

open import Data.Bool renaming (not to notb)
open import Data.String

data Form : Set where
  var : String → Form
  not : Form → Form
  and : Form → Form → Form
  or : Form → Form → Form
  implies : Form → Form → Form