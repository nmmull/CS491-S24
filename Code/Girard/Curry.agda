module Curry where

open import CS400-Lib

{-# NO_POSITIVITY_CHECK #-}
data SSet : Set1 where
  mk : (SSet -> Set) -> SSet

Elem : SSet -> (SSet -> Set)
Elem x (mk p) = p x

empty : SSet
empty = mk \_ -> False

Curry : Set -> SSet
Curry Y = mk (\ss -> Elem ss ss -> Y)

Russell : SSet
Russell = Curry False

not-in : Not (Elem Russell Russell)
not-in r-in-r = r-in-r r-in-r

contradiction : False
contradiction = not-in not-in
