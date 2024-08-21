module Curry-2 where

open import CS400-Lib

{-# NO_POSITIVITY_CHECK #-}
data Rec A : Set where
  into : (Rec A -> A) -> Rec A

out : {A : Set} -> Rec A -> (Rec A -> A)
out (into f) = f

y : {A : Set} -> (A -> A) -> A
y {A} f = (\x -> f (out x x)) (into (\x -> f (out x x)))

test : {A : Set} -> A
test = (\x -> (out x x)) (into (\x -> out x x))

contradiction : False
contradiction = y {False} (\x -> x)
