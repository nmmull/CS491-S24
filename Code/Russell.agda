{-# OPTIONS --type-in-type #-}
module Russell where

open import CS400-Lib

data ISet : Set where
  mk : (I : Set) -> (I -> ISet) -> ISet

-- ∅
empty : ISet
empty = mk Empty explode

-- {∅}
single : ISet
single = mk Unit (\_ -> empty)

-- {∅, {∅}}
two : ISet
two = mk Bool \{ true → empty ; false → single }

Elem : ISet -> ISet -> Set
Elem x (mk I p) = [ i ] (p i =P x)

Russell : ISet
Russell = mk ([ x ] Not (Elem x x))  \{ (wit x _) → x }

lemma1 : (x : ISet) -> Elem x Russell -> Not (Elem x x)
lemma1 x (wit (wit _ prf) refl) = prf

lemma2 : (x : ISet) -> Not (Elem x x) -> Elem x Russell
lemma2 x x-not-in-x = wit ((wit x x-not-in-x)) refl

lemma3 : Not (Elem Russell Russell)
lemma3 r-in-r = (lemma1 Russell r-in-r) r-in-r

contradiction : False
contradiction = lemma3 (lemma2 Russell lemma3)
