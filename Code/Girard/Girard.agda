{-#  OPTIONS --type-in-type #-}
module Girard where

open import CS400-Lib

data ISet : Set where
  mk : (I : Set) -> (I -> ISet) -> ISet

empty : ISet
empty = mk False explode

single : ISet
single = mk Unit (\_ -> empty)

two : ISet
two = mk Bool \{ true → single ; false → empty }

Elem : ISet -> ISet -> Set
Elem x (mk I elems) = [ i ] (elems i =P x)

Curry : Set -> ISet
Curry Y = mk ([ x ] (Elem x x -> Y)) \{ (wit a _) -> a }

Russell : ISet
Russell = mk ([ x ] Not (Elem x x)) \{ (wit a _) -> a }

is-russellian-1 : (a : ISet) -> Elem a Russell -> Not (Elem a a)
is-russellian-1 a (wit (wit a a-not-in-a) refl) = a-not-in-a

is-russellian-2 : (a : ISet) -> Not (Elem a a) -> Elem a Russell
is-russellian-2 a prf = wit (wit a prf) refl

russell-wf : Not (Elem Russell Russell)
russell-wf r-in-r = (is-russellian-1 Russell r-in-r) r-in-r

contradiction : False
contradiction = russell-wf (is-russellian-2 Russell russell-wf)

data CSet A : Set where
  mk : (A -> Set) -> CSet A
