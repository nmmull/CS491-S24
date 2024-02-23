module Empty where

open import CS400-Lib

IsEmpty : Set -> Set
IsEmpty A = A -> Empty

empty-is-empty : IsEmpty Empty
empty-is-empty found-one = found-one

data NotWell : Set where
  cannot : NotWell -> NotWell

emp : IsEmpty NotWell
emp (cannot but-I-did) = emp but-I-did

isEmpty-Prod :
  {A : Set} ->
  {B : Set} ->
  IsEmpty A ->
  IsEmpty B ->
  IsEmpty (Either A B)
isEmpty-Prod f g (left x) = f x
isEmpty-Prod f g (right x) = g x

explode : {A : Set} -> Empty -> A
explode ()

NonEmpty : {A : Set} -> List A -> Set
NonEmpty [] = Empty
NonEmpty {A} (x :: l) = Unit

head : {A : Set} -> (l : List A) -> {NonEmpty l} -> A
head (x :: xs) = x

x : Nat
x = head (1 :: [])

problem : {A : Set} -> A -> IsEmpty (IsEmpty A)
problem a f = f a

