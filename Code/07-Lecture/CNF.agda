module CNF where

open import CS400-Lib

Literal : Set
Literal = Nat & Bool

eqL : Literal -> Literal -> Bool
eqL (x , b) (y , c) = (x == y) && eqb b c

opL : Literal -> Literal -> Bool
opL (x , b) (y , c) = (x == y) && notb (eqb b c)

Clause : Set
Clause = List Literal

trueC : Clause
trueC = (0 , true) :: []

CNF : Set
CNF = List Clause

restrictC : Literal -> Clause -> Clause
restrictC l [] = []
restrictC l (x :: xs) with eqL l x
restrictC l (x :: xs) | true = trueC
restrictC l (x :: xs) | false with opL l x
restrictC l (x :: xs) | false | true = restrictC l xs
restrictC l (x :: xs) | false | false = x :: restrictC l xs

restrict : Literal -> CNF -> CNF
restrict l f = map (restrictC l) f where open Lists

find-var : CNF -> Maybe Nat
find-var [] = Nothing
find-var (((0 , true) :: []) :: xs) = find-var xs
find-var ([] :: xs) = find-var xs
find-var (((x , _) :: x₁) :: xs) = Just x

has-empty : CNF -> Bool
has-empty [] = false
has-empty ([] :: xs) = true
has-empty (_ :: xs) = has-empty xs

{-# TERMINATING #-}
is-sat : CNF -> Bool
is-sat f with find-var f
is-sat f | Nothing = notb (has-empty f)
is-sat f | Just x with is-sat (restrict (x , true) f)
is-sat f | Just x | true = true
is-sat f | Just x | false = is-sat (restrict (x , false) f)
