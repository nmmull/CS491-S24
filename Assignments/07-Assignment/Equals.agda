module Equals where

----------------------------------------------------------------------
-- Assignment 7: Equalities with List
--
-- In this assignment, you will be filling in proofs of equations on
-- lists, all leading to the fact that the tail-recursive reverse
-- function is involutive (i.e., it is its own inverse).  The general
-- approach is to prove the non-tail-recursive version is involutive
-- (this is a bit easier) and then show that the tail-recurive version
-- is equivalent.
--
-- See the code from lecture 15 for outlines on how to write these
-- proofs.  It may help to first write out an argument in English and
-- then think about how to convert into an Agda proof using the tools
-- we saw in lecture.
--
----------------------------------------------------------------------

open import CS400-Lib

rev : {A : Set} -> (l : List A) -> List A
rev [] = []
rev (x :: xs) = rev xs ++ (x :: [])

rev-tr-helper : {A : Set} -> (l acc : List A) -> List A
rev-tr-helper [] acc = acc
rev-tr-helper (x :: xs) acc = rev-tr-helper xs (x :: acc)

rev-tr : {A : Set} -> (l : List A) -> List A
rev-tr l = rev-tr-helper l []

l++[]=l : {A : Set} -> (l : List A) -> l ++ [] =P l
l++[]=l = {!!}

++-assoc : {A : Set} -> (l r m : List A) -> (l ++ r) ++ m =P l ++ (r ++ m)
++-assoc = {!!}

rev-++ : {A : Set} -> (l r : List A) -> rev (l ++ r) =P rev r ++ rev l
rev-++ = {!!}

rev-rev : {A : Set} -> (l : List A) -> rev (rev l) =P l
rev-rev = {!!}

rev-tr-rev-helper : {A : Set} -> (l r : List A) -> rev-tr-helper l r =P rev l ++ r
rev-tr-rev-helper = {!!}

rev-tr-rev : {A : Set} -> (l : List A) -> rev-tr l =P rev l
rev-tr-rev = {!!}

rev-tr-rev-tr : {A : Set} -> (l : List A) -> rev-tr (rev-tr l) =P l
rev-tr-rev-tr = {!!}
