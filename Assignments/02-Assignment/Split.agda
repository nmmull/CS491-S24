----------------------------------------------------------------------
-- Splitting Vectors
--
-- In lecture we saw that we could split a vector into two lists.  It
-- would be more satsifying we could split it into two vectors, but
-- this requires knowing the sizes of the vectors after splitting.
-- With dependent types, this is possible.
--
-- Implement a function `split` which given a vector `v` and an index
-- `i`, returns two vectors gotten by splitting `v` at `i`.
--
-- Note the type. It expresses, the length of each part of the split
-- vector.
--
-- Please try to use with-abstraction when you define this function.
----------------------------------------------------------------------

module Split where

open import CS400-Lib

split : {A : Set} -> {n : Nat} -> Vec A n -> (i : Fin n) -> (Vec A (toNat i)) & (Vec A (n - toNat i))
split = {!!}
