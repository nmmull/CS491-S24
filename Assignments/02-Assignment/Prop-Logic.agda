----------------------------------------------------------------------
-- Propositional Formulas
--
-- In this file, there are a couple problems to fill in based on our
-- discussions of propositional logic.  Note that formulas are defined
-- slightly differently here.  With dependent types we can specify how
-- many variables could appear in a formula, e.g., a `Form 3` is a
-- formula with at most 3 variables.  This allows us to give a simpler
-- notion of a valuation: its just a vector of bools, because we know
-- how many we variables we need to assign need to evaluate any given
-- formula.
----------------------------------------------------------------------

module Prop-Logic where

open import CS400-Lib

PropVar : Nat -> Set
PropVar n = Fin n

data Form n : Set where
  var : PropVar n -> Form n
  not : Form n -> Form n
  and : Form n -> Form n -> Form n
  or : Form n -> Form n -> Form n
  imp : Form n -> Form n -> Form n

----------------------------------------------------------------------
-- English to Formula
--
-- Convert the following english sentences into propositional
-- formulas.  In comments, write the formulas in unicode for practice.
----------------------------------------------------------------------

module English-to-Form where

  g : PropVar 3 -- The garage door is open.
  g = zero

  a : PropVar 3 -- The alarm is set.
  a = suc zero

  l : PropVar 3 -- The light is on.
  l = suc (suc zero)

  -- The garage door is open and the alarm is not set: g ∧ (¬ a)
  example : Form 3
  example = and (var g) (not (var a))

  -- If the garage door is closed then the alarm is set and the light is off: TODO
  problem-1 : Form 3
  problem-1 = {!!}

  -- Either the garage door is open or the alarm is set, but not both: TODO
  problem-2 : Form 3
  problem-2 = {!!}

  -- The light is off whenever the alarm is set: TODO
  problem-3 : Form 3
  problem-3 = {!!}

----------------------------------------------------------------------
-- Evaluation
--
-- Fill in the evaluation function for this new version of formulas.
-- Hint: take a look at the library code for Vectors to get some help
-- on the variable case.
----------------------------------------------------------------------

Val : Nat -> Set
Val n = Vec Bool n

eval : {n : Nat} -> Val n -> Form n -> Bool
eval = {!!}

----------------------------------------------------------------------
-- Tautologies
--
-- Fill in the function below which determines if a formula is a
-- tautology.  You should do this is the naive way: go over all
-- possible valuations and check if they all make the formula true.
-- It may be useful to build the list of all possible valuations of a
-- given length (`allVals` below).
--
-- Then, for all the following formulas, determine whether or not it
-- is a tautology by filling each problem with `yes` or `no v` where v
-- is a valuation that makes it false.
--
-- You don't need to completely understand IsTautology, but you'll
-- find that if you've done everything else correctly, it will be
-- impossible to type check your code unless your answers are correct!
----------------------------------------------------------------------

module Tautology where
  allVals : (n : Nat) -> List (Val n)
  allVals = {!!} -- optional

  isTautology : {n : Nat} -> Form n -> Bool
  isTautology = {!!}

  data IsTautology {n : Nat} (f : Form n) : Set where
    yes : {isTrue (isTautology f)} → IsTautology f
    no : (v : Val n) -> {isFalse (eval v f)} -> IsTautology f

  a : PropVar 2
  a = zero

  b : PropVar 2
  b = suc zero

  example-1 : IsTautology (or (var a) (not (var a))) -- a ∨ (¬ a)
  example-1 = {!!} -- yes    (you need to complete above to fill this in)

  example-2 : IsTautology (var a) -- a
  example-2 = {!!} -- no (false :: false :: [])    (you need to complete above to fill this in)

  problem-1 : IsTautology (imp (var a) (and (var a) (var b))) -- a → (a ∧ b)
  problem-1 = {!!}

  problem-2 : IsTautology (imp (var a) (imp (var b) (var a))) -- a → (b → a)
  problem-2 = {!!}

  problem-3 : IsTautology (imp (var a) (imp (var a) (var b))) -- a → (a → b)
  problem-3 = {!!}
