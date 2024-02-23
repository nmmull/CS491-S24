open import CS400-Lib

{-

In this assignment, you will be filling in an Agda definition of
resolution proofs.  We'll use the "IsTrue" trick that we talked about
in class to design resolution proofs as ADTs.

REMINDER: Please pull down the most recent changes to CS400-Lib, or
use the included copy of the file by changing the above line to:

open import CS400-Lib-Copy

-}

-- Variables are represented as natural numbers
Var : Set
Var = Nat

-- Literals are represented as a variable together with a Boolean
-- value, where x (or x¹) is represented as `(x , true)` and ¬x (or x⁰)
-- is represented as `(x , false)`
Lit : Set
Lit = Var & Bool

-- Clauses are represented as lists of literals, but treated as sets,
-- i.e., we ignore duplication of literals.  If both `(x , true)` and
-- `(x , false)` appear in a clause, then first one takes precedence.
-- So, for example,
--
-- (0 , true) :: (1 , true) :: (1 , true) :: (0 , false) :: []
--
-- represents the clause x₀ ∨ x₁.
Cls : Set
Cls = List Lit

-- CNF formulas is represented as a lists of clauses, also treated as
-- sets.
CNF : Set
CNF = List Cls

-- These are Boolean comparison functions for literals and clauses
eq-lit : Lit -> Lit -> Bool
eq-lit (x , b) (y , c) = (x == y) && (b ==b c)

eq-cls : Cls -> Cls -> Bool
eq-cls [] [] = true
eq-cls (_ :: _) [] = false
eq-cls [] (_ :: _) = false
eq-cls (x :: xs) (y :: ys) = eq-lit x y && eq-cls xs ys

-- TODO: Fill in the following function which determines if a variable x
-- appears in a clause, either as x⁰ or x¹.
has-var : Var -> Cls -> Bool
has-var = {!!}

-- TODO: Fill in the following function which determines if a given
-- literal appears in a clause.
has-lit : Lit -> Cls -> Bool
has-lit = {!!}

-- TODO: Fill in the following function which determines if a given
-- clause appears in a CNF formula.
has-cls : Cls -> CNF -> Bool
has-cls = {!!}

-- TODO: Fill in the following function which, given a variable x and
-- a clause c, returns c with any occurrence of x⁰ and x¹ removed.
remove-var : Var -> Cls -> Cls
remove-var = {!!}

-- TODO: Fill in the following function which resolves two clauses `c`
-- and `d` on a given variable `x`.  Note that in order to use the
-- function, x⁰ must appear in `c` and x¹ must appear in `d`.
resolve :
  (x : Var) ->
  (c : Cls) ->
  (d : Cls) ->
  {IsTrue (has-lit (x , false) c)} ->
  {IsTrue (has-lit (x , true) d)} ->
  Cls
resolve x c d = remove-var x (c ++ d)

-- You can use C-c C-n to verify that `check` is the empty clause.
check : Cls
check = {!!} -- resolve 0 ((0 , false) :: []) ((0 , true) :: [])

-- `Res` is an algebraic data type for representing resolution proofs.
-- A value of type `Res ϕ C` represents a derivation tree of ϕ ⊢ C.
data Res : CNF -> Cls -> Set where

  -- The `axiom` constructor represents the rule
  --
  --   ------------- (C ∈ ϕ)
  --       ϕ ⊢ C
  --
  -- It requires that `c` appears in the formula `f` in order to be
  -- constructed.  If `c` appears in `f` then we can write `axiom c`
  -- and it can be given the type `Res f c`.
  axiom : {f : CNF} -> (c : Cls) -> {IsTrue (has-cls c f)} -> Res f c

  -- The `res` constructor represents the rule
  --
  --   ϕ ⊢ C ∨ x⁰    ϕ ⊢ D ∨ x¹
  --   ------------------------
  --         ϕ ⊢ C ∨ D
  --
  -- It requires that `(x , false)` appears in `c` and `(x, true)`
  -- appears in `d` to be constructed.  If these conditions are met
  -- then we can write `res x left-tree right-tree`, where `left-tree`
  -- is a derivation of `c` and `right-tree` is a derivation of `d`
  -- and it can be given type `Res (resolve x c d)`
  res :
    {f : CNF} ->
    {c : Cls} ->
    {d : Cls} ->
    (x : Var) ->
    {l : IsTrue (has-lit (x , false) c)} ->
    {r : IsTrue (has-lit (x , true) d)} ->
    Res f c ->
    Res f d ->
    Res f (resolve x c d {l} {r})

-- A simple function for building a positive literal
x : Var -> Lit
x i = (i , true)

-- A simple function for building a negative literal
nx : Var -> Lit
nx i = (i , false)

-- ϕ is an instance of the formula we considered in class:
--   x₀ ∧ (¬x₀ ∨ x₁) ∧ (¬x₁ ∨ x₂) ∧ (¬x₂ ∨ x₃) ∧ ¬x₃
phi : CNF
phi =
  (x 0  :: [])        ::
  (nx 0 :: x 1 :: []) ::
  (nx 1 :: x 2 :: []) ::
  (nx 2 :: x 3 :: []) ::
  (nx 3 :: [])        ::
  []

-- We can prove ϕ ⊢ x₁ by building the proof
--
--   ------------    ------
--   ϕ ⊢ ¬x₀ ∨ x₁    ϕ ⊢ x₀
--   ----------------------
--          ϕ ⊢ x₁
step1 : Res phi (x 1 :: [])
step1 = {!!} -- res 0 (axiom ((nx 0) :: x 1 :: [])) (axiom (x 0 :: []))

-- TODO: Fill in the next step by proving ϕ ⊢ x₂ (hint: use `step1`)
step2 : Res phi (x 2 :: [])
step2 = {!!}

-- TODO: Fill in the next step
step3 : Res phi (x 3 :: [])
step3 = {!!}

-- TODO: Fill in the last step, which shows that ϕ is unsatisfiable
ref : Res phi []
ref = {!!}
