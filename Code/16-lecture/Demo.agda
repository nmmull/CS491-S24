module Demo where

open import CS400-Lib

{- Simple Types

   We beginning by defining types according to the following inductive
   definition:

   + ⊥ is a simple type
   + if 𝐀 and 𝐁 are simple types, the so is 𝐀 ⇒ 𝐁

   We also declare that our function arrow is right associative.

-}

infixr 10 _=>_

data Ty : Set where
  B : Ty
  _=>_ : Ty -> Ty -> Ty

ex-ty : Ty
ex-ty = (B => B) => (B => B)

ex-ty-2 : Ty
ex-ty-2 = B => B => B

{- Contexts

   We will ultimately use De Bruijn indices to represent λ-terms so we
   represent contexts as vectors, where

   t₂ :: t₁ :: []   represents   x₁ : t₁ , x₂ : t₂

   Note that contexts are built BACKWARDS (w.r.t. the syntax we saw in
   lecture) when they are represented as vectors.

-}

Cxt : Nat -> Set
Cxt n = Vec Ty n

{- λ-Terms

   Since contexts are indexed by the number of variable declarations
   they have, it is convenient to index λ-terms by the (maximum)
   number of free variables they have.

   This is also convenient for implementing De Bruijn indices.

   We define λ(i)-terms inductively as follows.

   + The variable 𝐯ⱼ where j ∈ {0, 1,..., i - 1} is a λ(i)-term
   + If 𝐦 is a λ(i + 1)-term then (λ 𝐦) is a λ(i)-term
   + If 𝐦 and 𝐧 are λ(i)-terms, then so is (𝐦 𝐧)

   In the second rule, the variable 𝐯₀ is implicitly bound by the
   λ-abstraction.

-}

data Tm : Nat -> Set where
  v[_] : {n : Nat} -> Fin n -> Tm n
  lam : {n : Nat} -> Tm (suc n) -> Tm n
  app : {n : Nat} -> Tm n -> Tm n -> Tm n

{- Examples -}

-- standard:   λ x . x
-- De Bruijn:  λ 𝐯₀ === λ 0
i : Tm 0
i = lam v[ zero ]

-- standard:   λ x . λ y . x
-- De Bruijn:  λ (λ 𝐯₁) === λ (λ 1)
k : Tm 0
k = lam (lam v[ suc zero ])

-- standard:   λ x . y
-- De Bruijn:  λ 𝐯₁ === λ 1
t : Tm 1
t = lam v[ suc zero ]

-- standard:   λ f . λ x . f x
-- De Bruijn:  λ (λ (𝐯₁ 𝐯₀))
a : Tm 0
a = lam (lam (app v[ suc zero ] v[ zero ]))

{-  Typing Judgments

    Formally speaking, typing judgments are just properties on
    contexts, terms and types (and, in this setting, also the numbers
    indexing those things).  This means typing judgments can be
    represented as INDEXED ADTs.

    We defined typing judgments inductively via the following
    inference rules.

    START:

    ------------------------------- (0 ≤ j ≤ i)
    𝐯₀ : 𝐓₀ ,..., 𝐯ᵢ : 𝐓ᵢ ⊢ 𝐯ⱼ : 𝐓ⱼ

    ABSTRACTION:

    Γ, 𝐯ᵢ : 𝐀 ⊢ 𝐦 : 𝐁
    ------------------
    Γ ⊢ λ 𝐦 : 𝐀 ⇒ 𝐁

    APPLICATION:

    Γ ⊢ 𝐦 : 𝐀 ⇒ 𝐁    Γ ⊢ 𝐧 : 𝐀
    ----------------------------
           Γ ⊢ 𝐦 𝐧 : 𝐁

    We represent these rules in the constructors of the ADT below.
    Note that for verifying that a variable appears in a context, we
    can use our vector lookup function.

-}

infix 5 _|-_is-type_

data _|-_is-type_ : {n : Nat} -> Cxt n -> Tm n -> Ty -> Set where
  start :
    {n : Nat} ->
    {gamma : Cxt n} ->
    {i : Fin n} ->

    --------------------------------------------------
    gamma |- v[ i ] is-type lookupV gamma i

  abst :
    {n : Nat} ->
    {gamma : Cxt n} ->
    {m : Tm (suc n)} ->
    {a b : Ty} ->

    (a :: gamma) |- m is-type b ->
    --------------------------------------------------
    gamma |- (lam m) is-type (a => b)

  app :
    {n : Nat} ->
    {gamma : Cxt n} ->
    {m n : Tm n} ->
    {a b : Ty} ->

    gamma |- m         is-type a => b ->
    gamma |- n         is-type a      ->
    --------------------------------------------------
    gamma |- (app m n) is-type b


{- Examples -}

{- A Derivation of the K-combinator

   (SRT) -----------------------
         𝐯₀ : ⊥ , 𝐯₁ : ⊥ ⊢ 𝐯₀ ⊥
   (ABS) -----------------------
         𝐯₀ : ⊥ ⊢ λ 𝐯₁ : ⊥ ⇒ ⊥
   (ABS) -----------------------
         ⊢ λ (λ 𝐯₁) : ⊥ ⇒ ⊥ ⇒ ⊥

-}

derive-k : [] |- (lam (lam v[ suc zero ])) is-type (B => (B => B) => B)
derive-k = abst (abst start)

-- {- A Derivation of the Constant Function

--    (SRT) ----------------------------------
--          𝐯₀ : ⊥ ⇒ ⊥, 𝐯₁ : ⊥ ⊢ 𝐯₀ : ⊥ ⇒ ⊥
--    (ABS) ----------------------------------
--          𝐯₀ : ⊥ ⇒ ⊥ ⊢ λ 𝐯₁ : ⊥ ⇒ ⊥ ⇒ ⊥

-- -}

derive-t : (B => B :: []) |- lam v[ suc zero ] is-type (B => B => B)
derive-t = abst start

{- Shifting Terms

   One of the trickiest aspects of working with De Bruijn indices is
   that the free variables in a term have to be increased when lambda
   abstractions are performed, or when declarations are added to the
   context.  For example, in the derivation of the constant function,
   the variable in the body of the lambda abstraction had to be
   increased, so as not to be bound implicitly.

   We won't focus too much on this, but it is useful to define a
   general shifting function, one which can increase variables above a
   certain value by a certain amount.  We will primarily use this to
   increase all free variables by 1.

-}

shiftTm : {n : Nat} -> (m p : Nat) -> Tm (m + n) -> Tm (m + (p + n))
shiftTm m p v[ x ] = v[ shiftF m p x ]
shiftTm m p (lam t) = lam (shiftTm (suc m) p t)
shiftTm m p (app f arg) = app (shiftTm m p f) (shiftTm m p arg)

{- Thinning lemma

   As a sanity check, we first prove a simple meta-theoretic lemma
   which says that we can add a declaration anywhere in the context of
   a derivable term. In symbols,

   If

           Γ, Δ ⊢ 𝐦 : 𝐀

   then

           Γ, 𝐯ⱼ : 𝐁, Δ ⊢ 𝐦 : 𝐀

   for any type 𝐁.

-}

thinning-lemma :
  {m n : Nat} ->
  {delta : Cxt m} ->
  {gamma : Cxt n} ->
  {tm : Tm (m + n)} ->
  {a b : Ty} ->

  (delta ++V gamma)        |- tm             is-type a ->
  --------------------------------------------------
  (delta ++V (b :: gamma)) |- shiftTm m 1 tm is-type a

thinning-lemma start = {!!}
thinning-lemma {delta = delta} {gamma = gamma} {a = a} (abst deriv) =
  abst {!thinning-lemma {delta = a :: delta} {gamma = gamma} deriv!}
thinning-lemma (app m-deriv n-deriv) =
  app (thinning-lemma m-deriv) (thinning-lemma n-deriv)

{- Substitution

   The next thing we need to define if we want to prove anything
   interesting about STLC is substitution.  It will be more convenient
   to define SIMULTANEOUS substitution, where we substitute every free
   variable instead of just one.

-}

-- TODO: subst

-- all-vars : {n : Nat} -> Vec (Tm n) n
-- all-vars {zero} = []
-- all-vars {suc n} = v[ zero ] :: mapV (shiftTm 0 1) (all-vars {n})

-- lookupV-all-vars :
--   {n : Nat} ->
--   {f : Fin n} ->
--   lookupV all-vars f =P v[ f ]
-- lookupV-all-vars {f = zero} = refl
-- lookupV-all-vars {f = suc f}
--   rewrite lookupV-mapV {f = shiftTm 0 1} {v = all-vars} {i = f} =
--   =P-cong (shiftTm 0 1) lookupV-all-vars

-- subst1 : {n : Nat} -> Tm n -> Tm (suc n) -> Tm n
-- subst1 {n} nt mt = subst (nt :: all-vars) mt

-- -- Standard:  (x y)[k / x][a / y]     = (k a)
-- -- De Bruijn: (𝐯₁ 𝐯₀)[k / 𝐯₀][a / 𝐯₁] = (k a)
-- subst-test-1 : subst (k :: a :: []) (app v[ suc zero ] v[ zero ]) =P app a k
-- subst-test-1 = refl

-- -- Standard:  (λ z . y)[k / x] = λ z . λ x . λ y . x
-- -- De Bruijn: (λ 𝐯₁)[λ (λ 𝐯₁) / 𝐯₀]   = λ (λ (λ 𝐯₁))
-- subst-test-2 : subst1 k t =P lam (lam (lam v[ suc zero ]))
-- subst-test-2 = refl

-- -- Standard:  (λ z . y)[λ z . y / y] = λ z . λ x . y
-- -- De Bruijn: (λ 𝐯₁)[λ 𝐯₁ / 𝐯₀] = λ (λ 𝐯₂)
-- subst-test-3 : subst (t :: []) t =P lam (lam v[ suc (suc zero) ])
-- subst-test-3 = refl

{- Substitution Lemma

   The main meta-theoretic lemma that we want to prove is the
   (simultaneous) substitution lemma.  Many important results follow
   directly from this one.  In words, it says that if we can
   substitute every variable in a context with typable terms, then
   the resulting term is still typable.  In symbols.

   If
           𝐯₀ : 𝐓₀ ,..., 𝐯ᵢ : 𝐓ᵢ ⊢ 𝐦 : 𝐀

   and

           Γ ⊢ 𝐧₀ : 𝐓₀ ,..., Γ ⊢ 𝐧ᵢ : 𝐓ᵢ

   then

           Γ ⊢ 𝐦[𝐧₀ / 𝐯₀]...[𝐧ᵢ / 𝐯ᵢ] : 𝐀

-}

-- TODO: subst-lemma

{- (Single) Substitution Lemma

   We can then specialize the above lemma to the standard substitution
   lemma. In symbols:

   If

           Γ, x : a ⊢ m : b

   and

           Γ ⊢ n : a

   then

           Γ ⊢ m[n / x] : a

-}

-- TODO: subst1-lemma

{- β-Reduction

   Our final aim is to prove the type preservation of STLC.  For this we
   need to define β-reduction.

   Recall that m ⟶β n is defined as a RELATION inductively as follows:

   (1)  (λ x . m) n ⟶β m[ n / x ]                        (β-reduction)

   (2)  m ⟶β n    implies    (λ x . m) ⟶β (λ x . m)    (λ-red)

   (3)  m ⟶β n    implies    m p       ⟶β n p          (app₁-red)

   (4)  m ⟶β n    implies    p m       ⟶β p n          (app₂-red)

-}

-- todo: Red

{- Type Preservation

   This lemma says that β-reduction does not change the type of a
   term.  In symbols:

   If

           m ⟶β n

   and

           Γ ⊢ m : a

   then

           Γ ⊢ n : a

   This is proved by induction on the beta-reduction relation (!)  The
   only "tricky" case is the β-red case, but it is very simple once we
   have our substitution lemma.

-}

-- TODO: pres
