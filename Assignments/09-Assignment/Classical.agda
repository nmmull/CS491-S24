open import CS400-Lib

----------------------------------------------------------------------
-- Classical Propositions
--
-- Demonstrate that the law of the excluded middle (LEM), double
-- negation elimination (DNE), Peirce's Law (Peirce) and the
-- disjunctive form of implication (ImpDisj) are all equivalent
-- /intuituionistically/ (i.e., in Agda).  We cannot prove any of
-- these four principles on their own in Agda.  You can do this
-- however you please, but I would recommend the following sequence of
-- implications.

LEM : Set1
LEM = (A : Set) -> A \/ Not A

DNE : Set1
DNE = (A : Set) -> Not (Not A) -> A

Peirce : Set1
Peirce = (A B : Set) -> ((A -> B) -> A) -> A

ImpDisj : Set1
ImpDisj = (A B : Set) -> (A -> B) -> Not A \/ B

LEM->DNE : LEM -> DNE
LEM->DNE = {!!}

LEM->Peirce : LEM -> Peirce
LEM->Peirce = {!!}

LEM->ImpDisj : LEM -> ImpDisj
LEM->ImpDisj = {!!}

DNE->Peirce : DNE -> Peirce
DNE->Peirce = {!!}

DNE->ImpDisj : DNE -> ImpDisj
DNE->ImpDisj = {!!}

Peirce->DNE : Peirce -> DNE
Peirce->DNE = {!!}

ImpDisj->LEM : ImpDisj -> LEM
ImpDisj->LEM = {!!}

----------------------------------------------------------------------
-- ¬ ¬ ¬ A → A
--
-- This is something of a gem in intuitionistic logic.  Even though we
-- cannot prove DNE, we /can/ prove that three negations can be
-- reduced to one.

3-to-1NE : (A : Set) -> Not (Not (Not A)) -> Not A
3-to-1NE = {!!}
