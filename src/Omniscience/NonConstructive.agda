{-# OPTIONS --safe --without-K #-}
module Omniscience.NonConstructive where

open import Prelude
open import Omniscience.Principles
open import Omniscience.Implications

-- For our purposes, a proposition is non-construtive (i.e. has no constructive proof) iff it
--  implies either Bishop's WLPO for ℕ or Bishop's MP for ℕ. It is well accepted that there is
--  no constructive proof for either of these statements in intuitionistic type theory.
-- Note that although there are certainly other propositions which have no constructive proof
--  and are not covered by this definition, as far as I'm aware any other such internal definition
--  will have the same problem, and this one is good enough.

NonConstructive : Setω → Setω
NonConstructive X = X → Bishop.WLPO ℕ + Bishop.MP ℕ

implWLPO : ∀ {X : Setω} → (X → Bishop.WLPO ℕ) → NonConstructive X
implMP   : ∀ {X : Setω} → (X → Bishop.MP   ℕ) → NonConstructive X
implWLPO f x = inl (f x)
implMP   f x = inr (f x)

implNonConstr : ∀ {X Y : Setω} → NonConstructive Y → (X → Y) → NonConstructive X
implNonConstr g f x = g (f x)


-- Using what was shown in Omniscience.Implications, we can show that all the principles
--  in Omniscience.Principles are non-constructive:

-- Bishop

BishopMP-NonConstr : NonConstructive (∀ {ℓ} (A : Set ℓ) → Bishop.MP A)
BishopMP-NonConstr = implMP (λ mp → mp ℕ)

BishopWLPO-NonConstr : NonConstructive (∀ {ℓ} (A : Set ℓ) → Bishop.WLPO A)
BishopWLPO-NonConstr = implWLPO (λ wlpo → wlpo ℕ)

BishopLPO-NonConstr : NonConstructive (∀ {ℓ} (A : Set ℓ) → Bishop.LPO A)
BishopLPO-NonConstr = implNonConstr BishopMP-NonConstr (λ lpo {_} A → BishopLPO→BishopMP (lpo A))

-- Propositional

MP-NonConstr : NonConstructive (∀ {ℓ} (A : Set ℓ) → MP A)
MP-NonConstr = implNonConstr BishopMP-NonConstr (λ mp {_} A → MP→BishopMP (mp A))

WLPO-NonConstr : NonConstructive (∀ {ℓ} (A : Set ℓ) → WLPO A)
WLPO-NonConstr = implNonConstr BishopWLPO-NonConstr (λ wlpo {_} A → WLPO→BishopWLPO (wlpo A))

LPO-NonConstr : NonConstructive (∀ {ℓ} (A : Set ℓ) → LPO A)
LPO-NonConstr = implNonConstr BishopLPO-NonConstr (λ lpo {_} A → LPO→BishopLPO (lpo A))

-- Classical

DNE-NonConstr : NonConstructive DNE
DNE-NonConstr = implNonConstr MP-NonConstr DNE→MP

WLEM-NonConstr : NonConstructive WLEM
WLEM-NonConstr = implNonConstr WLPO-NonConstr WLEM→WLPO

LEM-NonConstr : NonConstructive LEM
LEM-NonConstr = implNonConstr LPO-NonConstr LEM→LPO
