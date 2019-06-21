{-# OPTIONS --safe --without-K #-}
module Omniscience.Implications where

open import Prelude
open import Theorems.Constructive
open import Omniscience.Principles

{- The various principles in Omniscience.Principles are related as follows:

        LEM  ⇔  WLEM  ×  DNE    (i.e. LEM → WLEM, LEM → DNE, and WLEM → DNE → LEM)
         ⇕       ⇕       ⇕      (i.e. LEM → LPO, LPO → LEM, WLEM → WLPO, WLPO → WLEM, etc.) 
        LPO  ⇔  WLPO  ×  MP
         ↓       ↓        ↓
       B.LPO ⇔ B.WLPO × B.MP

   Thus, the 'weakest' principles are Bishop.WLPO and Bishop.MP -- this justifies
    the definition of NonConstructive at the bottom of the file, and means that
    all the principles in Omniscience.Principles are therefore NonConstructive.

   Based on:
    Separating Fragments of WLEM, LPO, and MP by Matt Hendtlass and Robert Lubarsky
    (http://math.fau.edu/lubarsky/Separating%20LLPO.pdf)


   The double negation of any LEM-inst also holds, and etc. by the impications above.
-}


-- The first row: LEM ⇔ WLEM × DNE
-- Note that we actually have something stronger: ∀ A → LEM-inst A ⇔ WLEM-inst A × DNE-inst A

LEM→WLEM-inst : ∀ (A : Set ℓ) → LEM-inst A → WLEM-inst A
LEM→WLEM-inst A LEM-A = map-+ DNE-conv id LEM-A

LEM→DNE-inst : ∀ (A : Set ℓ) → LEM-inst A → DNE-inst A
LEM→DNE-inst A (inl a) ¬¬a = a
LEM→DNE-inst A (inr ¬a) ¬¬a = absurd (¬¬a ¬a)

WLEM×DNE→LEM-inst : ∀ (A : Set ℓ) → WLEM-inst A → DNE-inst A → LEM-inst A
WLEM×DNE→LEM-inst A WLEM-A DNE-A = map-+ DNE-A id WLEM-A
                                -- notice the similarity to LEM→WLEM-inst!

LEM→WLEM : LEM → WLEM
LEM→DNE  : LEM → DNE
LEM→WLEM lem A = LEM→WLEM-inst A (lem A)
LEM→DNE  lem A = LEM→DNE-inst A (lem A)
WLEM×DNE→LEM : WLEM → DNE → LEM
WLEM×DNE→LEM wlem dne A = WLEM×DNE→LEM-inst A (wlem A) (dne A)


-- The second row: LEM ⇔ LPO , WLEM ⇔ WLPO , DNE ⇔ MP
-- Note that we actually have stronger relations between LEM-inst & LPO-inst, etc.

LEM→LPO-inst : ∀ (A : Set ℓa) (P : A → Set ℓp) → LEM-inst (∃ A P) → LPO-inst A P
LEM→LPO-inst A P LEM-∃AP = map-+ id (fwd ∃-DeM) LEM-∃AP

LPO→LEM-inst : ∀ (A : Set ℓa) → LPO-inst ⊤ (const A) → LEM-inst A
LPO→LEM-inst A LPO-⊤-A = map-+ snd (λ f → f tt) LPO-⊤-A

WLEM→WLPO-inst : ∀ (A : Set ℓa) (P : A → Set ℓp) → WLEM-inst (∃ A P) → WLPO-inst A P
WLEM→WLPO-inst A P WLEM-∃AP = map-+ (fwd-contra (bwd ∃-DeM)) (fwd ∃-DeM) WLEM-∃AP

WLPO→WLEM-inst : ∀ (A : Set ℓa) → WLPO-inst ⊤ (const A) → WLEM-inst A
WLPO→WLEM-inst A WLPO-⊤-A = map-+ (λ f ¬a → f (const ¬a)) (λ f → f tt) WLPO-⊤-A

DNE→MP-inst : ∀ (A : Set ℓa) (P : A → Set ℓp) → DNE-inst (∃ A P) → MP-inst A P
DNE→MP-inst A P DNE-∃AP = DNE-∃AP ∘ fwd-contra (fwd ∃-DeM)

MP→DNE-inst : ∀ (A : Set ℓa) → MP-inst ⊤ (const A) → DNE-inst A
MP→DNE-inst A MP-⊤-A = snd ∘ MP-⊤-A ∘ (λ ¬¬a f → ¬¬a (f tt))

LEM→LPO   : LEM → ∀ {ℓ} (A : Set ℓ) → LPO A
WLEM→WLPO : WLEM → ∀ {ℓ} (A : Set ℓ) → WLPO A
DNE→MP    : DNE → ∀ {ℓ} (A : Set ℓ) → MP A
LEM→LPO   lem  A P = LEM→LPO-inst A P (lem (∃ A P))
WLEM→WLPO wlem A P = WLEM→WLPO-inst A P (wlem (∃[ a ∶ A ] P a))
DNE→MP    dne  A P = DNE→MP-inst A P (dne (∃[ a ∶ A ] P a))
LPO→LEM   : (∀ {ℓ} (A : Set ℓ) → LPO A) → LEM
WLPO→WLEM : (∀ {ℓ} (A : Set ℓ) → WLPO A) → WLEM
MP→DNE    : (∀ {ℓ} (A : Set ℓ) → MP A) → DNE
LPO→LEM   lpo  A = LPO→LEM-inst A (lpo ⊤ (const A))
WLPO→WLEM wlpo A = WLPO→WLEM-inst A (wlpo ⊤ (const A))
MP→DNE    mp   A = MP→DNE-inst A (mp ⊤ (const A))


-- The third row: LPO ⇔ WLPO × MP
-- Note that we actually have something stronger: ∀ A P → LPO-inst A P ⇔ WLPO-inst A P × MP-inst A P
-- (Notice the similarities with the proofs of the first row!)

LPO→WLPO-inst : ∀ (A : Set ℓ) (P : A → Set ℓ') → LPO-inst A P → WLPO-inst A P
LPO→WLPO-inst A P LPO-A-P = map-+ ((fwd-contra (bwd ∃-DeM)) ∘ DNE-conv) id (LPO-A-P)

LPO→MP-inst : ∀ (A : Set ℓ) (P : A → Set ℓ') → LPO-inst A P → MP-inst A P
LPO→MP-inst A P LPO-A-P ¬f with LPO-A-P
... | inl (a , p) = (a , p)
... | inr f = absurd (¬f f)

WLPO×MP→LPO-inst : ∀ {ℓ} (A : Set ℓ) (P : A → Set ℓ') → WLPO-inst A P → MP-inst A P → LPO-inst A P
WLPO×MP→LPO-inst A P WLPO-A-P MP-A-P = map-+ (MP-A-P) id (WLPO-A-P)

LPO→WLPO : ∀ (A : Set ℓ) → LPO A → WLPO A
LPO→MP   : ∀ (A : Set ℓ) → LPO A → MP A
LPO→WLPO A LPO-A P = LPO→WLPO-inst A P (LPO-A P)
LPO→MP   A LPO-A P = LPO→MP-inst   A P (LPO-A P)
WLPO×MP→LPO : ∀ (A : Set ℓ) → WLPO A → MP A → LPO A
WLPO×MP→LPO A WLPO-A MP-A P = WLPO×MP→LPO-inst A P (WLPO-A P) (MP-A P)


-- The fourth row: LPO → B.LPO , WLPO → B.WLPO , MP → B.MP

LPO→BishopLPO : ∀ {A : Set ℓ} → LPO A → Bishop.LPO A
LPO→BishopLPO LPO-A P = LPO-A (λ a → isTrue (P a))

WLPO→BishopWLPO : ∀ {A : Set ℓ} → WLPO A → Bishop.WLPO A
WLPO→BishopWLPO WLPO-A P = WLPO-A (λ a → isTrue (P a))

MP→BishopMP : ∀ {A : Set ℓ} → MP A → Bishop.MP A
MP→BishopMP MP-A P = MP-A (λ a → isTrue (P a))


-- The fifth row: Bishop.LPO ⇔ Bishop.WLPO × Bishop.MP
-- (Idential to the proofs of the second row)

BishopLPO→BishopWLPO : ∀ {A : Set ℓ} → Bishop.LPO A → Bishop.WLPO A
BishopLPO→BishopWLPO LPO-A P = map-+ ((fwd-contra (bwd ∃-DeM) ∘ DNE-conv)) id (LPO-A P)

BishopLPO→BishopMP : ∀ {A : Set ℓ} → Bishop.LPO A → Bishop.MP A
BishopLPO→BishopMP LPO-A P ¬f with LPO-A P
... | inl (a , p) = (a , p)
... | inr f = absurd (¬f f)

BishopWLPO×MP→BishopLPO : ∀ {A : Set ℓ} → Bishop.WLPO A → Bishop.MP A → Bishop.LPO A
BishopWLPO×MP→BishopLPO WLPO-A MP-A P = map-+ (MP-A P) id (WLPO-A P)


-- The double negation of LEM-inst...

¬¬LEM-inst : ∀ (A : Set ℓ) → ¬¬ (LEM-inst A)
¬¬LEM-inst A ¬LEM = ¬LEM (inr (λ a → ¬LEM (inl a)))

-- ... and its implications

¬¬WLEM-inst : ∀ (A : Set ℓ) → ¬¬ (WLEM-inst A)
¬¬WLEM-inst A = assume-dn (¬¬LEM-inst A) (LEM→WLEM-inst A)

¬¬DNE-inst : ∀ (A : Set ℓ) → ¬¬ (DNE-inst A)
¬¬DNE-inst A = assume-dn (¬¬LEM-inst A) (LEM→DNE-inst A)

¬¬LPO-inst : ∀ (A : Set ℓa) (P : A → Set ℓp) → ¬¬ (LPO-inst A P)
¬¬LPO-inst A P = assume-dn (¬¬LEM-inst (∃ A P)) (LEM→LPO-inst A P)

¬¬WLPO-inst : ∀ (A : Set ℓa) (P : A → Set ℓp) → ¬¬ (WLPO-inst A P)
¬¬WLPO-inst A P = assume-dn (¬¬WLEM-inst (∃ A P)) (WLEM→WLPO-inst A P)

¬¬MP-inst : ∀ (A : Set ℓa) (P : A → Set ℓp) → ¬¬ (MP-inst A P)
¬¬MP-inst A P = assume-dn (¬¬DNE-inst (∃ A P)) (DNE→MP-inst A P)

¬¬BishopLPO-inst : ∀ (A : Set ℓ) (P : A → 𝟚) → ¬¬ (Bishop.LPO-inst A P)
¬¬BishopLPO-inst A P = assume-dn (¬¬LPO-inst A (λ a → isTrue (P a))) id

¬¬BishopWLPO-inst : ∀ (A : Set ℓ) (P : A → 𝟚) → ¬¬ (Bishop.WLPO-inst A P)
¬¬BishopWLPO-inst A P = assume-dn (¬¬WLPO-inst A (λ a → isTrue (P a))) id

¬¬BishopMP-inst : ∀ (A : Set ℓ) (P : A → 𝟚) → ¬¬ (Bishop.MP-inst A P)
¬¬BishopMP-inst A P = assume-dn (¬¬MP-inst A (λ a → isTrue (P a))) id
