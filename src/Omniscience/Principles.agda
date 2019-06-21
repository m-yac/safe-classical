{-# OPTIONS --safe --without-K #-}
module Omniscience.Principles where

open import Prelude

--  "A principle of omniscience is any principle of classical mathematics
--    that is not valid in constructive mathematics."
--  (https://ncatlab.org/nlab/show/principle+of+omniscience)

-- The principles here and their relationships are drawn from the above page as well as:
--  Separating Fragments of WLEM, LPO, and MP by Matt Hendtlass and Robert Lubarsky
--  (http://math.fau.edu/lubarsky/Separating%20LLPO.pdf)

module Classical where

  -- The Law of Excluded Middle

  LEM-inst : Set ℓ → Set ℓ
  LEM-inst A = A + (¬ A)

  -- The Weak Law of Excluded Middle

  WLEM-inst : Set ℓ → Set ℓ
  WLEM-inst A = (¬¬ A) + (¬ A)

  -- Double Negation Elimination

  DNE-inst : Set ℓ → Set ℓ
  DNE-inst A = ¬¬ A → A

  -- (Note that some of these are inconsistent with MLTT! See ...)
  LEM WLEM DNE : Setω
  LEM  = ∀ {ℓ} (A : Set ℓ) → LEM-inst A
  WLEM = ∀ {ℓ} (A : Set ℓ) → WLEM-inst A
  DNE  = ∀ {ℓ} (A : Set ℓ) → DNE-inst A

-- General versions of Bishop's LPO, WLPO, and MP -- from nLab

module Propl where

  -- The Limited Principle of Omniscience

  LPO-inst : (A : Set ℓ) → (P : A → Set ℓ') → Set (ℓ-max ℓ ℓ')
  LPO-inst A P = (∃[ a ∶ A ] P a) + (∀ (a : A) → ¬ (P a))
               -- equivalent to LEM-inst (∃[ a ∶ A ] P a)

  -- The Weak Limited Principle of Omniscience

  WLPO-inst : (A : Set ℓ) → (P : A → Set ℓ') → Set (ℓ-max ℓ ℓ')
  WLPO-inst A P = (¬ (∀ (a : A) → ¬ (P a))) + (∀ (a : A) → ¬ (P a))
               -- equivalent to WLEM-inst (∃[ a ∶ A ] P a)

  -- Markov's Principle

  MP-inst : (A : Set ℓ) → (P : A → Set ℓ') → Set (ℓ-max ℓ ℓ')
  MP-inst A P = ¬ (∀ (a : A) → ¬ (P a)) → ∃[ a ∶ A ] P a
              -- equivalent to DNE-inst (∃[ a ∶ A ] P a)

  -- (Note that some of these are inconsistent with MLTT! See ...)
  LPO WLPO MP : Set ℓ → Setω
  LPO A  = ∀ {ℓ'} (P : A → Set ℓ') → LPO-inst A P
  WLPO A = ∀ {ℓ'} (P : A → Set ℓ') → WLPO-inst A P
  MP A   = ∀ {ℓ'} (P : A → Set ℓ') → MP-inst A P

-- A more standard statement of Bishop's LPO, WLPO, and MP -- from Hendtlass-Lubarsky

module Bishop where

  -- The Limited Principle of Omniscience

  LPO-inst : (A : Set ℓ) → (P : A → 𝟚) → Set ℓ
  LPO-inst A P = Propl.LPO-inst A (λ a → isTrue (P a))

  -- The Weak Limited Principle of Omniscience

  WLPO-inst : (A : Set ℓ) → (P : A → 𝟚) → Set ℓ
  WLPO-inst A P = Propl.WLPO-inst A (λ a → isTrue (P a))

  -- Markov's Principle

  MP-inst : (A : Set ℓ) → (P : A → 𝟚) → Set ℓ
  MP-inst A P = Propl.MP-inst A (λ a → isTrue (P a))

  -- ...
  LPO WLPO MP : Set ℓ → Set ℓ
  LPO A  = ∀ (P : A → 𝟚) → LPO-inst A P
  WLPO A = ∀ (P : A → 𝟚) → WLPO-inst A P
  MP A   = ∀ (P : A → 𝟚) → MP-inst A P


open Classical public
open Propl     public

