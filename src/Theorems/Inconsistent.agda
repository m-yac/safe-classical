{-# OPTIONS --safe --cubical #-}
module Theorems.Inconsistent where

open import Prelude
open import Theorems.Constructive

open import Omniscience.Principles
open import Omniscience.Implications
open import Omniscience.NonConstructive


-- In HoTT DNE is rejected!

¬DNE : ¬ (∀ (A : Set ℓ) → DNE-inst A)
¬DNE = {!!}


-- ...and as a result, so are (6) and (5)

¬-bwd-∀-DN : ( ∀ {ℓa} {A : Set ℓa} {P : A → Set ℓp} → (∀ (a : A) → ¬¬ (P a)) → ¬¬ (∀ (a : A) → P a) ) → ⊥
¬-bwd-∀-DN bwd-∀-DN = bwd-∀-DN (λ A → ¬¬DNE-inst A) ¬DNE

¬-fwd-∀-DeM : ( ∀ {ℓa} {A : Set ℓa} {P : A → Set ℓp} → ¬ (∀ (a : A) → P a) → ∃[ a ∶ A ] ¬ (P a) ) → ⊥
¬-fwd-∀-DeM fwd-∀-DeM = ¬-bwd-∀-DN (fwd-contra fwd-∀-DeM ∘ bwd ∃-DeM)
