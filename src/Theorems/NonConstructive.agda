{-# OPTIONS --safe --without-K #-}
module Theorems.NonConstructive where

open import Prelude
open import Theorems.Constructive

open import Omniscience.Principles
open import Omniscience.Implications
open import Omniscience.NonConstructive


-- (1) Non-constructive: fwd-+-DN : ¬¬ (A + B) → (¬¬ A) + (¬¬ B)

¬¬-fwd-+-DN : ¬¬ ( ¬¬ (A + B) → (¬¬ A) + (¬¬ B) )
¬¬-fwd-+-DN {A = A} {B = B} = assume-dn (¬¬DNE-inst (A + B))
                                        (λ DNE-A+B → map-+ DNE-conv DNE-conv ∘ DNE-A+B)

fwd-+-DN-NonConstr : NonConstructive ( ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → ¬¬ (A + B) → (¬¬ A) + (¬¬ B) )
fwd-+-DN-NonConstr = implNonConstr WLEM-NonConstr
                                   (λ fwd-+-DN A → map-+ id DNE-¬ (fwd-+-DN (¬¬LEM-inst A)))


-- (2) Non-constructive: fwd-∃-DN : ¬¬ (∃[ a ∶ A ] P a) → ∃[ a ∶ A ] ¬¬ (P a)

¬¬-fwd-∃-DN : ¬¬ ( ¬¬ (∃[ a ∶ A ] P a) → ∃[ a ∶ A ] ¬¬ (P a) )
¬¬-fwd-∃-DN {A = A} {P = P} = assume-dn (¬¬DNE-inst (∃ A P))
                                        (λ DNE-∃AP → map-∃ DNE-conv ∘ DNE-∃AP)

fwd-∃-DN-NonConstr : NonConstructive ( ∀ {ℓa ℓp} {A : Set ℓa} {P : A → Set ℓp}
                                       → ¬¬ (∃[ a ∶ A ] P a) → ∃[ a ∶ A ] ¬¬ (P a) )
fwd-∃-DN-NonConstr = implNonConstr fwd-+-DN-NonConstr
                                   (λ fwd-∃-DN ¬¬a+b → pair (fwd-∃-DN (assume-dn ¬¬a+b unpair)))
                                   
  where case-𝟚-Set : Set ℓa → Set ℓb → 𝟚 → Set (ℓ-max ℓa ℓb)
        case-𝟚-Set {ℓb = ℓb} A B false = Lift ℓb A
        case-𝟚-Set {ℓa = ℓa} A B true  = Lift ℓa B

        pair : ∀ {A : Set ℓa} {B : Set ℓb} → Σ[ b ∶ 𝟚 ] (¬¬ (case-𝟚-Set A B b)) → (¬¬ A) + (¬¬ B)
        pair (false , ¬¬la) = inl (λ ¬a → ¬¬la (λ { (lift a) → ¬a a }))
        pair (true  , ¬¬lb) = inr (λ ¬b → ¬¬lb (λ { (lift b) → ¬b b }))

        unpair : ∀ {A : Set ℓa} {B : Set ℓb} → A + B → Σ[ b ∶ 𝟚 ] (case-𝟚-Set A B b) 
        unpair (inl a) = (false , lift a)
        unpair (inr b) = (true  , lift b)


-- (3) Non-constructive: fwd-×-DeM : ¬ (A × B) → (¬ A) + (¬ B)

¬¬-fwd-×-DeM : ¬¬ ( ¬ (A × B) → (¬ A) + (¬ B) )
¬¬-fwd-×-DeM = contra-dn (bwd ×-DN ∘ fwd +-DeM)

fwd-×-DeM-NonConstr : NonConstructive ( ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → ¬ (A × B) → (¬ A) + (¬ B) )
fwd-×-DeM-NonConstr = implNonConstr fwd-+-DN-NonConstr
                                    (λ fwd-×-DeM ¬¬a+b → fwd-×-DeM (fwd-contra (bwd +-DeM) ¬¬a+b))


-- (4) Inconsistent: fwd-∀-DeM : ¬ (∀ (a : A) → P a) → ∃[ a ∶ A ] ¬ (P a)

-- See Theorems.Inconsistent for a proof of the negation of this claim! (in an extension of agda)

fwd-∀-DeM-NonConstr : NonConstructive ( ∀ {ℓa ℓp} {A : Set ℓa} {P : A → Set ℓp}
                                        → ¬ (∀ (a : A) → P a) → ∃[ a ∶ A ] ¬ (P a) )
fwd-∀-DeM-NonConstr = implNonConstr DNE-NonConstr
                                    (λ fwd-∀-DeM A ¬¬a → fst (fwd-∀-DeM ¬¬a))


-- (5) Inconsistent: bwd-∀-DN : (∀ (a : A) → ¬¬ (P a)) → ¬¬ (∀ (a : A) → P a)

-- See Theorems.Inconsistent for a proof of the negation of this claim! (in an extension of agda)
-- I am unsure as to whether non-constructivity can be shown without the aforementioned proof.

-- fwd-∀-DN-NonConstr : NonConstructive ( ∀ {ℓa ℓp} {A : Set ℓa} {P : A → Set ℓp}
--                                        → ∀ (a : A) → ¬¬ (P a) → ¬¬ (∀ (a : A) → P a) )
-- fwd-∀-DN-NonConstr = implNonConstr {!!} {!!}


-- (6) Non-constructive: fwd-→-DeM : ¬ (A → B) → A × (¬ B)

¬¬-fwd-→-DeM : ¬¬ ( ¬ (A → B) → A × (¬ B) )
¬¬-fwd-→-DeM {A = A} {B = B}
  = contra-dn (λ ¬p → assume-dn₂ ¬¬-fwd-×-DeM (¬¬DNE-inst B)
                                 (λ fwd-×-DeM DNE-B → bwd-impl (map-+ id DNE-B (fwd-×-DeM ¬p))))

fwd-→-DeM-NonConstr : NonConstructive ( ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → ¬ (A → B) → A × (¬ B) )
fwd-→-DeM-NonConstr = implNonConstr DNE-NonConstr
                                    (λ fwd-→-DeM A ¬¬a → fst (fwd-→-DeM ¬¬a))


-- (7) Non-constructive: fwd-impl : (A → B) → (¬ A) + B

¬¬-fwd-impl : ¬¬ ( (A → B) → (¬ A) + B )
¬¬-fwd-impl {A = A} {B = B} = assume-dn (¬¬LEM-inst A)
                                        (λ LEM-A f → map-+ id f (sym-+ LEM-A))

fwd-impl-NonConstr : NonConstructive ( ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → (A → B) → (¬ A) + B )
fwd-impl-NonConstr = implNonConstr LEM-NonConstr
                                   (λ fwd-impl A → sym-+ (fwd-impl id))


-- (8) Non-constructive: bwd-contra : (¬ B → ¬ A) → (A → B)

¬¬-bwd-contra : ¬¬ ( (¬ B → ¬ A) → (A → B) )
¬¬-bwd-contra = bwd →-DN contra-dn

bwd-contra-NonConstr : NonConstructive ( ∀ {ℓa ℓb} {A : Set ℓa} {B : Set ℓb} → (¬ B → ¬ A) → (A → B) )
bwd-contra-NonConstr = implNonConstr DNE-NonConstr
                                     (λ bwd-contra A → bwd-contra DNE-conv)
