{-# OPTIONS --safe --without-K #-}
{-
   Contstructive proofs of some classical tautologies involving negation.

   All those marked 'missing' are shown to be non-constructive in Theorems.NonConstructive
-}
module Theorems.Constructive where

open import Prelude

variable
  A B C : Set ℓ
  P Q R : A → Set ℓ'


--------------------
-- Double Negation
--------------------

-- The converse to DNE (see Omniscience.Principles)
DNE-conv : A → ¬¬ A
DNE-conv a ¬a = ¬a a

-- DNE holds for negation
DNE-¬ : ¬¬ (¬ A) → ¬ A
DNE-¬ ¬¬¬a a = ¬¬¬a (DNE-conv a)

-- DNE holds for ⊥
DNE-⊥ : ¬¬ ⊥ → ⊥
DNE-⊥ ¬⊥ = ¬⊥ (λ ())

-- When proving a double negation, one can assume a double negation!
assume-dn : ¬¬ A → (A → B) → ¬¬ B
assume-dn ¬¬a f ¬b = ¬¬a (λ a → ¬b (f a))

assume-dn₂ : ¬¬ A → ¬¬ B → (A → B → C) → ¬¬ C
assume-dn₂ ¬¬a ¬¬b f ¬c = ¬¬a (λ a → ¬¬b (λ b → ¬c (f a b)))


------------------------------
-- Binary sums / Disjunction
------------------------------

-- De Morgan's law for binary sums / disjunction
+-DeM : ¬ (A + B) ⇔ (¬ A) × (¬ B)
fst (fwd +-DeM ¬a+b) a = ¬a+b (inl a)
snd (fwd +-DeM ¬a+b) b = ¬a+b (inr b)
bwd +-DeM (¬a , ¬b) (inl a) = ¬a a
bwd +-DeM (¬a , ¬b) (inr b) = ¬b b

-- Double negation of binary sums / disjunction
bwd-+-DN : (¬¬ A) + (¬¬ B) → ¬¬ (A + B)
bwd-+-DN (inl ¬¬a) = assume-dn ¬¬a (λ a → inl a)
bwd-+-DN (inr ¬¬b) = assume-dn ¬¬b (λ b → inr b)

-- (1) Missing: fwd-+-DN : ¬¬ (A + B) → (¬¬ A) + (¬¬ B)


--------------------------------------
-- Sums / Existential quantification
--------------------------------------

-- De Morgan's law for sums / existential quantification
∃-DeM : ¬ (∃[ a ∶ A ] P a) ⇔ (∀ (a : A) → ¬ (P a))
fwd ∃-DeM ¬∃ a p = ¬∃ (a , p)
bwd ∃-DeM f (a , p) = f a p

-- Double negation of sums / existential quantification
bwd-∃-DN : ∃[ a ∶ A ] ¬¬ (P a) → ¬¬ (∃[ a ∶ A ] P a)
bwd-∃-DN (a , ¬¬p) = assume-dn ¬¬p (λ p → (a , p))

-- (2) Missing: fwd-∃-DN : ¬¬ (∃[ a ∶ A ] P a) → ∃[ a ∶ A ] ¬¬ (P a)


----------------------------------
-- Binary products / Conjunction
----------------------------------

-- De Morgan's law for binary products / conjunction
bwd-×-DeM : (¬ A) + (¬ B) → ¬ (A × B)
bwd-×-DeM (inl ¬a) ab = ¬a (fst ab)
bwd-×-DeM (inr ¬b) ab = ¬b (snd ab)

-- (3) Missing: fwd-×-DeM : ¬ (A × B) → (¬ A) + (¬ B)

-- Double negation of binary products / conjunction
×-DN : ¬¬ (A × B) ⇔ (¬¬ A) × (¬¬ B)
fst (fwd ×-DN ¬¬a×b) = assume-dn ¬¬a×b (λ a×b → (fst a×b))
snd (fwd ×-DN ¬¬a×b) = assume-dn ¬¬a×b (λ a×b → (snd a×b))
bwd ×-DN (¬¬a , ¬¬b) = assume-dn₂ ¬¬a ¬¬b (λ a b → a , b)


----------------------------------------
-- Products / Universal quantification
----------------------------------------

-- De Morgan's law for products / universal quantification
bwd-∀-DeM : ∃[ a ∶ A ] ¬ (P a) → ¬ (∀ (a : A) → P a)
bwd-∀-DeM (a , ¬p) f = ¬p (f a)

-- (4) Missing: fwd-∀-DeM : ¬ (∀ (a : A) → P a) → ∃[ a ∶ A ] ¬ (P a)

-- Double negation of products / universal quantification
fwd-∀-DN : ¬¬ (∀ (a : A) → P a) → (∀ (a : A) → ¬¬ (P a))
fwd-∀-DN ¬¬f a = assume-dn ¬¬f (λ f → f a)

-- (5) Missing: bwd-∀-DN : (∀ (a : A) → ¬¬ (P a)) → ¬¬ (∀ (a : A) → P a)


----------------------------
-- Functions / Implication
----------------------------

-- De Morgan's law for functions / implication
bwd-→-DeM : A × (¬ B) → ¬ (A → B)
bwd-→-DeM (a , ¬b) f = ¬b (f a)

-- (6) Missing: fwd-→-DeM : ¬ (A → B) → A × (¬ B)

-- Double negation of functions / implication
→-DN : ¬¬ (A → B) ⇔ (A → ¬¬ B)
fwd →-DN ¬¬f a = assume-dn ¬¬f (λ f → f a)
bwd →-DN a→¬¬b = -- assume-dn (¬¬DNE-inst B) (λ DNE-B → DNE-B ∘ a→¬¬b)
                 -- (that ^ creates a circular dependency but normalizes to the below)
                 λ ¬f → ¬f (λ a → absurd (a→¬¬b a (λ b → ¬f (λ _ → b))))

-- Law of implication
bwd-impl : (¬ A) + B → (A → B)
bwd-impl (inl ¬a) a = absurd (¬a a)
bwd-impl (inr b ) a = b

-- (7) Missing: fwd-impl : (A → B) → (¬ A) + B

-- Law of contrapositives
fwd-contra : (A → B) → ¬ B → ¬ A
fwd-contra f ¬b a = ¬b (f a)

-- (8) Missing: bwd-contra : (¬ B → ¬ A) → (A → B)

-- Note that using the above, we can get weaker versions of (6) and (8):

-- Weak De Morgan's law for functions / implication
wk-→-DeM : ¬ (A → B) ⇔ (¬¬ A) × (¬ B)
fwd wk-→-DeM = fwd +-DeM ∘ fwd-contra bwd-impl
bwd wk-→-DeM (¬¬a , ¬b) f = ¬¬a (λ a → ¬b (f a))

-- Weak law of contrapositives
wk-contra : (¬ B → ¬ A) ⇔ (A → ¬¬ B)
fwd wk-contra f a ¬b = f ¬b a
bwd wk-contra f ¬b a = f a ¬b

contra-dn : (¬ B → ¬ A) → ¬¬ (A → B)
contra-dn = bwd →-DN ∘  fwd wk-contra
