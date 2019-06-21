{-# OPTIONS --safe --without-K #-}
module Prelude where


-- Universe levels

open import Agda.Primitive public
  using    ( Level ; Setω )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max )

variable ℓ ℓ' ℓa ℓb ℓc ℓd ℓp ℓq : Level

record Lift ℓ {ℓa} (A : Set ℓa) : Set (ℓ-max ℓ ℓa) where
  constructor lift
  field lower : A
open Lift public

record Liftω {ℓa} (A : Set ℓa) : Setω where
  constructor liftω
  field lowerω : A
open Liftω public


-- The empty type and negation

data ⊥ : Set₀ where

absurd : ∀ {X : Set ℓ} → ⊥ → X
absurd ()

¬_ : Set ℓ → Set ℓ
¬ A = A → ⊥

¬¬ : Set ℓ → Set ℓ
¬¬ A = ¬ (¬ A)


-- The unit, boolean, and natural number types

open import Agda.Builtin.Unit public using (⊤; tt)
open import Agda.Builtin.Bool public renaming (Bool to 𝟚) using (true; false)
open import Agda.Builtin.Nat  public renaming (Nat to ℕ) using (zero; suc) renaming (_<_ to _<?_)

isTrue : 𝟚 → Set₀
isTrue true  = ⊤
isTrue false = ⊥

isFalse : 𝟚 → Set₀
isFalse true  = ⊥
isFalse false = ⊤


-- Binary sums / Disjunction

data _+_ (A : Set ℓa) (B : Set ℓb) : Set (ℓ-max ℓa ℓb) where
  inl : A → A + B
  inr : B → A + B

map-+ : ∀ {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} {D : Set ℓd} → (A → C) → (B → D) → A + B → C + D
map-+ f g (inl a) = inl (f a)
map-+ f g (inr b) = inr (g b)

sym-+ : ∀ {A : Set ℓa} {B : Set ℓb} → A + B → B + A
sym-+ (inl a) = inr a
sym-+ (inr b) = inl b


-- Sums / Existential quantification

record Σ (A : Set ℓa) (P : A → Set ℓp) : Set (ℓ-max ℓa ℓp) where
  constructor _,_
  field fst : A
        snd : P fst
open Σ public

-- NB: That colon is '\:' not ':'!
syntax Σ A (λ a → B) = Σ[ a ∶ A ] B

∃ : (A : Set ℓa) (P : A → Set ℓp) → Set (ℓ-max ℓa ℓp)
∃ = Σ

-- NB: That colon is '\:' not ':'!
syntax ∃ A (λ a → B) = ∃[ a ∶ A ] B

map-∃ : ∀ {A : Set ℓa} {P : A → Set ℓp} {Q : A → Set ℓq} → (∀ {a} → P a → Q a) → ∃ A P → ∃ A Q
map-∃ f (a , p) = (a , f p)


-- Binary products / Conjuction

_×_ : Set ℓa → Set ℓb → Set (ℓ-max ℓa ℓb)
A × B = Σ[ _ ∶ A ] B

map-× : ∀ {A : Set ℓa} {B : Set ℓb} {C : Set ℓc} {D : Set ℓd} → (A → C) → (B → D) → A × B → C × D
map-× f g (a , b) = (f a , g b)

sym-× : ∀ {A : Set ℓa} {B : Set ℓb} → A × B → B × A
sym-× (a , b) = (b , a)


-- Products / Universal quantification

Π : (A : Set ℓa) (P : A → Set ℓp) → Set (ℓ-max ℓa ℓp)
Π A P = ∀ (a : A) → P a

-- NB: That colon is '\:' not ':'!
syntax Π A (λ a → B) = Π[ a ∶ A ] B

_∘_ : ∀ {A : Set ℓa} {B : A → Set ℓb} {C : (a : A) → B a → Set ℓc}
        (g : ∀ {a : A} (b : B a) → C a b) (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) x = g (f x)
infixr 9 _∘_


-- Functions / Implication

record _⇔_ (A : Set ℓa) (B : Set ℓb) : Set (ℓ-max ℓa ℓb) where
  field fwd : A → B
        bwd : B → A
open _⇔_ public
infix 18 _⇔_

id : ∀ {A : Set ℓ} → A → A
id x = x

const : ∀ {A : Set ℓ} {B : Set ℓ'} → B → A → B
const b a = b
