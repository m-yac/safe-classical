{-# OPTIONS --safe --without-K #-}
module Classical where

open import Agda.Primitive public
  using    ( Level ; Setω )
  renaming ( lzero to ℓ-zero
           ; lsuc  to ℓ-suc
           ; _⊔_   to ℓ-max )

variable
  ℓ ℓ' ℓ'' : Level
  P Q R S : Set ℓ
  


-----------
-- Basics
-----------

-- the empty type

data ⊥ : Set₀ where

¬_ : Set ℓ → Set ℓ
¬ A = A → ⊥


¬¬ : Set ℓ → Set ℓ
¬¬ A = ¬ (¬ A)

absurd : ∀ {X : Set ℓ} → ⊥ → X
absurd ()

-- sums and products of types

data _+_ (P : Set ℓ) (Q : Set ℓ') : Set (ℓ-max ℓ ℓ') where
  inl : P → P + Q
  inr : Q → P + Q

record Σ (P : Set ℓ) (Q : P → Set ℓ') : Set (ℓ-max ℓ ℓ') where
  constructor _,_
  field fst : P
        snd : Q fst
open Σ

-- NB: That colon is '\:' not ':'!
syntax Σ P (λ p → Q) = Σ[ p ∶ P ] Q

_×_ : Set ℓ → Set ℓ' → Set (ℓ-max ℓ ℓ')
P × Q = Σ[ _ ∶ P ] Q

-- function types

_∘_ : ∀ {A : Set ℓ} {B : A → Set ℓ'} {C : (a : A) → B a → Set ℓ''}
        (g : ∀ {a : A} (b : B a) → C a b) (f : (a : A) → B a) → (a : A) → C a (f a)
(g ∘ f) x = g (f x)



----------------------------------
-- Constructive Classical Lemmas
----------------------------------

contra-fwd : (P → Q) → ¬ Q → ¬ P
contra-fwd f nq p = nq (f p)

contra-bwd : Set ℓ → Set ℓ' → Set (ℓ-max ℓ ℓ')
contra-bwd Q P = (¬ Q → ¬ P) → (P → Q)


+-DeM-fwd : ¬ (P + Q) → (¬ P) × (¬ Q)
fst (+-DeM-fwd n+) p = n+ (inl p)
snd (+-DeM-fwd n+) q = n+ (inr q)

+-DeM-bwd : (¬ P) × (¬ Q) → ¬ (P + Q)
+-DeM-bwd (nP , nQ) (inl p) = nP p
+-DeM-bwd (nP , nQ) (inr q) = nQ q


×-DeM-fwd : Set ℓ → Set ℓ' → Set (ℓ-max ℓ ℓ')
×-DeM-fwd P Q = ¬ (P × Q) → (¬ P) + (¬ Q)

×-DeM-bwd : Set ℓ → Set ℓ' → Set (ℓ-max ℓ ℓ')
×-DeM-bwd P Q = (¬ P) + (¬ Q) → ¬ (P × Q)


→-DeM-fwd : Set ℓ → Set ℓ' → Set (ℓ-max ℓ ℓ')
→-DeM-fwd P Q = (P → Q) → (¬ P) + Q

→-DeM-bwd : (¬ P) + Q → (P → Q)
→-DeM-bwd (inl nP) p = absurd (nP p)
→-DeM-bwd (inr q ) p = q


¬-→-fwd : ¬ (P → Q) → (¬¬ P) × (¬ Q)
¬-→-fwd = +-DeM-fwd ∘ contra-fwd →-DeM-bwd

¬-→-bwd : Set ℓ → Set ℓ' → Set (ℓ-max ℓ ℓ')
¬-→-bwd P Q = (¬¬ P) × (¬ Q) → ¬ (P → Q)



---------------
-- DN and LEM
---------------

-- Double Negation

DN-inst : Set ℓ → Set ℓ
DN-inst A = ¬¬ A → A

DN : Setω
DN = ∀ {ℓ} (A : Set ℓ) → DN-inst A

-- the converse of DN-inst is provable!
DN-conv : ∀ {ℓ} (A : Set ℓ) → A → ¬¬ A
DN-conv A x f = f x

double-DN : ∀ {ℓ} (A : Set ℓ) → ¬¬ (¬¬ A) → ¬¬ A
double-DN A = contra-fwd (DN-conv (¬ A))

DN-⊥ : ¬¬ ⊥ → ⊥
DN-⊥ dn⊥ = dn⊥ (λ ())

-- Law of Excluded Middle

LEM-inst : Set ℓ → Set ℓ
LEM-inst A = A + (¬ A)

LEM : Setω
LEM = ∀ {ℓ} (A : Set ℓ) → LEM-inst A

-- the double negation of LEM-inst is provable!
¬¬LEM-inst : ∀ (A : Set ℓ) → ¬¬ (LEM-inst A)
¬¬LEM-inst A ¬lem = ¬¬A ¬A
  where ¬A  : ¬ A
        ¬¬A : ¬¬ A
        ¬A  a = ¬lem (inl a)
        ¬¬A a = ¬lem (inr a)

-- LEM implies DN

LEM→DN-inst : ∀ {A : Set ℓ} → LEM-inst A → DN-inst A
LEM→DN-inst lem dn with lem
... | inl a  = a
... | inr na = absurd (dn na)

LEM→DN : LEM → DN
LEM→DN lem A = LEM→DN-inst (lem A)

-- thus the double negation of DN-inst is also provable
¬¬DN-inst : ∀ (A : Set ℓ) → ¬¬ (DN-inst A)
¬¬DN-inst A ¬dn = ¬¬LEM-inst A (λ lem → ¬dn (LEM→DN-inst lem))



--------------------------
-- Classical Corollaries
--------------------------

-- The key lemma: if P implies Q and ¬¬ P holds, then ¬¬ Q holds

→-dn : ∀ (P : Set ℓ) (dnP : ¬¬ P) → (P → Q) → ¬¬ Q
→-dn P dnP f = contra-fwd (contra-fwd f) dnP

→₂-dn : ∀ (P : Set ℓ) (dnP : ¬¬ P) (Q : Set ℓ') (dnQ : ¬¬ Q) → (P → Q → R) → ¬¬ R
→₂-dn P dnP Q dnQ f = double-DN _ (→-dn P dnP (λ p → →-dn Q dnQ (λ q → f p q)))

-- how ¬¬ factors in to →, ×, and +

dn-→-fwd : ¬¬ (P → Q) → P → ¬¬ Q
dn-→-fwd {P = P} {Q = Q} dnf p = →-dn (P → Q) dnf (λ f → f p)

dn-→-bwd : (P → ¬¬ Q) → ¬¬ (P → Q)
dn-→-bwd {Q = Q} f = →-dn (DN-inst Q) (¬¬DN-inst Q) (λ DN-Q p → DN-Q (f p))

dn-×-fwd : ¬¬ (P × Q) → (¬¬ P) × (¬¬ Q)
fst (dn-×-fwd {P = P} {Q = Q} dnP×Q)
  = →-dn (DN-inst (P × Q)) (¬¬DN-inst (P × Q)) (λ DN-P×Q → fst (DN-P×Q dnP×Q))
snd (dn-×-fwd {P = P} {Q = Q} dnP×Q)
  = →-dn (DN-inst (P × Q)) (¬¬DN-inst (P × Q)) (λ DN-P×Q → snd (DN-P×Q dnP×Q))

dn-×-bwd : (¬¬ P) × (¬¬ Q) → ¬¬ (P × Q)
dn-×-bwd {P = P} {Q = Q} (dnP , dnQ) = →₂-dn (DN-inst P) (¬¬DN-inst P) (DN-inst Q) (¬¬DN-inst Q) cnd-dn-×-bwd
  where cnd-dn-×-bwd : DN-inst P → DN-inst Q → P × Q
        cnd-dn-×-bwd DN-P DN-Q = (DN-P dnP , DN-Q dnQ)

-- hunh, this one doesn't hold purely!
dn-+-fwd : ¬¬ ( ¬¬ (P + Q) → (¬¬ P) + (¬¬ Q) )
dn-+-fwd {P = P} {Q = Q} = →-dn (DN-inst (P + Q)) (¬¬DN-inst (P + Q)) cnd-dn-+-fwd-dn
  where cnd-dn-+-fwd-dn : DN-inst (P + Q) → ¬¬ (P + Q) → (¬¬ P) + (¬¬ Q)
        cnd-dn-+-fwd-dn DN-P+Q dnP+Q with DN-P+Q dnP+Q
        ... | inl p = inl (DN-conv P p)
        ... | inr q = inr (DN-conv Q q)

dn-+-bwd : (¬¬ P) + (¬¬ Q) → ¬¬ (P + Q)
dn-+-bwd {P = P} (inl dnP) = →-dn (DN-inst P) (¬¬DN-inst P) (λ DN-P → inl (DN-P dnP))
dn-+-bwd {Q = Q} (inr dnQ) = →-dn (DN-inst Q) (¬¬DN-inst Q) (λ DN-Q → inr (DN-Q dnQ))

-- ...

dn-contra-bwd : ¬¬ (contra-bwd Q P)
dn-contra-bwd {Q = Q} {P = P} = →-dn (DN-inst Q) (¬¬DN-inst Q) cnd-contra-bwd
  where -- if (DN-inst Q) holds then (contra-bwd Q P) holds!
        cnd-contra-bwd : DN-inst Q → (¬ Q → ¬ P) → (P → Q)
        cnd-contra-bwd DN-Q f p = DN-Q (contra-fwd f (DN-conv P p))

-- as a corollary, if we can prove the contrapositive we get the double negation
contra-bwd-dn : (¬ Q → ¬ P) → ¬¬ (P → Q)
contra-bwd-dn = dn-→-fwd dn-contra-bwd

-- of course, the converse also holds
conv-contra-bwd-dn : ¬¬ (P → Q) → ¬ Q → ¬ P
conv-contra-bwd-dn {P = P} {Q = Q} dnf nQ p = DN-⊥ (→-dn (P → Q) dnf (λ f → nQ (f p)))


dn-×-DeM-fwd : ¬¬ (×-DeM-fwd P Q)
dn-×-DeM-fwd {P = P} {Q = Q} = contra-bwd-dn contra-×-DeM-fwd
  where -- we can prove the contrapositive of ×-DeM-fwd!
        contra-×-DeM-fwd : ¬ ((¬ P) + (¬ Q)) → ¬¬ (P × Q)
        contra-×-DeM-fwd = dn-×-bwd ∘ +-DeM-fwd

dn-×-DeM-bwd : ¬¬ (×-DeM-bwd P Q)
dn-×-DeM-bwd {P = P} {Q = Q} = contra-bwd-dn contra-×-DeM-bwd
  where -- we can prove the contrapositive of ×-DeM-bwd!
        contra-×-DeM-bwd : ¬¬ (P × Q) → ¬ ((¬ P) + (¬ Q))
        contra-×-DeM-bwd = +-DeM-bwd ∘ dn-×-fwd


dn-→-DeM-fwd : ¬¬ (→-DeM-fwd P Q)
dn-→-DeM-fwd {P = P} {Q = Q} = →-dn (LEM-inst P) (¬¬LEM-inst P) cnd-→-DeM-fwd
  where -- if (LEM P) holds then (→-DeM-fwd P Q) holds!
        cnd-→-DeM-fwd : LEM-inst P → (P → Q) → (¬ P) + Q
        cnd-→-DeM-fwd LEM-P f with LEM-P
        ... | inl p  = inr (f p)
        ... | inr nP = inl nP


-- dn-¬-→-bwd : ¬¬ (¬-→-bwd P Q)
-- dn-¬-→-bwd = {!!}

-- ¬-→-bwd P Q = (¬¬ P) × (¬ Q) → ¬ (P → Q)

-- ...

dn-→-dep-fwd : ∀ {Q : P → Set ℓ} → ¬¬ ((p : P) → Q p) → (p : P) → ¬¬ (Q p)
dn-→-dep-fwd {P = P} {Q = Q} dnf p = →-dn ((p : P) → Q p) dnf (λ f → f p)

thing : ∀ {Q : P → Set ℓ} → ¬¬ ( ¬ ((p : P) → Q p) → Σ[ p ∶ P ] ¬ (Q p) )
thing {P = P} {Q = Q} = {!!} -- contra-bwd-dn (dn-→-dep-bwd ∘ thinga)

dn-→-dep-bwd : ∀ {Q : P → Set ℓ} → ((p : P) → ¬¬ (Q p)) → ¬¬ ((p : P) → Q p)
dn-→-dep-bwd {P = P} {Q = Q} f = →-dn (LEM-inst P) (¬¬LEM-inst P) cnd-dn-→-dep-bwd
  where cnd-dn-→-dep-bwd : LEM-inst P → (p : P) → Q p
        cnd-dn-→-dep-bwd = {!!}

¬¬LEM : ¬¬ ( ∀ (A : Set ℓ) → LEM-inst A )
¬¬LEM {ℓ} = dn-→-dep-bwd ¬¬LEM-inst


-- thinga : ∀ {Q : P → Set ℓ} → ¬ (Σ[ p ∶ P ] Q p) → (∀ (p : P) → ¬ (Q p))
-- thinga nΣ p q = nΣ (p , q)

-- thingb : ∀ {Q : P → Set ℓ} → (∀ (p : P) → ¬ (Q p)) → ¬ (Σ[ p ∶ P ] Q p)
-- thingb f (p , q) = f p q

-- thing1 : ∀ {Q : P → Set ℓ} → Σ[ p ∶ P ] ¬ (Q p) → ¬ (∀ (p : P) → Q p)
-- thing1 (p , nQ) f = nQ (f p)

-- ¬¬LEM {ℓ} nf = DN-⊥ (→-dn (¬ (∀ (A : Set ℓ) → LEM-inst A) → Σ[ A ∶ Set ℓ ] ¬ (LEM-inst A))
--                           thing (λ th → cnd-¬¬LEM (th nf)))
--   where cnd-¬¬LEM : Σ[ A ∶ Set ℓ ] (¬ (LEM-inst A)) → ⊥
--         cnd-¬¬LEM (A , nLEM-A) = ¬¬LEM-inst A nLEM-A


