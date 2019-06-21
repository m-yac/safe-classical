I couldn't find any treatment of classical reasoning without postulates in agda to my satisfaction, so I made one!


The idea is that any theorem which holds 'classically' (i.e. proven assuming LEM as a postulate) should hold just as well constructively (e.g. in agda with the `--safe` flag) just so long as double negation (`¬¬`) is inserted appropriately in the statement and `assume-dn` (or a something similar) is inserted appropriately in the proof, where:
```agda
assume-dn : ¬¬ A → (A → B) → ¬¬ B
```
is defined in `Theorems.Constructive`.

Breifly, the philosophy behind this is that many times (especially in topology!) when mathematicians say that they've proven `P`, they really mean that they've proven that `P` cannot be false (i.e. that `P` *must* be true). If we demand all proofs be constructive, then these two notions (`P` and `¬¬ P`) are very much distinct. If the reader is not familiar with this distinction, then try to prove directly (i.e. without using LEM or DNE) the missing facts in `Theorems.Constructive` -- it's not easy!

### Structure

- `Prelude` fixes some basics of intuitionistic type theory, assuming the reader's familiarity with the [Curry-Howard correspondence](https://en.wikipedia.org/wiki/Curry%E2%80%93Howard_correspondence).

- `Theorems.Constructive` proves those instances of DeMorgan's laws, double negation laws, etc. that *are* constructive, and notes those that are missing.

- `Omniscience.Principles` states the various [principles of omniscience](https://ncatlab.org/nlab/show/principle+of+omniscience) that we'll consider, most familiarly:

     ```agda
     LEM = ∀ {ℓ} (A : Set ℓ) → A + (¬ A)
     DNE = ∀ {ℓ} (A : Set ℓ) → ¬¬ A → A
     ```
   
    - `Omniscience.Implications` establishes the relationships between these principles, as well as proves a suitably doubly-negated version of each of them, including:
    
         ```agda
         ¬¬LEM-inst : ∀ {ℓ} (A : Set ℓ) → ¬¬ ( A + (¬ A) )
         ¬¬DNE-inst : ∀ {ℓ} (A : Set ℓ) → ¬¬ ( ¬¬ A → A )
         ```
         
         Thus the constructive mathematician doesn't *really* reject LEM or DNE, they are just always wrapped up in `¬¬`.
    
    - `Omniscience.NonConstructive` fixes our definition of 'non-constructive' and shows that all our omniscience principles indeed satisfy this predicate.

- `Theorems.NonConstructive` proves the double negation of most of the missing classical facts from `Theorems.Constructive` and proves that they are all non-constructive, using `assume-dn` and our omniscience principles (the double negations of the instances of which we've established all hold).

### TODO / Future Additions

- In-progress: `Theorems.Inconsistent` will show that the remaining two classical facts are *inconsistent* with standard agda! (Claim (5) is discussed on [this nLab page](https://ncatlab.org/nlab/show/double-negation).) This essentially corresponds to the idea that not all placements of `¬¬` are equally good.

- A proof of LPO for a coinductive `ℕ∞` (like in [this blog post](http://math.andrej.com/2014/05/08/seemingly-impossible-proofs/)) as well as for finite sets (in the sense of having an injection to some `Fin n`).

- A proof of a properly double-negated Brower's fixed point theorem, or similar topological fact, in this style.
