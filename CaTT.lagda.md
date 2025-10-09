```agda
open import Data.Nat
```

```agda
module CaTT where
```

The type theory CaTT (cf. https://arxiv.org/abs/2106.04475) is implemented as a type Ty of types
toghether with an unspecified presheaf Tm over Ty.

```agda
mutual
  data Ty : Set where
    ⋆ : Ty
    [_]_⇒_ : (A : Ty) → Tm A → Tm A → Ty

  postulate Tm : Ty → Set
```

Coherences, as for example identities and inverses below, can be assumed on ad hoc using agda's
postulates. Every coherence assumed rests on a pen-and-paper derivation in CaTT.

```agda
postulate Inv : {A : Ty} {t u : Tm A} {f g : Tm ([ A ] t ⇒ u)} → Tm ([ _ ] f ⇒ g) → Tm ([ _ ] g ⇒ f)

postulate Id : {A : Ty} (a : Tm A) → Tm ([ A ] a ⇒ a)
```

The dimension of types.

```agda
dim : Ty → ℕ
dim ⋆ = 0
dim ([ A ] _ ⇒ _) = suc (dim A)
```

The boundary/source/target predicates. For types A B : Ty we have ∂* A ≡ B iff either A = B or
A = [ A' ] t ⇒ u for some type A' with ∂* A' ≡ B. For a type A and a term u : B, we have t* A ≡ u
iff either A = [ B ] t ⇒ u for some term t : B or A = [ A' ] x ⇒ y for some type A' with t* A' ≡ u.
Note that we can have t* A ≡ u and t* A ≡ U for some u ≠ U. The predicate s*_≡_ is defined dually.

```agda
data ∂*_≡_ : Ty → Ty → Set where
  base : {A : Ty} → ∂* A ≡ A
  step : {A : Ty} {t u : Tm A} → {B : Ty} → ∂* A ≡ B → ∂* ([ A ] t ⇒ u) ≡ B

data s*_≡_ {B : Ty} : Ty → Tm B → Set where 
  base : {D E : Tm B} → s* ([ B ] D ⇒ E) ≡ D
  step : {A : Ty} {D : Tm B} → s* A ≡ D → {t u : Tm A} → s* ([ A ] t ⇒ u) ≡ D

data t*_≡_ {B : Ty} : Ty → Tm B → Set where 
  base : {C D : Tm B} → t* ([ B ] C ⇒ D) ≡ D
  step : {A : Ty} {D : Tm B} → t* A ≡ D → {t u : Tm A} → t* ([ A ] t ⇒ u) ≡ D
```

The operators returning the codimension-1 boundary/source/target of a type. Since the latter is
well-defined only for types of dimension > 0, the operators take an additional argument witnessing
t* A ≡ C or s* A ≡ C for some term C : ⋆, which ensures that the dimensional constraint is
satisfied.  

```agda
∂ₜ : (A : Ty) → {C : Tm ⋆} → (p : t* A ≡ C) → Ty
∂ₜ ([ _ ] _ ⇒ _) base = ⋆
∂ₜ ([ A ] _ ⇒ _) (step _) = A

∂ₜ⁻ : (A : Ty) → {C : Tm ⋆} → (p : t* A ≡ C) → Tm (∂ₜ A p)
∂ₜ⁻ ([ _ ] t ⇒ _) base = t
∂ₜ⁻ ([ _ ] t ⇒ _) (step _) = t

∂ₜ⁺ : (A : Ty) → {C : Tm ⋆} → (p : t* A ≡ C) → Tm (∂ₜ A p)
∂ₜ⁺ ([ _ ] _ ⇒ u) base = u
∂ₜ⁺ ([ _ ] _ ⇒ u) (step _) = u

∂ₛ : (A : Ty) → {C : Tm ⋆} → (p : s* A ≡ C) → Ty
∂ₛ ([ _ ] _ ⇒ _) base = ⋆
∂ₛ ([ A ] _ ⇒ _) (step _) = A

∂ₛ⁻ : (A : Ty) → {C : Tm ⋆} → (p : s* A ≡ C) → Tm (∂ₛ A p)
∂ₛ⁻ ([ _ ] t ⇒ _) base = t
∂ₛ⁻ ([ _ ] t ⇒ _) (step _) = t

∂ₛ⁺ : (A : Ty) → {C : Tm ⋆} → (p : s* A ≡ C) → Tm (∂ₛ A p)
∂ₛ⁺ ([ _ ] _ ⇒ u) base = u
∂ₛ⁺ ([ _ ] _ ⇒ u) (step _) = u
```