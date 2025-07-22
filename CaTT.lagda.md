```agda
open import Data.Nat

module CaTT where

mutual

  data Ty : Set where
    ⋆ : Ty
    [_]_⇒_ : (A : Ty) → Tm A → Tm A → Ty

  postulate Tm : Ty → Set

postulate Inv : {A : Ty} {t u : Tm A} → Tm ([ A ] t ⇒ u)  → Tm ([ A ] u ⇒ t)

postulate Id : {A : Ty} (a : Tm A) → Tm ([ A ] a ⇒ a)

dim : Ty → ℕ
dim ⋆ = 0
dim ([ A ] _ ⇒ _) = suc (dim A)

data t*_≡_ {B : Ty} : Ty → Tm B → Set where 
  t*-base : (C D : Tm B) → t* ([ B ] C ⇒ D) ≡ D
  t*-step : {A : Ty} {D : Tm B} →  (t* A ≡ D) → (t u : Tm A) → t* ([ A ] t ⇒ u) ≡ D

data s*_≡_ {B : Ty} : Ty → Tm B → Set where 
  s*-base : (D E : Tm B) → s* ([ B ] D ⇒ E) ≡ D
  s*-step : {A : Ty} {D : Tm B} → (s* A ≡ D) → (t u : Tm A) → s* ([ A ] t ⇒ u) ≡ D

data ∂*_≡_ : Ty → Ty → Set where
  ∂*-base : (A : Ty) → ∂* A ≡ A
  ∂*-step : {A : Ty} (t u : Tm A) → (B : Ty) → ∂* A ≡ B → ∂* ([ A ] t ⇒ u) ≡ B

∂ₜ : (A : Ty) → {C : Tm ⋆} → (p : t* A ≡ C) → Ty
∂ₜ ([ _ ] _ ⇒ _) (t*-base _ _) = ⋆
∂ₜ ([ A ] _ ⇒ _) (t*-step _ _ _) = A

∂ₜ⁺ : (A : Ty) → {C : Tm ⋆} → (p : t* A ≡ C) → Tm (∂ₜ A p)
∂ₜ⁺ ([ _ ] _ ⇒ u) (t*-base _ _) = u
∂ₜ⁺ ([ _ ] _ ⇒ u) (t*-step _ _ _) = u

∂ₜ⁻ : (A : Ty) → {C : Tm ⋆} → (p : t* A ≡ C) → Tm (∂ₜ A p)
∂ₜ⁻ ([ _ ] t ⇒ _) (t*-base _ _) = t
∂ₜ⁻ ([ _ ] t ⇒ _) (t*-step _ _ _) = t
```