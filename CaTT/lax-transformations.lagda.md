```agda
{-# OPTIONS --guardedness #-}

open import CaTT.CaTT
open import CaTT.coherences
open import CaTT.whiskering
open import CaTT.type-morphisms

module CaTT.lax-transformations where
```

A pointwise homotopy Φ between type morphisms φ ψ : A ⇝ B is given by a term Φ a : [ B ] φ a ⇒ ψ a
for every term a : A. Pointwise homotopies can be composed and we have identity homotopies. 

```agda
lax-trans : {A B : Ty} (φ ψ : ty-morph A B) → Set
lax-trans {A} {B} φ ψ = (α : Tm A) → Tm ([ B ] (ty-morph-base φ) α ⇒ (ty-morph-base ψ) α)

-- record lax-nat-trans {A B : Ty} (φ ψ : morph A B) : Set
--   where
--   coinductive
--   field
--     lax-nat-trans-base : (α : Tm A) → Tm ([ B ] (morph-base φ) α ⇒ (morph-base ψ) α)
--     lax-nat-trans-step : {α α' : Tm A} →
--       lax-nat-trans
--         ( morph-postcomp (morph-step φ) (t*-base _ _) (lax-nat-trans-base α'))
--         ( morph-precomp (morph-step ψ) (s*-base _ _) (lax-nat-trans-base α))

-- open lax-nat-trans public

id-lax-trans : {A B : Ty} (φ : ty-morph A B) → lax-trans φ φ
id-lax-trans φ α = Id (ty-morph-base φ α)

lax-trans-comp : {A B : Ty} {φ ψ ξ : ty-morph A B}
    (Ψ : lax-trans ψ ξ) → (Φ : lax-trans φ ψ) → lax-trans φ ξ
lax-trans-comp Ψ Φ α = Comp (Ψ α) (Φ α)

lax-3-iso : {A B : Ty} {φ ψ : ty-morph A B} (Φ₀ Φ₁ : lax-trans φ ψ) → Set
lax-3-iso {A} {B} {φ} {ψ} Φ₀ Φ₁ = (α : Tm A) →
  Tm ([ ([ B ] ty-morph-base φ α ⇒ ty-morph-base ψ α) ] Φ₀ α ⇒ Φ₁ α)
  
record lax-trans-is-iso {A B : Ty} {φ ψ : ty-morph A B} (Φ : lax-trans φ ψ) : Set
  where
  field
    lax-trans-is-iso-inv : lax-trans ψ φ
    lax-trans-is-iso-inv-is-sec :
      lax-3-iso {φ = ψ} {ψ}
        ( lax-trans-comp {φ = ψ} {φ} {ψ} Φ lax-trans-is-iso-inv)
        ( id-lax-trans ψ)
    lax-trans-is-iso-inv-is-ret :
      lax-3-iso {φ = φ} {φ}
        ( lax-trans-comp {φ = φ} {ψ} {φ} lax-trans-is-iso-inv Φ)
        ( id-lax-trans φ)
open lax-trans-is-iso public

record lax-iso {A B : Ty} (φ ψ : ty-morph A B) : Set
  where
  field
    lax-iso-lax-trans : lax-trans φ ψ
    lax-iso-is-iso : lax-trans-is-iso {φ = φ} {ψ} lax-iso-lax-trans
open lax-iso public
```

The components of a lax natural isomorphism.

```agda
lax-iso-map : {A B : Ty} {φ ψ : ty-morph A B} → lax-iso φ ψ → lax-trans φ ψ
lax-iso-map = lax-iso-lax-trans

lax-iso-inv-map : {A B : Ty} {φ ψ : ty-morph A B} → lax-iso φ ψ → lax-trans ψ φ
lax-iso-inv-map Φ = lax-trans-is-iso-inv (lax-iso-is-iso Φ)

lax-iso-inv-is-sec : {A B : Ty} {φ ψ : ty-morph A B} → (Φ : lax-iso φ ψ) →
  lax-3-iso {φ = ψ} {ψ}
    ( lax-trans-comp {φ = ψ} {φ} {ψ}
      ( lax-iso-map Φ)
      ( lax-iso-inv-map Φ))
    ( id-lax-trans ψ)
lax-iso-inv-is-sec Φ = lax-trans-is-iso-inv-is-sec (lax-iso-is-iso Φ)

lax-iso-inv-is-ret : {A B : Ty} {φ ψ : ty-morph A B} → (Φ : lax-iso φ ψ) →
      lax-3-iso {φ = φ} {φ}
        ( lax-trans-comp {φ = φ} {ψ} {φ}
          ( lax-iso-inv-map Φ)
          ( lax-iso-map Φ))
        ( id-lax-trans φ)
lax-iso-inv-is-ret Φ = lax-trans-is-iso-inv-is-ret (lax-iso-is-iso Φ)
```

The identity lax transformation is a lax iso.

```agda
id-lax-trans-is-iso : {A B : Ty} (φ : ty-morph A B) → lax-trans-is-iso {φ = φ} {φ} (id-lax-trans φ)
lax-trans-is-iso-inv (id-lax-trans-is-iso φ) = id-lax-trans φ
lax-trans-is-iso-inv-is-sec (id-lax-trans-is-iso φ) = λ α → Left-unit-law _
lax-trans-is-iso-inv-is-ret (id-lax-trans-is-iso φ) = λ α → Right-unit-law _  
```

```agda
lax-iso-inv : {A B : Ty} {φ ψ : ty-morph A B} → lax-iso φ ψ → lax-iso ψ φ
lax-iso-inv Φ = record {
  lax-iso-lax-trans = lax-iso-inv-map Φ ;
  lax-iso-is-iso = record
    { lax-trans-is-iso-inv = lax-iso-map Φ
    ; lax-trans-is-iso-inv-is-sec = λ a → lax-iso-inv-is-ret Φ a
    ; lax-trans-is-iso-inv-is-ret = λ a → lax-iso-inv-is-sec Φ a
    }
  }
```

In fact every lax transformation between morphisms whose codomain is of positive dimension is
invertible.

```agda
lax-trans-nonzero-dim-is-iso : {A B : Ty} {t u : Tm B} {φ ψ : ty-morph A ([ B ] t ⇒ u)} →
  (Φ : lax-trans φ ψ) → lax-trans-is-iso {φ = φ} {ψ} Φ
lax-trans-is-iso-inv (lax-trans-nonzero-dim-is-iso Φ) α = Inv (Φ α)
lax-trans-is-iso-inv-is-sec (lax-trans-nonzero-dim-is-iso Φ) α = Inv-is-sec (Φ α)
lax-trans-is-iso-inv-is-ret (lax-trans-nonzero-dim-is-iso Φ) α = Inv-is-ret (Φ α)

lax-trans-iso : {A B : Ty} {t u : Tm B} {φ ψ : ty-morph A ([ B ] t ⇒ u)} →
  lax-trans φ ψ → lax-iso φ ψ
lax-iso-lax-trans (lax-trans-iso Φ) = Φ
lax-iso-is-iso (lax-trans-iso Φ) = lax-trans-nonzero-dim-is-iso Φ
```

Every lax-3-iso is pointwise invertible.

```agda
lax-3-iso-inv : {A B : Ty} {φ ψ : ty-morph A B} {Φ Ψ : lax-trans φ ψ} →
  lax-3-iso {φ = φ} {ψ} Φ Ψ → lax-3-iso {φ = φ} {ψ} Ψ Φ
lax-3-iso-inv ξ α = Inv (ξ α)

lax-3-iso-inv-is-sec : {A B : Ty} {φ ψ : ty-morph A B} {Φ Ψ : lax-trans φ ψ} →
  (ξ : lax-3-iso {φ = φ} {ψ} Φ Ψ) → (α : Tm A) →
    Tm ([ _ ] Comp (ξ α) ((lax-3-iso-inv {φ = φ} {ψ} {Φ} {Ψ}  ξ) α) ⇒ Id _)
lax-3-iso-inv-is-sec ξ α = Inv-is-sec (ξ α)

lax-3-iso-inv-is-ret : {A B : Ty} {φ ψ : ty-morph A B} {Φ Ψ : lax-trans φ ψ} →
  (ξ : lax-3-iso {φ = φ} {ψ} Φ Ψ) → (α : Tm A) →
    Tm ([ _ ] Comp ((lax-3-iso-inv {φ = φ} {ψ} {Φ} {Ψ}  ξ) α) (ξ α) ⇒ Id _)
lax-3-iso-inv-is-ret ξ α = Inv-is-ret (ξ α)
```

```agda
r-whisk-lax-trans : {A B C : Ty} {φ ψ : ty-morph A B} (Φ : lax-trans φ ψ) → (ξ : ty-morph B C) →
  lax-trans (ty-morph-comp ξ φ) (ty-morph-comp ξ ψ)
r-whisk-lax-trans Φ ξ α = ty-morph-base (ty-morph-step ξ) (Φ α)

l-whisk-lax-trans : {A B C : Ty} {ψ ξ : ty-morph B C} (φ : ty-morph A B) (Φ : lax-trans ψ ξ) →
  lax-trans (ty-morph-comp ψ φ) (ty-morph-comp ξ φ)
l-whisk-lax-trans φ Φ α = Φ (ty-morph-base φ α)

```