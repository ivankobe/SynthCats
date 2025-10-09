```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import whiskering
open import synthetic-categories
open import type-morphisms
open import lax-transformations
open import functoriality-of-whiskering

module type-equivalences where
```

A type morphism φ : A ⇝ B is an *equivalence* if there is a type morphism ψ : B ⇝ A together with
lax isos ψφ ≅ id_A and φψ ≅ id_B. 

```agda
record ty-morph-is-equiv {A B : Ty} (φ : ty-morph A B) : Set
  where
  field
    ty-morph-is-equiv-inv : ty-morph B A
    ty-morph-is-equiv-inv-is-sec : lax-iso (ty-morph-comp φ ty-morph-is-equiv-inv) (id-ty-morph B)
    ty-morph-is-equiv-inv-is-ret : lax-iso (id-ty-morph A) (ty-morph-comp ty-morph-is-equiv-inv φ)

open ty-morph-is-equiv public

record ty-equiv (A B : Ty) : Set
  where
  field
    ty-equiv-morph : ty-morph A B
    ty-equiv-is-equiv : ty-morph-is-equiv ty-equiv-morph

open ty-equiv public
```

The componenets of a type equivalence.

```agda
ty-equiv-map : {A B : Ty} → ty-equiv A B → ty-morph A B
ty-equiv-map = ty-equiv-morph

ty-equiv-inv-map : {A B : Ty} → ty-equiv A B → ty-morph B A
ty-equiv-inv-map φ = ty-morph-is-equiv-inv (ty-equiv-is-equiv φ)

ty-equiv-inv-is-sec : {A B : Ty} → (φ : ty-equiv A B) →
  lax-iso (ty-morph-comp (ty-equiv-morph φ) (ty-equiv-inv-map φ)) (id-ty-morph B)
ty-equiv-inv-is-sec φ = ty-morph-is-equiv-inv-is-sec (ty-equiv-is-equiv φ)

ty-equiv-inv-is-sec-map : {A B : Ty} → (φ : ty-equiv A B) →
  lax-trans (ty-morph-comp (ty-equiv-morph φ) (ty-equiv-inv-map φ)) (id-ty-morph B)
ty-equiv-inv-is-sec-map φ = lax-iso-map (ty-equiv-inv-is-sec φ)

ty-equiv-inv-is-sec-inv-map : {A B : Ty} → (φ : ty-equiv A B) →
  lax-trans (id-ty-morph B) (ty-morph-comp (ty-equiv-morph φ) (ty-equiv-inv-map φ))
ty-equiv-inv-is-sec-inv-map φ = lax-iso-inv-map (ty-equiv-inv-is-sec φ)

ty-morph-is-equiv-inv-is-sec-map : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-trans (ty-morph-comp φ (ty-morph-is-equiv-inv P)) (id-ty-morph B)
ty-morph-is-equiv-inv-is-sec-map φ P = lax-iso-map (ty-morph-is-equiv-inv-is-sec P)

ty-morph-is-equiv-inv-is-sec-inv : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-trans (id-ty-morph B) (ty-morph-comp φ (ty-morph-is-equiv-inv P))
ty-morph-is-equiv-inv-is-sec-inv φ P = lax-iso-inv-map (ty-morph-is-equiv-inv-is-sec P)

ty-equiv-inv-is-ret : {A B : Ty} → (φ : ty-equiv A B) →
  lax-iso (id-ty-morph A) (ty-morph-comp (ty-equiv-inv-map φ) (ty-equiv-morph φ))
ty-equiv-inv-is-ret φ = ty-morph-is-equiv-inv-is-ret (ty-equiv-is-equiv φ)

ty-equiv-inv-is-ret-map : {A B : Ty} → (φ : ty-equiv A B) →
  lax-trans (id-ty-morph A) (ty-morph-comp (ty-equiv-inv-map φ) (ty-equiv-morph φ))
ty-equiv-inv-is-ret-map φ = lax-iso-map (ty-equiv-inv-is-ret φ)

ty-equiv-inv-is-ret-inv-map : {A B : Ty} → (φ : ty-equiv A B) →
  lax-trans (ty-morph-comp (ty-equiv-inv-map φ) (ty-equiv-morph φ)) (id-ty-morph A)
ty-equiv-inv-is-ret-inv-map φ = lax-iso-inv-map (ty-equiv-inv-is-ret φ)
```

```
record ty-morph-is-adj {A B : Ty} (φ : ty-morph A B) : Set
  where
  field
    ty-morph-is-adj-inv : ty-morph B A
    ty-morph-is-adj-inv-is-sec : lax-trans (ty-morph-comp φ ty-morph-is-adj-inv) (id-ty-morph B)
    ty-morph-is-adj-inv-is-ret : lax-trans (id-ty-morph A) (ty-morph-comp ty-morph-is-adj-inv φ)

open ty-morph-is-adj public

record ty-adj (A B : Ty) : Set
  where
  field
    ty-adj-morph : ty-morph A B
    ty-adj-is-adj : ty-morph-is-adj ty-adj-morph

open ty-adj public
```


```agda
ty-adj-map : {A B : Ty} → ty-adj A B → ty-morph A B
ty-adj-map = ty-adj-morph

ty-adj-inv-map : {A B : Ty} → ty-adj A B → ty-morph B A
ty-adj-inv-map φ = ty-morph-is-adj-inv (ty-adj-is-adj φ)

ty-adj-inv-is-sec-map : {A B : Ty} → (φ : ty-adj A B) →
  lax-trans (ty-morph-comp (ty-adj-morph φ) (ty-adj-inv-map φ)) (id-ty-morph B)
ty-adj-inv-is-sec-map φ = ty-morph-is-adj-inv-is-sec (ty-adj-is-adj φ)

ty-adj-inv-is-ret-map : {A B : Ty} → (φ : ty-adj A B) →
  lax-trans (id-ty-morph A) (ty-morph-comp (ty-adj-inv-map φ) (ty-adj-morph φ))
ty-adj-inv-is-ret-map φ = ty-morph-is-adj-inv-is-ret (ty-adj-is-adj φ)
```

If a type morphism between types of nonzero dimension is part of an adjunction,
then it is an equivalence. 

```agda
ty-morph-is-adj-is-equiv : {A B : Ty} {a a' : Tm A} {b b' : Tm B} 
  {φ : ty-morph ([ A ] a ⇒ a') ([ B ] b ⇒ b')} → ty-morph-is-adj φ → ty-morph-is-equiv φ
ty-morph-is-equiv-inv (ty-morph-is-adj-is-equiv p) = ty-morph-is-adj-inv p
ty-morph-is-equiv-inv-is-sec (ty-morph-is-adj-is-equiv p) =
  lax-trans-iso (ty-morph-is-adj-inv-is-sec p)
ty-morph-is-equiv-inv-is-ret (ty-morph-is-adj-is-equiv p) =
  lax-trans-iso (ty-morph-is-adj-inv-is-ret p)

ty-morph-adj-equiv : {A B : Ty} {a a' : Tm A} {b b' : Tm B} →
  ty-adj ([ A ] a ⇒ a') ([ B ] b ⇒ b') → ty-equiv ([ A ] a ⇒ a') ([ B ] b ⇒ b')
ty-equiv-morph (ty-morph-adj-equiv φ) = ty-adj-map φ
ty-equiv-is-equiv (ty-morph-adj-equiv φ) = ty-morph-is-adj-is-equiv (ty-adj-is-adj φ)
```

# Properties of type equivalences.

The identity type morphism is an equivalence.

```agda
id-ty-morph-is-equiv : (A : Ty) → ty-morph-is-equiv (id-ty-morph A)
id-ty-morph-is-equiv A = record
  { ty-morph-is-equiv-inv = id-ty-morph A
  ; ty-morph-is-equiv-inv-is-sec = record {
      lax-iso-lax-trans = id-lax-trans (id-ty-morph A) ;
      lax-iso-is-iso = record
        { lax-trans-is-iso-inv = id-lax-trans (id-ty-morph A)
        ; lax-trans-is-iso-inv-is-sec = λ α → Left-unit-law _
        ; lax-trans-is-iso-inv-is-ret = λ α → Right-unit-law _
        }
      }
  ; ty-morph-is-equiv-inv-is-ret = record {
    lax-iso-lax-trans = id-lax-trans (id-ty-morph A) ;
    lax-iso-is-iso = record
      { lax-trans-is-iso-inv = id-lax-trans (id-ty-morph A)
      ; lax-trans-is-iso-inv-is-sec = λ α → Left-unit-law _
      ; lax-trans-is-iso-inv-is-ret = λ α → Right-unit-law _
      }
    }
  }
```

If a type morphism f : A ⇝ B is an equivalence and tere is a lax isomorphism α : f ≅ f',
then f' is an equivalence. 

```agda
ty-equiv-lax-iso-is-ty-adj : {A B : Ty} {f f' : ty-morph A B} (p : ty-morph-is-equiv f) →
  (φ : lax-iso f f') → ty-morph-is-adj f'
ty-equiv-lax-iso-is-ty-adj p φ = record
  { ty-morph-is-adj-inv = ty-morph-is-equiv-inv p
  ; ty-morph-is-adj-inv-is-sec = λ b → {!  !}
  ; ty-morph-is-adj-inv-is-ret = {!   !}
  }
```

-- ```agda
-- morph-equiv-invariant-under-lax-trans : {A B : Ty} {f f' : morph A B} (e : morph-is-equiv f) →
--   (α : lax-iso f f') → morph-is-equiv f'
-- morph-is-equiv-inv (morph-equiv-invariant-under-lax-trans e α) = morph-is-equiv-inv e
-- lax-iso-lax-trans (morph-is-equiv-inv-is-sec (morph-equiv-invariant-under-lax-trans e α)) b =
--   Comp
--     ( lax-iso-lax-trans (morph-is-equiv-inv-is-sec e) b)
--     ( lax-trans-is-iso-inv (lax-iso-is-iso α) _)
-- lax-trans-is-iso-inv
--   ( lax-iso-is-iso
--     ( morph-is-equiv-inv-is-sec
--       ( morph-equiv-invariant-under-lax-trans e α))) b =
--   Comp
--     ( lax-iso-lax-trans α _)
--     ( lax-trans-is-iso-inv (lax-iso-is-iso (morph-is-equiv-inv-is-sec e)) b)
-- lax-trans-is-iso-inv-is-sec
--   ( lax-iso-is-iso
--      ( morph-is-equiv-inv-is-sec
--         ( morph-equiv-invariant-under-lax-trans e α))) b = {!   !}
-- lax-trans-is-iso-inv-is-ret
--   (lax-iso-is-iso
--      (morph-is-equiv-inv-is-sec
--         (morph-equiv-invariant-under-lax-trans e α))) b = {!   !}
-- morph-is-equiv-inv-is-ret (morph-equiv-invariant-under-lax-trans e α) = {!   !}
```



If a functor f : C → D is an equivalence and A is a type such that t* A ≡ C, then the right
whiskering morphism f ⋆ _ : A ⇝ f ⋆ A is a type equivalence.


-- ```agda
-- r-whisk-equiv-morph-is-equiv : {C D : cat} (f : equiv C D) → (A : Ty) → (p : t* A ≡ C) → 
--   morph-is-equiv (r-whisk-morph A p (equiv-map f))
-- morph-is-equiv-inv (r-whisk-equiv-morph-is-equiv {C} f A p) =
--   morph-comp (morph-r-unit C A p)
--     ( morph-comp (morph-r-transport (equiv-ret-is-ret f) A p)
--       ( morph-comp (morph-r-assoc-inv (equiv-map f) (equiv-ret-map f) A p)
--         (r-whisk-morph _ (t*-r-whisk-ty (equiv-map f) A p) (equiv-ret-map f))))
-- morph-is-equiv-inv-is-ret (r-whisk-equiv-morph-is-equiv {C} f ([ A ] t ⇒ u) p) = 
--   lax-trans-nonzero-dim-iso
--     ( λ α → Inv 
--       ( Comp ( lax-trans-r-unit C ([ A ] _ ⇒ _) p α)
--         ( Comp
--           ( morph-base (shift (morph-r-unit C ([ A ] t ⇒ u) p) _ (∂*-step _ _ _ (∂*-base _)))
--             ( lax-trans-r-transport (equiv-ret-is-ret f) ([ A ] t ⇒ u) p α))
--           ( morph-base
--             ( shift
--               ( morph-comp
--                 ( morph-r-unit C ([ A ] t ⇒ u) p)
--                 ( morph-r-transport (equiv-ret-is-ret f) ([ A ] t ⇒ u) p))
--               ( _)
--               ( ∂*-step _ _ _ (∂*-base _)))
--             ( lax-trans-r-assoc-inv (equiv-map f) (equiv-ret-map f) ([ A ] t ⇒ u) p α)))))
-- morph-is-equiv-inv-is-sec (r-whisk-equiv-morph-is-equiv f ([ ⋆ ] t ⇒ C) (t*-base .t .C)) =
--   lax-trans-nonzero-dim-iso {!   !}
-- morph-is-equiv-inv-is-sec (r-whisk-equiv-morph-is-equiv f ([ [ A ] x ⇒ y ] t ⇒ u) (t*-step p .t .u)) =
--   lax-trans-nonzero-dim-iso {!   !}
-- ```