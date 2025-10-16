```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import whiskering
open import functoriality-of-whiskering
open import type-morphisms
open import lax-transformations
open import type-equivalences
open import synthetic-categories

module whiskering-equivalences where
```

```agda
r-whisk-morph-id-is-equiv : {C : cat} (A : Ty) → (p : t* A ≡ C) →
  ty-morph-is-equiv (r-whisk-morph A p (Id C))
r-whisk-morph-id-is-equiv {C} .([ ⋆ ] _ ⇒ C) base = record
  { ty-morph-is-equiv-inv-map = r-unit-morph C _ base
  ; ty-morph-is-equiv-inv-is-sec = lax-trans-iso (λ α → r-unit-lax-trans-inv C _ base α)
  ; ty-morph-is-equiv-inv-is-ret = lax-trans-iso (λ α → Inv (r-unit-lax-trans C _ base α))
  }
r-whisk-morph-id-is-equiv {C} .( [ _ ] _ ⇒ _ ) (step p) = record
  { ty-morph-is-equiv-inv-map = r-unit-morph C _ (step p)
  ; ty-morph-is-equiv-inv-is-sec = lax-trans-iso (λ α → r-unit-lax-trans-inv C _ (step p) α)
  ; ty-morph-is-equiv-inv-is-ret = lax-trans-iso (λ α → Inv (r-unit-lax-trans C _ (step p) α))
  }

postulate
  r-assoc-morph-is-equiv : {B : Ty} {D E F : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
      (B' : Ty) → (p : t* B' ≡ D) → ty-morph-is-equiv (r-assoc-morph g h B' p)

postulate
  r-transport-morph-is-equiv : {B : Ty} {D E : Tm B}  {g g' : Tm ([ B ] D ⇒ E)} (β : Tm ([ _ ] g ⇒ g')) →
    (B' : Ty) → (p : t* B' ≡ D) → ty-morph-is-equiv (r-transport-morph β B' p)

r-whisk-equiv-ty-morph-is-equiv-iso : {C D : cat} (f : equiv C D) → (A : Ty) → (p : t* A ≡ C) →
  lax-iso
    ( ty-morph-comp
      ( ty-morph-comp
        ( r-assoc-morph (equiv-map f) (equiv-sec-map f) A p)
        ( r-transport-morph (Inv (equiv-sec-is-ret f)) A p))
      ( r-whisk-morph A p (Id C)))
    ( ty-morph-comp
      ( r-whisk-morph _ (t*-r-whisk-ty (equiv-map f) A p) (equiv-sec-map f))
      ( r-whisk-morph A p (equiv-map f)))
r-whisk-equiv-ty-morph-is-equiv-iso f ([ .⋆ ] t ⇒ u) base = lax-trans-iso {!   !}
r-whisk-equiv-ty-morph-is-equiv-iso f ([ A ] t ⇒ u) (step p) =
  lax-trans-iso
    λ α → Inv 
      ( Comp
        ( ty-morph-base (ty-morph-step (r-assoc-morph _ _ _ (step p)))
          ( Inv ( r-transport-lax-trans (Inv (equiv-sec-is-ret f)) _ (step p) α)))
        ( Inv (r-assoc-lax-trans (equiv-map f) (equiv-sec-map f) _ (step p) α)))

r-whisk-equiv-ty-morph-is-equiv : {C D : cat} (f : equiv C D) → (A : Ty) → (p : t* A ≡ C) →
  ty-morph-is-equiv (r-whisk-morph A p (equiv-map f))
r-whisk-equiv-ty-morph-is-equiv f ([ .⋆ ] t ⇒ u) base =
  ty-equiv-6-for-2-left-factor
    ( r-whisk-morph ([ ⋆ ] t ⇒ u) base (equiv-map f))
    ( r-whisk-morph _ base (equiv-sec-map f))
    ( r-whisk-morph _ base (equiv-map f))
    ( ty-equiv-lax-iso-is-equiv
      ( ty-equiv-comp
        ( r-whisk-morph-id-is-equiv ([ ⋆ ] t ⇒ u) base)
        ( ty-equiv-comp
          ( id-ty-morph-is-equiv ([ ⋆ ] t ⇒ u))
          ( id-ty-morph-is-equiv ([ ⋆ ] t ⇒ u))))
      ( r-whisk-equiv-ty-morph-is-equiv-iso f ([ ⋆ ] t ⇒ u) base))
    ( ty-equiv-lax-iso-is-equiv
      ( ty-equiv-comp
        (r-whisk-morph-id-is-equiv _ base)
        ( ty-equiv-comp
          ( id-ty-morph-is-equiv _)
          ( id-ty-morph-is-equiv _)))
      ( r-whisk-equiv-ty-morph-is-equiv-iso
        ( equiv-inv f)
        ( r-whisk-ty (equiv-map f) ([ ⋆ ] t ⇒ u) base)
        ( base)))
r-whisk-equiv-ty-morph-is-equiv f ([ A ] t ⇒ u) (step p) =
  ty-equiv-6-for-2-left-factor
    ( r-whisk-morph ([ A ] t ⇒ u) (step p) (equiv-map f))
    ( r-whisk-morph _ (step (t*-r-whisk-ty (equiv-map f) A p)) (equiv-sec-map f))
    ( r-whisk-morph _ (step (t*-r-whisk-ty (equiv-sec-map f) _ _)) (equiv-map f))
    ( ty-equiv-lax-iso-is-equiv
      ( ty-equiv-comp
        ( r-whisk-morph-id-is-equiv ([ A ] t ⇒ u) (step p))
        ( ty-equiv-comp
          ( r-transport-morph-is-equiv (Inv (equiv-sec-is-ret f)) ([ A ] t ⇒ u) (step p))
          (r-assoc-morph-is-equiv (equiv-map f) (sec-map (equiv-sec f)) ([ A ] t ⇒ u) (step p))))
      ( r-whisk-equiv-ty-morph-is-equiv-iso f ([ A ] t ⇒ u) (step p)))
    ( ty-equiv-lax-iso-is-equiv
      ( ty-equiv-comp
        ( r-whisk-morph-id-is-equiv _ (step (t*-r-whisk-ty _ _ p)))
        ( ty-equiv-comp
          ( r-transport-morph-is-equiv (Inv (equiv-sec-is-ret (equiv-inv f)))
            ( _)
            ( step (t*-r-whisk-ty _ _ p)))
          ( r-assoc-morph-is-equiv (equiv-sec-map f) (equiv-map f)
            (_ )
            ( step (t*-r-whisk-ty _ _ p)))))
      ( r-whisk-equiv-ty-morph-is-equiv-iso (equiv-inv f) _ (step (t*-r-whisk-ty _ _ p))))
```