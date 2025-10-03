```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import whiskering
open import synthetic-categories
open import type-morphisms
open import pointwise-homotopies
open import functoriality-of-whiskering

module type-equivalences where
```

A type morphism φ : A ⇝ B is an *equivalence* if there is a type morphism ψ : B ⇝ A together with
pointwise homotopies ψφ ⇒ id_A and φψ ⇒ id_B. 

```agda
record morph-is-equiv {A B : Ty} (φ : morph A B) : Set
  where
  field
    inv : morph B A
    inv-is-sec : ptw-htpy (morph-comp φ inv) (morph-id B)
    inv-is-ret : ptw-htpy (morph-id A) (morph-comp inv φ)

record morph-equiv (A B : Ty) : Set
  where
  field
    morph-equiv-morph : morph A B
    morph-equiv-is-equiv : morph-is-equiv morph-equiv-morph
```

If a functor f : C → D is an equivalence and A is a type such that t* A ≡ C, then the right
whiskering morphism f ⋆ _ : A ⇝ f ⋆ A is a type equivalence.

```agda
r-morph-equiv-morph-is-equiv : {C D : cat} (f : equiv C D) → (A : Ty) → (p : t* A ≡ C) → 
  morph-is-equiv (r-whisk-morph A p (equiv-map f))
morph-is-equiv.inv (r-morph-equiv-morph-is-equiv {C} {D} f A p) =
  morph-comp (morph-r-unit C A p)
    ( morph-comp (morph-r-transport (equiv-ret-is-ret f) A p)
      ( morph-comp (morph-r-assoc-inv (equiv-map f) (equiv-ret-map f) A p)
        (r-whisk-morph _ (t*-r-whisk-ty (equiv-map f) A p) (equiv-ret-map f))))
morph-is-equiv.inv-is-ret (r-morph-equiv-morph-is-equiv {C} {D} f ([ A ] t ⇒ u) p) x =
  Inv 
    ( Comp ( ptw-htpy-r-unit C ([ A ] _ ⇒ _) p x)
      ( Comp
        ( morph-base (shift (morph-r-unit C ([ A ] t ⇒ u) p) _ (∂*-step _ _ _ (∂*-base _)))
          ( ptw-htpy-r-transport (equiv-ret-is-ret f) ([ A ] t ⇒ u) p x))
        ( morph-base
          ( shift
            ( morph-comp
              ( morph-r-unit C ([ A ] t ⇒ u) p)
              ( morph-r-transport (equiv-ret-is-ret f) ([ A ] t ⇒ u) p))
            ( _)
            ( ∂*-step _ _ _ (∂*-base _)))
          ( ptw-htpy-r-assoc-inv (equiv-map f) (equiv-ret-map f) ([ A ] t ⇒ u) p x))))
morph-is-equiv.inv-is-sec (r-morph-equiv-morph-is-equiv f A p) y = {!  y !}
```
-- ( ptw-htpy-r-assoc-inv (equiv-map f) (equiv-ret-map f) A p x)