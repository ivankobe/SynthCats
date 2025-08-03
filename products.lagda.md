```agda
{-# OPTIONS --guardedness #-}

open import Data.Product.Base

open import CaTT
open import whiskering
open import synthetic-categories
open import terminal-category

module products where
```

We postulate the existence of products of synthetic categories.

```agda
module prod-cons
  (C D : category)
  where

  postulate prod : category
  postulate pr₁-prod : functor prod C
  postulate pr₂-prod : functor prod D

open prod-cons public

module prod-intro
  {C D : category} {A : Ty} {p : t* A ≡ (prod C D)}
  (f : Tm (r-whisk-ty (pr₁-prod C D) A p)) (g : Tm (r-whisk-ty (pr₂-prod C D) A p))
  where

  postulate
    pair-prod : Tm A
  postulate
    coh₁-prod : Tm ([ r-whisk-ty (pr₁-prod C D) A p ] f ⇒ r-whisk-tm (pr₁-prod C D) A p pair-prod)
  postulate 
    coh₂-prod : Tm ([ r-whisk-ty (pr₂-prod C D) A p ] g ⇒ r-whisk-tm (pr₂-prod C D) A p pair-prod)

open prod-intro public
```

The formation of products is functorial in the second component, in the following sense.
Fix a synthetic category C. Then, for every type A such that s* A ≡ D and t* A ≡ E, there exists:
- a type C × A with t* (C × A) ≡ C × E
- a term id_{pr_C}^A : pr_C ⋆ (C × A)
For every term α : A, there moreover exist:
- a term C × α : C × A
- a term α_E : pr_E ⋆ (C × A)
- a term φ_C : [ pr_C ⋆ (C × A) ] id_{pr_C}^A ⇒ pr_C ⋆ (C × α)
- a term φ_E : [ pr_E ⋆ (C × A) ] α_E ⇒ pr_E ⋆ (C × α).
The formation of products is likewise functorial in the first component.

```agda
mutual

  snd-prod-ty : (C : category) → (A : Ty) → (t u : Tm A) → Ty
  snd-prod-ty C ⋆ D E = [ ⋆ ] prod C D ⇒ prod C E
  snd-prod-ty C ([ A ] x ⇒ y) t u =
    [ snd-prod-ty C A x y ] snd-prod-tm C A x y t ⇒ snd-prod-tm C A x y u

  snd-prod-tm : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm (snd-prod-ty C A t u)
  snd-prod-tm C A t u α = pair-prod (snd-prod-comm₁ C A t u) (snd-prod-comm₂ C A t u α)

  snd-prod-ty-tgt : (C : category) → (A : Ty) → (t u : Tm A) →
    t* (snd-prod-ty C A t u) ≡ (prod C (tgt A t u))
  snd-prod-ty-tgt C ⋆ D E = t*-base _ _
  snd-prod-ty-tgt C ([ A ] x ⇒ y) t u = t*-step (snd-prod-ty-tgt C A x y) _ _

  snd-prod-comm₁ : (C : category) → (A : Ty) → (t u : Tm A) →
    Tm (r-whisk-ty (pr₁-prod C (tgt A t u)) (snd-prod-ty C A t u) (snd-prod-ty-tgt C A t u))
  snd-prod-comm₁ C ⋆ D E = pr₁-prod C D
  snd-prod-comm₁ C ([ A ] x ⇒ y) t u =
    comp (snd-prod-iso₁ C A x y u) (Inv (snd-prod-iso₁ C A x y t))

  snd-prod-comm₂ : (C : category) → (A : Ty) → (t u : Tm A) → (β : Tm ([ A ] t ⇒ u)) →
    Tm (r-whisk-ty (pr₂-prod C (tgt A t u)) (snd-prod-ty C A t u) (snd-prod-ty-tgt C A t u))
  snd-prod-comm₂ C ⋆ D E f = comp f (pr₂-prod C D)
  snd-prod-comm₂ C ([ A ] x ⇒ y) f g β =
    comp
      ( snd-prod-iso₂ C A x y g)
      ( comp
        ( snd-prod-coh C f g)
        ( Inv (snd-prod-iso₂ C A x y f)))

  postulate
    snd-prod-coh : (C : category) → {A : Ty} → {x y : Tm A} → (f g : Tm ([ A ] x ⇒ y)) →
      Tm ([ _ ] snd-prod-comm₂ C A x y f ⇒ snd-prod-comm₂ C A x y g)

  snd-prod-iso₁ : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        snd-prod-comm₁ C A t u ⇒
        r-whisk-tm (pr₁-prod C _) _ (snd-prod-ty-tgt C A t u) (snd-prod-tm C A t u α))
  snd-prod-iso₁ C A t u α = coh₁-prod (snd-prod-comm₁ C A t u) (snd-prod-comm₂ C A t u α)

  snd-prod-iso₂ : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        snd-prod-comm₂ C A t u α ⇒
        r-whisk-tm (pr₂-prod C (tgt A t u)) _ (snd-prod-ty-tgt C A t u) (snd-prod-tm C A t u α))
  snd-prod-iso₂ C A t u α = coh₂-prod _ _

mutual

  fst-prod-ty : (C : category) → (A : Ty) → (t u : Tm A) → Ty
  fst-prod-ty C ⋆ D E = [ ⋆ ] prod D C ⇒ prod E C
  fst-prod-ty C ([ A ] x ⇒ y) t u =
    [ fst-prod-ty C A x y ] fst-prod-tm C A x y t ⇒ fst-prod-tm C A x y u

  fst-prod-tm : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm (fst-prod-ty C A t u)
  fst-prod-tm C A t u α = pair-prod (fst-prod-comm₁ C A t u α) (fst-prod-comm₂ C A t u)

  fst-prod-ty-tgt : (C : category) → (A : Ty) → (t u : Tm A) →
    t* (fst-prod-ty C A t u) ≡ (prod (tgt A t u) C)
  fst-prod-ty-tgt C ⋆ D E = t*-base _ _
  fst-prod-ty-tgt C ([ A ] x ⇒ y) t u = t*-step (fst-prod-ty-tgt C A x y) _ _

  fst-prod-comm₂ : (C : category) → (A : Ty) → (t u : Tm A) →
    Tm (r-whisk-ty (pr₂-prod (tgt A t u) C) (fst-prod-ty C A t u) (fst-prod-ty-tgt C A t u))
  fst-prod-comm₂ C ⋆ D E = pr₂-prod D C
  fst-prod-comm₂ C ([ A ] x ⇒ y) t u =
    comp (fst-prod-iso₂ C A x y u) (Inv (fst-prod-iso₂ C A x y t))

  fst-prod-comm₁ : (C : category) → (A : Ty) → (t u : Tm A) → (β : Tm ([ A ] t ⇒ u)) →
    Tm (r-whisk-ty (pr₁-prod (tgt A t u) C) (fst-prod-ty C A t u) (fst-prod-ty-tgt C A t u))
  fst-prod-comm₁ C ⋆ D E f = comp f (pr₁-prod D C)
  fst-prod-comm₁ C ([ A ] x ⇒ y) f g β =
    comp
      ( fst-prod-iso₁ C A x y g)
      ( comp
        ( fst-prod-coh C f g)
        ( Inv (fst-prod-iso₁ C A x y f)))

  postulate
    fst-prod-coh : (C : category) → {A : Ty} → {x y : Tm A} → (f g : Tm ([ A ] x ⇒ y)) →
      Tm ([ _ ] fst-prod-comm₁ C A x y f ⇒ fst-prod-comm₁ C A x y g)

  fst-prod-iso₂ : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        fst-prod-comm₂ C A t u ⇒
        r-whisk-tm (pr₂-prod _ C) _ (fst-prod-ty-tgt C A t u) (fst-prod-tm C A t u α))
  fst-prod-iso₂ C A t u α = coh₂-prod _ _

  fst-prod-iso₁ : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        fst-prod-comm₁ C A t u α ⇒
        r-whisk-tm (pr₁-prod (tgt A t u) C) _ (fst-prod-ty-tgt C A t u) (fst-prod-tm C A t u α))
  fst-prod-iso₁ C A t u α = coh₁-prod _ _
```

For a type A : Ty and a category D with t* A ≡ D, we have t* (C × A) ≡ C × D.

```agda
t*-fst-prod : (C D : category) → (A : Ty) → (p : t* A ≡ D) →
  t* fst-prod-ty C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p) ≡ prod D C
t*-fst-prod C D ([ .⋆ ] x ⇒ .D) (t*-base .x .D) = t*-base _ _
t*-fst-prod C D ([ [ .⋆ ] t ⇒ .D ] x ⇒ y) (t*-step (t*-base .t .D) .x .y) =
  t*-step (t*-base _ _) _ _
t*-fst-prod C D ([ [ A ] t ⇒ u ] x ⇒ y) (t*-step (t*-step p .t .u) .x .y) =
  t*-step (t*-fst-prod C D ([ A ] t ⇒ u) (t*-step p t u)) _ _
```

By the universal property of the product, a pair of functors f : C → D, g : C' → D' gives rise to
a functor f × g : C × C' → D × D'.

```agda
prod-fun : {C D C' D' : category} → functor C D  → functor C' D' → functor (prod C C') (prod D D')
prod-fun {C} {D} {C'} {D'} f g =
  pair-prod
    { p = t*-base (prod C C') (prod D D')}
    ( comp f (pr₁-prod C C'))
    ( comp g (pr₂-prod C C'))
```

Given two functors f g : T → C × D together with natural isomorphisms pr_C ∘ f ⇒ pr_C ∘ g and
pr_D ∘ f ⇒ pr_D ∘ g, we obtain a natural isomorphism f ⇒ g.

```agda
prod-fun-ext :
  {C D T : category} {f g : functor T (prod C D)} →
  nat-iso (comp (pr₁-prod C D) f) (comp (pr₁-prod C D) g) →
  nat-iso (comp (pr₂-prod C D) f) (comp (pr₂-prod C D) g) →
    nat-iso f g
prod-fun-ext φ ψ = pair-prod {p = t*-step (t*-base _ _) _ _} φ ψ
```

The terminal category is the unit for taking products in the second component. 

```agda
𝟙-prod-r-unit-equiv : (C : category) → equiv (prod C 𝟙) C
equiv-map (𝟙-prod-r-unit-equiv C) = pr₁-prod C 𝟙
sec-map (equiv-sec (𝟙-prod-r-unit-equiv C)) = pair-prod {p = t*-base _ _} (Id C) (𝟙-proj-cat C)
sec-is-sec (equiv-sec (𝟙-prod-r-unit-equiv C)) = Inv (coh₁-prod (Id C) (𝟙-proj-cat C))
ret-map (equiv-ret (𝟙-prod-r-unit-equiv C)) = sec-map (equiv-sec (𝟙-prod-r-unit-equiv C))
ret-is-ret (equiv-ret (𝟙-prod-r-unit-equiv C)) =
  Inv ( prod-fun-ext
    ( comp
      ( comp (Inv (assoc _ _ _)) (l-whisk-fun _ (coh₁-prod _ _)))
      ( comp (Inv (left-unit-law _)) (right-unit-law _)))
    ( 𝟙-proj
      ( [ _ ] (comp (pr₂-prod C 𝟙) (Id (prod C 𝟙))) ⇒
              (comp (pr₂-prod C 𝟙) (comp (pair-prod (Id C) (𝟙-proj-cat C)) (pr₁-prod C 𝟙))))
      { t*-step (t*-base _ _) _ _}) )
```

Products are symmetric.

```agda
prod-symm : (C D : category) → equiv (prod C D) (prod D C)
equiv-map (prod-symm C D) = pair-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D)
sec-map (equiv-sec (prod-symm C D)) = pair-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C)
sec-is-sec (equiv-sec (prod-symm C D)) =
  prod-fun-ext
    ( comp
      ( Inv (right-unit-law (pr₁-prod D C)))
      ( comp
        ( Inv (coh₂-prod {p = t*-base _ _}(pr₂-prod D C) (pr₁-prod D C)))
        ( comp
          ( l-whisk-fun (pair-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C))
            ( Inv (coh₁-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D))))
          ( assoc _ _ _))))
    ( comp
      ( Inv (right-unit-law (pr₂-prod D C)))
      ( comp
        ( Inv (coh₁-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C)))
        ( comp
          ( l-whisk-fun (pair-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C))
            ( Inv (coh₂-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D))))
          ( assoc _ _ _))))
ret-map (equiv-ret (prod-symm C D)) = sec-map (equiv-sec (prod-symm C D))
ret-is-ret (equiv-ret (prod-symm C D)) =
  prod-fun-ext
    ( comp
      ( Inv (right-unit-law (pr₁-prod C D)))
      ( comp
        ( Inv (coh₂-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D)))
        ( comp
          ( l-whisk-fun (pair-prod (pr₂-prod C D) (pr₁-prod C D))
            ( Inv (coh₁-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C))))
          ( assoc _ _ _))))
    ( comp
      ( Inv (right-unit-law (pr₂-prod C D)))
      ( comp
        ( Inv (coh₁-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D)))
        ( comp
          ( l-whisk-fun (pair-prod (pr₂-prod C D) (pr₁-prod C D))
            ( Inv (coh₂-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C))))
          ( assoc _ _ _))))
```

The terminal category is the unit for taking products in the first component. 


```agda
𝟙-prod-l-unit-equiv : (C : category) → equiv (prod 𝟙 C) C
𝟙-prod-l-unit-equiv C = equiv-comp (𝟙-prod-r-unit-equiv C) (prod-symm 𝟙 C)
```