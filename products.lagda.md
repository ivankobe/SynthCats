```agda
{-# OPTIONS --guardedness #-}

open import Data.Product.Base

open import CaTT
open import whiskering
open import synthetic-categories
open import type-morphisms
open import functoriality-of-whiskering
open import terminal-category

module products where
```

We postulate the existence of products of synthetic categories.

```agda
module prod-cons
  (C D : cat)
  where

  postulate prod : cat
  postulate pr₁-prod : fun prod C
  postulate pr₂-prod : fun prod D

open prod-cons public

module prod-intro
  {C D : cat} {A : Ty} {p : t* A ≡ (prod C D)}
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

The predicate of being a product of two categories.

```agda
module _
  (C D : cat)
  where

  record is-prod (P : cat) : Set where
    field
      pr₁ : fun P C
      pr₂ : fun P D
      pair : {A : Ty} → {p : t* A ≡ P} → (f : Tm (r-whisk-ty pr₁ A p)) →
        (g : Tm (r-whisk-ty pr₂ A p)) → Tm A
      coh₁ : {A : Ty} → {p : t* A ≡ P} → (f : Tm (r-whisk-ty pr₁ A p)) →
        (g : Tm (r-whisk-ty pr₂ A p)) →
          Tm ([ r-whisk-ty pr₁ A p ] f ⇒ r-whisk-tm pr₁ A p (pair f g))
      coh₂ : {A : Ty} → {p : t* A ≡ P} → (f : Tm (r-whisk-ty pr₁ A p)) →
        (g : Tm (r-whisk-ty pr₂ A p)) →
          Tm ([ r-whisk-ty pr₂ A p ] g ⇒ r-whisk-tm pr₂ A p (pair f g))
```

The standard product is a product.

```agda
prod-is-prod : {C D : cat} → is-prod C D (prod C D)
is-prod.pr₁ (prod-is-prod {C} {D}) = pr₁-prod C D
is-prod.pr₂ (prod-is-prod {C} {D}) = pr₂-prod C D
is-prod.pair prod-is-prod f g = pair-prod f g
is-prod.coh₁ prod-is-prod f g = coh₁-prod f g
is-prod.coh₂ prod-is-prod f g = coh₂-prod f g
```

Products are stable under equivalence.

```agda

prod-stable-equiv : {C D P P' : cat} → equiv P P' → is-prod C D P → is-prod C D P'
is-prod.pr₁ (prod-stable-equiv e p) = Comp (is-prod.pr₁ p) (equiv-sec-map e)
is-prod.pr₂ (prod-stable-equiv e p) = Comp (is-prod.pr₂ p) (equiv-sec-map e)
is-prod.pair (prod-stable-equiv e p) {A} {q} f g =
  morph-base ( morph-r-unit _ A q)
    ( morph-base (morph-r-transport (equiv-sec-is-sec e) A q)
      ( morph-base (morph-r-assoc-inv (equiv-sec-map e) (equiv-map e) A q)
        ( r-whisk-tm
          ( equiv-map e)
          ( r-whisk-ty (equiv-sec-map e) A q)
          ( t*-r-whisk-ty (equiv-sec-map e) A q)
          ( is-prod.pair p
            ( morph-base (morph-r-assoc (equiv-sec-map e) (is-prod.pr₁ p) A q) f)
            ( morph-base (morph-r-assoc (equiv-sec-map e) (is-prod.pr₂ p) A q) g)))))
is-prod.coh₁ (prod-stable-equiv e p) {A} {q} f g = {!   !}
is-prod.coh₂ (prod-stable-equiv e p) f g = {!   !}

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

  snd-prod-ty : (C : cat) → (A : Ty) → (t u : Tm A) → Ty
  snd-prod-ty C ⋆ D E = [ ⋆ ] prod C D ⇒ prod C E
  snd-prod-ty C ([ A ] x ⇒ y) t u =
    [ snd-prod-ty C A x y ] snd-prod-tm C A x y t ⇒ snd-prod-tm C A x y u

  snd-prod-tm : (C : cat) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm (snd-prod-ty C A t u)
  snd-prod-tm C A t u α = pair-prod (snd-prod-comm₁ C A t u) (snd-prod-comm₂ C A t u α)

  snd-prod-ty-tgt : (C : cat) → (A : Ty) → (t u : Tm A) →
    t* (snd-prod-ty C A t u) ≡ (prod C (tgt A t u))
  snd-prod-ty-tgt C ⋆ D E = t*-base _ _
  snd-prod-ty-tgt C ([ A ] x ⇒ y) t u = t*-step (snd-prod-ty-tgt C A x y) _ _

  snd-prod-comm₁ : (C : cat) → (A : Ty) → (t u : Tm A) →
    Tm (r-whisk-ty (pr₁-prod C (tgt A t u)) (snd-prod-ty C A t u) (snd-prod-ty-tgt C A t u))
  snd-prod-comm₁ C ⋆ D E = pr₁-prod C D
  snd-prod-comm₁ C ([ ⋆ ] x ⇒ y) t u =
    Comp (snd-prod-iso₁ C ⋆ x y u) (Inv (snd-prod-iso₁ C ⋆ x y t))
  snd-prod-comm₁ C ([ [ A ] a ⇒ b ] x ⇒ y) t u =
    Comp (snd-prod-iso₁ C ([ A ] a ⇒ b) x y u) (Inv (snd-prod-iso₁ C ([ A ] a ⇒ b) x y t))

  snd-prod-comm₂ : (C : cat) → (A : Ty) → (t u : Tm A) → (β : Tm ([ A ] t ⇒ u)) →
    Tm (r-whisk-ty (pr₂-prod C (tgt A t u)) (snd-prod-ty C A t u) (snd-prod-ty-tgt C A t u))
  snd-prod-comm₂ C ⋆ D E f = Comp f (pr₂-prod C D)
  snd-prod-comm₂ C ([ ⋆ ] x ⇒ y) f g β =
    Comp
      ( snd-prod-iso₂ C ⋆ x y g)
      ( Comp
        ( snd-prod-coh C f g)
        ( Inv (snd-prod-iso₂ C ⋆ x y f)))
  snd-prod-comm₂ C ([ [ A ] a ⇒ b ] x ⇒ y) f g β =
    Comp
      ( snd-prod-iso₂ C ([ A ] a ⇒ b) x y g)
      ( Comp
        ( snd-prod-coh C f g)
        ( Inv (snd-prod-iso₂ C ([ A ] a ⇒ b) x y f)))

  postulate
    snd-prod-coh : (C : cat) → {A : Ty} → {x y : Tm A} → (f g : Tm ([ A ] x ⇒ y)) →
      Tm ([ _ ] snd-prod-comm₂ C A x y f ⇒ snd-prod-comm₂ C A x y g)

  snd-prod-iso₁ : (C : cat) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        snd-prod-comm₁ C A t u ⇒
        r-whisk-tm (pr₁-prod C _) _ (snd-prod-ty-tgt C A t u) (snd-prod-tm C A t u α))
  snd-prod-iso₁ C A t u α = coh₁-prod (snd-prod-comm₁ C A t u) (snd-prod-comm₂ C A t u α)

  snd-prod-iso₂ : (C : cat) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        snd-prod-comm₂ C A t u α ⇒
        r-whisk-tm (pr₂-prod C (tgt A t u)) _ (snd-prod-ty-tgt C A t u) (snd-prod-tm C A t u α))
  snd-prod-iso₂ C A t u α = coh₂-prod _ _

mutual

  fst-prod-ty : (C : cat) → (A : Ty) → (t u : Tm A) → Ty
  fst-prod-ty C ⋆ D E = [ ⋆ ] prod D C ⇒ prod E C
  fst-prod-ty C ([ A ] x ⇒ y) t u =
    [ fst-prod-ty C A x y ] fst-prod-tm C A x y t ⇒ fst-prod-tm C A x y u

  fst-prod-tm : (C : cat) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm (fst-prod-ty C A t u)
  fst-prod-tm C A t u α = pair-prod (fst-prod-comm₁ C A t u α) (fst-prod-comm₂ C A t u)

  fst-prod-ty-tgt : (C : cat) → (A : Ty) → (t u : Tm A) →
    t* (fst-prod-ty C A t u) ≡ (prod (tgt A t u) C)
  fst-prod-ty-tgt C ⋆ D E = t*-base _ _
  fst-prod-ty-tgt C ([ A ] x ⇒ y) t u = t*-step (fst-prod-ty-tgt C A x y) _ _

  fst-prod-comm₂ : (C : cat) → (A : Ty) → (t u : Tm A) →
    Tm (r-whisk-ty (pr₂-prod (tgt A t u) C) (fst-prod-ty C A t u) (fst-prod-ty-tgt C A t u))
  fst-prod-comm₂ C ⋆ D E = pr₂-prod D C
  fst-prod-comm₂ C ([ ⋆ ] x ⇒ y) t u =
    Comp (fst-prod-iso₂ C ⋆ x y u) (Inv (fst-prod-iso₂ C ⋆ x y t))
  fst-prod-comm₂ C ([ [ A ] a ⇒ b ] x ⇒ y) t u =
    Comp (fst-prod-iso₂ C ([ A ] a ⇒ b) x y u) (Inv (fst-prod-iso₂ C ([ A ] a ⇒ b) x y t))

  fst-prod-comm₁ : (C : cat) → (A : Ty) → (t u : Tm A) → (β : Tm ([ A ] t ⇒ u)) →
    Tm (r-whisk-ty (pr₁-prod (tgt A t u) C) (fst-prod-ty C A t u) (fst-prod-ty-tgt C A t u))
  fst-prod-comm₁ C ⋆ D E f = Comp f (pr₁-prod D C)
  fst-prod-comm₁ C ([ ⋆ ] x ⇒ y) f g β =
    Comp
      ( fst-prod-iso₁ C ⋆ x y g)
      ( Comp
        ( fst-prod-coh C f g)
        ( Inv (fst-prod-iso₁ C ⋆ x y f)))
  fst-prod-comm₁ C ([ [ A ] a ⇒ b ] x ⇒ y) f g β =
    Comp
      ( fst-prod-iso₁ C ([ A ] a ⇒ b) x y g)
      ( Comp
        ( fst-prod-coh C f g)
        ( Inv (fst-prod-iso₁ C ([ A ] a ⇒ b) x y f)))

  postulate
    fst-prod-coh : (C : cat) → {A : Ty} → {x y : Tm A} → (f g : Tm ([ A ] x ⇒ y)) →
      Tm ([ _ ] fst-prod-comm₁ C A x y f ⇒ fst-prod-comm₁ C A x y g)

  fst-prod-iso₂ : (C : cat) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        fst-prod-comm₂ C A t u ⇒
        r-whisk-tm (pr₂-prod _ C) _ (fst-prod-ty-tgt C A t u) (fst-prod-tm C A t u α))
  fst-prod-iso₂ C A t u α = coh₂-prod _ _

  fst-prod-iso₁ : (C : cat) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        fst-prod-comm₁ C A t u α ⇒
        r-whisk-tm (pr₁-prod (tgt A t u) C) _ (fst-prod-ty-tgt C A t u) (fst-prod-tm C A t u α))
  fst-prod-iso₁ C A t u α = coh₁-prod _ _
```

For a type A : Ty and a cat D with t* A ≡ D, we have t* (C × A) ≡ C × D.

```agda
t*-fst-prod : (C D : cat) → (A : Ty) → (p : t* A ≡ D) →
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
prod-fun : {C D C' D' : cat} → fun C D  → fun C' D' → fun (prod C C') (prod D D')
prod-fun {C} {D} {C'} {D'} f g =
  pair-prod
    { p = t*-base (prod C C') (prod D D')}
    ( Comp f (pr₁-prod C C'))
    ( Comp g (pr₂-prod C C'))
```

Given two functors f g : T → C × D together with natural isomorphisms pr_C ∘ f ⇒ pr_C ∘ g and
pr_D ∘ f ⇒ pr_D ∘ g, we obtain a natural isomorphism f ⇒ g.

```agda
prod-fun-ext :
  {C D T : cat} {f g : fun T (prod C D)} →
  nat-iso (Comp (pr₁-prod C D) f) (Comp (pr₁-prod C D) g) →
  nat-iso (Comp (pr₂-prod C D) f) (Comp (pr₂-prod C D) g) →
    nat-iso f g
prod-fun-ext φ ψ = pair-prod {p = t*-step (t*-base _ _) _ _} φ ψ
```

The terminal category is the unit for taking products in the second component. 

```agda
trmn-cat-prod-r-unit-equiv : (C : cat) → equiv (prod C trmn-cat) C
equiv-map (trmn-cat-prod-r-unit-equiv C) = pr₁-prod C trmn-cat
sec-map (equiv-sec (trmn-cat-prod-r-unit-equiv C)) =
  pair-prod {p = t*-base _ _} (Id C) (trmn-cat-proj-cat C)
sec-is-sec (equiv-sec (trmn-cat-prod-r-unit-equiv C)) = Inv (coh₁-prod (Id C) (trmn-cat-proj-cat C))
ret-map (equiv-ret (trmn-cat-prod-r-unit-equiv C)) =
  sec-map (equiv-sec (trmn-cat-prod-r-unit-equiv C))
ret-is-ret (equiv-ret (trmn-cat-prod-r-unit-equiv C)) =
  Inv ( prod-fun-ext
    ( Comp
      ( Comp (Inv (Assoc _ _ _)) (l-whisk-fun _ (coh₁-prod _ _)))
      ( Comp (Inv (left-unit-law _)) (right-unit-law _)))
    ( trmn-cat-proj
      ( [ _ ] (Comp (pr₂-prod C trmn-cat) (Id (prod C trmn-cat))) ⇒
              (Comp
                ( pr₂-prod C trmn-cat)
                ( Comp (pair-prod (Id C) (trmn-cat-proj-cat C)) (pr₁-prod C trmn-cat))))
      { t*-step (t*-base _ _) _ _}) )
```

Products are symmetric.

```agda
prod-symm : (C D : cat) → equiv (prod C D) (prod D C)
equiv-map (prod-symm C D) = pair-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D)
sec-map (equiv-sec (prod-symm C D)) = pair-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C)
sec-is-sec (equiv-sec (prod-symm C D)) =
  prod-fun-ext
    ( Comp
      ( Inv (right-unit-law (pr₁-prod D C)))
      ( Comp
        ( Inv (coh₂-prod {p = t*-base _ _}(pr₂-prod D C) (pr₁-prod D C)))
        ( Comp
          ( l-whisk-fun (pair-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C))
            ( Inv (coh₁-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D))))
          ( Assoc _ _ _))))
    ( Comp
      ( Inv (right-unit-law (pr₂-prod D C)))
      ( Comp
        ( Inv (coh₁-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C)))
        ( Comp
          ( l-whisk-fun (pair-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C))
            ( Inv (coh₂-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D))))
          ( Assoc _ _ _))))
ret-map (equiv-ret (prod-symm C D)) = sec-map (equiv-sec (prod-symm C D))
ret-is-ret (equiv-ret (prod-symm C D)) =
  prod-fun-ext
    ( Comp
      ( Inv (right-unit-law (pr₁-prod C D)))
      ( Comp
        ( Inv (coh₂-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D)))
        ( Comp
          ( l-whisk-fun (pair-prod (pr₂-prod C D) (pr₁-prod C D))
            ( Inv (coh₁-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C))))
          ( Assoc _ _ _))))
    ( Comp
      ( Inv (right-unit-law (pr₂-prod C D)))
      ( Comp
        ( Inv (coh₁-prod {p = t*-base _ _} (pr₂-prod C D) (pr₁-prod C D)))
        ( Comp
          ( l-whisk-fun (pair-prod (pr₂-prod C D) (pr₁-prod C D))
            ( Inv (coh₂-prod {p = t*-base _ _} (pr₂-prod D C) (pr₁-prod D C))))
          ( Assoc _ _ _))))
```

The terminal category is the unit for taking products in the first and in the second component. 


```agda
trmn-cat-prod-l-unit-equiv : (C : cat) → equiv (prod trmn-cat C) C
trmn-cat-prod-l-unit-equiv C = equiv-comp (trmn-cat-prod-r-unit-equiv C) (prod-symm trmn-cat C)
```