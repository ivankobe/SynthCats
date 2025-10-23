```agda
{-# OPTIONS --guardedness #-}

open import Data.Product.Base

open import CaTT.CaTT
open import CaTT.whiskering
open import CaTT.type-morphisms
open import CaTT.type-equivalences
open import CaTT.functoriality-of-whiskering
open import Synthetic-categories.synthetic-categories
open import Synthetic-categories.whiskering-equivalences
open import Constructions.terminal-category

module Constructions.products where
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
    coh₁-prod : Tm ([ r-whisk-ty (pr₁-prod C D) A p ] f ⇒ r-whisk-tm (pr₁-prod C D) pair-prod p)
  postulate 
    coh₂-prod : Tm ([ r-whisk-ty (pr₂-prod C D) A p ] g ⇒ r-whisk-tm (pr₂-prod C D) pair-prod p)

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
          Tm ([ r-whisk-ty pr₁ A p ] f ⇒ r-whisk-tm pr₁ (pair f g) p)
      coh₂ : {A : Ty} → {p : t* A ≡ P} → (f : Tm (r-whisk-ty pr₁ A p)) →
        (g : Tm (r-whisk-ty pr₂ A p)) →
          Tm ([ r-whisk-ty pr₂ A p ] g ⇒ r-whisk-tm pr₂ (pair f g) p)
  
  open is-prod public
```

The standard product is a product.

```agda
prod-is-prod : {C D : cat} → is-prod C D (prod C D)
pr₁ (prod-is-prod {C} {D}) = pr₁-prod C D
pr₂ (prod-is-prod {C} {D}) = pr₂-prod C D
pair prod-is-prod f g = pair-prod f g
coh₁ prod-is-prod f g = coh₁-prod f g
coh₂ prod-is-prod f g = coh₂-prod f g
```

Products are stable under equivalence.

```agda
prod-stable-equiv' : {C D P P' : cat} → equiv P P' → is-prod C D P → is-prod C D P'
pr₁ (prod-stable-equiv' e p) = Comp (pr₁ p) (equiv-map (equiv-inv e))
pr₂ (prod-stable-equiv' e p) = Comp (pr₂ p) (equiv-map (equiv-inv e))
pair (prod-stable-equiv' e p) {[ A ] t ⇒ u} {q} f g =
  ty-morph-base
    ( ty-morph-is-equiv-inv-map ( r-whisk-equiv-ty-morph-is-equiv (equiv-inv e) ([ A ] t ⇒ u) (q)))
    ( pair p
      ( ty-morph-base (r-assoc-morph (equiv-sec-map e) (pr₁ p) _ q) f)
      ( ty-morph-base (r-assoc-morph (equiv-sec-map e) (pr₂ p) _ q) g))
coh₁ (prod-stable-equiv' e p) {[ A ] t ⇒ u} {q} f g =
  Comp
    ( r-assoc-lax-trans-inv (equiv-map (equiv-inv e)) (pr₁ p) _ q _)
    ( Comp
      ( ty-morph-base
        ( ty-morph-step (r-assoc-morph-inv ( equiv-map (equiv-inv e)) ( pr₁ p) _ q))
        ( Comp
          ( ty-morph-base
            ( ty-morph-step (r-whisk-morph _ (t*-r-whisk-ty (equiv-map (equiv-inv e)) _ q) (pr₁ p)))
            ( ty-morph-is-equiv-inv-is-sec-inv
              ( r-whisk-morph _ q (equiv-map (equiv-inv e)))
              ( r-whisk-equiv-ty-morph-is-equiv (equiv-inv e) _ q)
              ( _)))
          ( coh₁ p 
            ( ty-morph-base (r-assoc-morph (equiv-sec-map e) (pr₁ p) _ q) f)
            ( ty-morph-base (r-assoc-morph (equiv-sec-map e) (pr₂ p) _ q) g)))) 
      ( ty-morph-is-equiv-inv-is-ret-map
        ( r-assoc-morph (equiv-map (equiv-inv e)) (pr₁ p) _ q)
        ( r-assoc-morph-is-equiv (equiv-map (equiv-inv e)) (pr₁ p) _ q) f))
coh₂ (prod-stable-equiv' e p) {[ A ] t ⇒ u} {q} f g =
  Comp
    ( r-assoc-lax-trans-inv (equiv-map (equiv-inv e)) (pr₂ p) _ q _)
    ( Comp
      ( ty-morph-base
        ( ty-morph-step (r-assoc-morph-inv ( equiv-map (equiv-inv e)) ( pr₂ p) _ q))
        ( Comp
          ( ty-morph-base
            ( ty-morph-step (r-whisk-morph _ (t*-r-whisk-ty (equiv-map (equiv-inv e)) _ q) (pr₂ p)))
            ( ty-morph-is-equiv-inv-is-sec-inv
              ( r-whisk-morph _ q (equiv-map (equiv-inv e)))
              ( r-whisk-equiv-ty-morph-is-equiv (equiv-inv e) _ q)
              ( _)))
          ( coh₂ p 
            ( ty-morph-base (r-assoc-morph (equiv-sec-map e) (pr₁ p) _ q) f)
            ( ty-morph-base (r-assoc-morph (equiv-sec-map e) (pr₂ p) _ q) g)))) 
      ( ty-morph-is-equiv-inv-is-ret-map
        ( r-assoc-morph (equiv-map (equiv-inv e)) (pr₂ p) _ q)
        ( r-assoc-morph-is-equiv (equiv-map (equiv-inv e)) (pr₂ p) _ q) g))

prod-stable-equiv : {C D P P' : cat} → equiv P' P → is-prod C D P → is-prod C D P'
prod-stable-equiv e p = prod-stable-equiv' (equiv-inv e) p
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
  snd-prod-ty-tgt C ⋆ D E = base
  snd-prod-ty-tgt C ([ A ] x ⇒ y) t u = step (snd-prod-ty-tgt C A x y)

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
        r-whisk-tm (pr₁-prod C _) (snd-prod-tm C A t u α) (snd-prod-ty-tgt C A t u))
  snd-prod-iso₁ C A t u α = coh₁-prod (snd-prod-comm₁ C A t u) (snd-prod-comm₂ C A t u α)

  snd-prod-iso₂ : (C : cat) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        snd-prod-comm₂ C A t u α ⇒
        r-whisk-tm (pr₂-prod C (tgt A t u)) (snd-prod-tm C A t u α) (snd-prod-ty-tgt C A t u))
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
  fst-prod-ty-tgt C ⋆ D E = base
  fst-prod-ty-tgt C ([ A ] x ⇒ y) t u = step (fst-prod-ty-tgt C A x y)

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
        r-whisk-tm (pr₂-prod _ C) (fst-prod-tm C A t u α) (fst-prod-ty-tgt C A t u))
  fst-prod-iso₂ C A t u α = coh₂-prod _ _

  fst-prod-iso₁ : (C : cat) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        fst-prod-comm₁ C A t u α ⇒
        r-whisk-tm (pr₁-prod (tgt A t u) C) (fst-prod-tm C A t u α) (fst-prod-ty-tgt C A t u))
  fst-prod-iso₁ C A t u α = coh₁-prod _ _
```

For a type A : Ty and a cat D with t* A ≡ D, we have t* (C × A) ≡ C × D.

```agda
t*-fst-prod : (C D : cat) → (A : Ty) → (p : t* A ≡ D) →
  t* fst-prod-ty C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p) ≡ prod D C
t*-fst-prod C D ([ .⋆ ] x ⇒ .D) base = base
t*-fst-prod C D ([ [ .⋆ ] t ⇒ .D ] x ⇒ y) (step base) = step base
t*-fst-prod C D ([ [ A ] t ⇒ u ] x ⇒ y) (step (step p)) =
  step (t*-fst-prod C D ([ A ] t ⇒ u) (step p))
```

By the universal property of the product, a pair of functors f : C → D, g : C' → D' gives rise to
a functor f × g : C × C' → D × D'.

```agda
prod-fun : {C D C' D' : cat} → fun C D  → fun C' D' → fun (prod C C') (prod D D')
prod-fun {C} {D} {C'} {D'} f g =
  pair-prod
    { p = base}
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
prod-fun-ext φ ψ = pair-prod {p = step base} φ ψ
```

The terminal category is the unit for taking products in the second component. 

```agda
trmn-cat-prod-r-unit-equiv : (C : cat) → equiv (prod C trmn-cat) C
equiv-map (trmn-cat-prod-r-unit-equiv C) = pr₁-prod C trmn-cat
sec-map (equiv-sec (trmn-cat-prod-r-unit-equiv C)) =
  pair-prod {p = base} (Id C) (trmn-cat-proj-cat C)
is-sec (equiv-sec (trmn-cat-prod-r-unit-equiv C)) = Inv (coh₁-prod (Id C) (trmn-cat-proj-cat C))
ret-map (equiv-ret (trmn-cat-prod-r-unit-equiv C)) =
  sec-map (equiv-sec (trmn-cat-prod-r-unit-equiv C))
is-ret (equiv-ret (trmn-cat-prod-r-unit-equiv C)) =
  Inv ( prod-fun-ext
    ( Comp
      ( Comp (Inv (Assoc _ _ _)) (l-whisk-fun _ (coh₁-prod _ _)))
      ( Comp (Inv (Left-unit-law _)) (Right-unit-law _)))
    ( trmn-cat-proj
      ( [ _ ] (Comp (pr₂-prod C trmn-cat) (Id (prod C trmn-cat))) ⇒
              (Comp
                ( pr₂-prod C trmn-cat)
                ( Comp (pair-prod (Id C) (trmn-cat-proj-cat C)) (pr₁-prod C trmn-cat))))
      ( step base)) )
```

Products are symmetric.

```agda
prod-symm : (C D : cat) → equiv (prod C D) (prod D C)
equiv-map (prod-symm C D) = pair-prod {p = base} (pr₂-prod C D) (pr₁-prod C D)
sec-map (equiv-sec (prod-symm C D)) = pair-prod {p = base} (pr₂-prod D C) (pr₁-prod D C)
is-sec (equiv-sec (prod-symm C D)) =
  prod-fun-ext
    ( Comp
      ( Inv (Right-unit-law (pr₁-prod D C)))
      ( Comp
        ( Inv (coh₂-prod {p = base}(pr₂-prod D C) (pr₁-prod D C)))
        ( Comp
          ( l-whisk-fun (pair-prod {p = base} (pr₂-prod D C) (pr₁-prod D C))
            ( Inv (coh₁-prod {p = base} (pr₂-prod C D) (pr₁-prod C D))))
          ( Assoc _ _ _))))
    ( Comp
      ( Inv (Right-unit-law (pr₂-prod D C)))
      ( Comp
        ( Inv (coh₁-prod {p = base} (pr₂-prod D C) (pr₁-prod D C)))
        ( Comp
          ( l-whisk-fun (pair-prod {p = base} (pr₂-prod D C) (pr₁-prod D C))
            ( Inv (coh₂-prod {p = base} (pr₂-prod C D) (pr₁-prod C D))))
          ( Assoc _ _ _))))
ret-map (equiv-ret (prod-symm C D)) = sec-map (equiv-sec (prod-symm C D))
is-ret (equiv-ret (prod-symm C D)) =
  prod-fun-ext
    ( Comp
      ( Inv (Right-unit-law (pr₁-prod C D)))
      ( Comp
        ( Inv (coh₂-prod {p = base} (pr₂-prod C D) (pr₁-prod C D)))
        ( Comp
          ( l-whisk-fun (pair-prod (pr₂-prod C D) (pr₁-prod C D))
            ( Inv (coh₁-prod {p = base} (pr₂-prod D C) (pr₁-prod D C))))
          ( Assoc _ _ _))))
    ( Comp
      ( Inv (Right-unit-law (pr₂-prod C D)))
      ( Comp
        ( Inv (coh₁-prod {p = base} (pr₂-prod C D) (pr₁-prod C D)))
        ( Comp
          ( l-whisk-fun (pair-prod (pr₂-prod C D) (pr₁-prod C D))
            ( Inv (coh₂-prod {p = base} (pr₂-prod D C) (pr₁-prod D C))))
          ( Assoc _ _ _))))
```

The terminal category is the unit for taking products in the first and in the second component. 


```agda
trmn-cat-prod-l-unit-equiv : (C : cat) → equiv (prod trmn-cat C) C
trmn-cat-prod-l-unit-equiv C = equiv-comp (trmn-cat-prod-r-unit-equiv C) (prod-symm trmn-cat C)
```