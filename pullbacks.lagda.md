```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import type-morphisms
open import whiskering
open import functoriality-of-whiskering
open import synthetic-categories

module pullbacks where
```

The datatype of cones over a cospan.

```agda
module _
  {C D E : cat} (f : fun C E) (g : fun D E)
  where

  record cone : Set where
    field
      apex : cat
      fst : fun apex C
      snd : fun apex D
      coh : nat-iso (Comp f fst) (Comp g snd)
```

We postulate the existence of pullbacks.

```agda
module pullback-cons
  {C D E : cat} (f : fun C E) (g : fun D E)
  where

  postulate pb : cone f g

open pullback-cons public
```

The components of a pullback cone.

```agda
coh-pb-ty : {C D E : cat} {f : fun C E} {g : fun D E} {A : Ty} → (c : cone f g) →
  (p : t* A ≡ (cone.apex c)) → (t₁ : Tm (r-whisk-ty (cone.fst c) A p)) →
  (t₂ : Tm (r-whisk-ty (cone.snd c) A p)) → Ty
coh-pb-ty {f = f} {g} {A} c p t₁ t₂ =
  [ (r-whisk-ty g (r-whisk-ty (cone.snd c) A p) (t*-r-whisk-ty (cone.snd c) A p)) ]
    morph-base
      ( morph-r-assoc (cone.snd c) g A p)
      ( morph-base
        ( morph-r-transport (cone.coh c) A p)
        ( morph-base
          ( morph-r-assoc-inv (cone.fst c) f A p)
          ( r-whisk-tm f _ _ t₁)))
    ⇒
    r-whisk-tm g _ _ t₂


module pullback-intro'
  {C D E : cat} {f : fun C E} {g : fun D E}
  where

  coh₁-pb-ty : (A : Ty) → (c : cone f g) → (p : t* A ≡ (cone.apex c)) →
    (t₁ : Tm (r-whisk-ty (cone.fst c) A p)) → (t₂ : Tm (r-whisk-ty (cone.snd c) A p)) → 
    (coh : Tm (coh-pb-ty c p t₁ t₂)) → Tm A → Ty
  coh₁-pb-ty A c p t₁ t₂ coh a = [ r-whisk-ty (cone.fst c) A p ] t₁ ⇒ r-whisk-tm (cone.fst c) A p a

  coh₂-pb-ty : (A : Ty) → (c : cone f g) → (p : t* A ≡ (cone.apex c)) →
    (t₁ : Tm (r-whisk-ty (cone.fst c) A p)) → (t₂ : Tm (r-whisk-ty (cone.snd c) A p)) → 
    (coh : Tm (coh-pb-ty c p t₁ t₂)) → Tm A → Ty
  coh₂-pb-ty A c p t₁ t₂ coh a = [ r-whisk-ty (cone.snd c) A p ] t₂ ⇒ r-whisk-tm (cone.snd c) A p a

  coh₃-pb-ty : (A : Ty) → (c : cone f g) → (p : t* A ≡ (cone.apex c)) →
    (t₁ : Tm (r-whisk-ty (cone.fst c) A p)) → (t₂ : Tm (r-whisk-ty (cone.snd c) A p)) → 
    (coh : Tm (coh-pb-ty c p t₁ t₂)) → (a : Tm A) → Tm (coh₁-pb-ty A c p t₁ t₂ coh a) → 
    Tm (coh₂-pb-ty A c p t₁ t₂ coh a) → Ty
  coh₃-pb-ty A c p t₁ t₂ coh a coh₁ coh₂ =
    [ _ ]
    Comp (r-whisk-tm g _ (t*-step (t*-r-whisk-ty _ _ _) _ _) coh₂) coh ⇒
    Comp
      ( Comp
        ( ptw-htpy-r-assoc (cone.snd c) g A p a)
        ( morph-base
          ( shift (morph-r-assoc (cone.snd c) g A p) _ (∂*-step _ _ _ (∂*-base _)))
          ( Comp
            ( ptw-htpy-r-transport (cone.coh c) A p a)
              ( morph-base
                ( shift (morph-r-transport (cone.coh c) A p) _ (∂*-step _ _ _ (∂*-base _)))
                ( ptw-htpy-r-assoc-inv (cone.fst c) f A p a)))))
      ( morph-base
        ( shift
          ( morph-comp
            ( morph-comp
              ( morph-r-assoc _ g _ _)
              ( morph-r-transport (cone.coh c) _ _))
            ( morph-r-assoc-inv _ f _ _))
          _ 
          ( ∂*-step _ _ _ (∂*-base _)))
        ( r-whisk-tm f _ (t*-step (t*-r-whisk-ty (cone.fst c) A p) _ _) coh₁))

open pullback-intro' public
```

We postulate that pullbacks satisfy a universal property.

```agda
module pullback-intro
  {C D E : cat} {f : fun C E} {g : fun D E} (A : Ty)
  (p : t* A ≡ (cone.apex (pb f g))) (t₁ : Tm (r-whisk-ty (cone.fst (pb f g)) A p))
  (t₂ : Tm (r-whisk-ty (cone.snd (pb f g)) A p)) (coh : Tm (coh-pb-ty (pb f g) p t₁ t₂))
  where

  postulate pair-pb : Tm A
  postulate coh₁-pb : Tm (coh₁-pb-ty A (pb f g) p t₁ t₂ coh pair-pb)
  postulate coh₂-pb : Tm (coh₂-pb-ty A (pb f g) p t₁ t₂ coh pair-pb)
  postulate coh₃-pb : Tm (coh₃-pb-ty A (pb f g) p t₁ t₂ coh pair-pb coh₁-pb coh₂-pb)

open pullback-intro public
```

The predicate of a cone being a pullback cone.

```agda
module _
  {C D E : cat} (f : fun C E) (g : fun D E)
  where

  record is-pb (c : cone f g) : Set where
    field
      pair :
        (A : Ty) → (p : t* A ≡ (cone.apex c)) → (t₁ : Tm (r-whisk-ty (cone.fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone.snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) →
          Tm A
      coh₁ :
        (A : Ty) → (p : t* A ≡ (cone.apex c)) → (t₁ : Tm (r-whisk-ty (cone.fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone.snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) → 
          Tm (coh₁-pb-ty A c p t₁ t₂ coh (pair A p t₁ t₂ coh))
      coh₂ :
        (A : Ty) → (p : t* A ≡ (cone.apex c)) → (t₁ : Tm (r-whisk-ty (cone.fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone.snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) → 
          Tm (coh₂-pb-ty A c p t₁ t₂ coh (pair A p t₁ t₂ coh))
      coh₃ :
        (A : Ty) → (p : t* A ≡ (cone.apex c)) → (t₁ : Tm (r-whisk-ty (cone.fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone.snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) → 
          Tm (coh₃-pb-ty A c p t₁ t₂ coh (pair A p t₁ t₂ coh) (coh₁ A p t₁ t₂ _) (coh₂ A p t₁ t₂ _))
```

Pullbacks are stable under equivalence.