```agda
{-# OPTIONS --guardedness #-}

open import CaTT.CaTT
open import CaTT.type-morphisms
open import CaTT.whiskering
open import CaTT.functoriality-of-whiskering
open import Synthetic-categories.synthetic-categories

module Constructions.pullbacks where
```

The datatype of cones over a cospan.

```agda
module _
  {C D E : cat} (f : fun C E) (g : fun D E)
  where

  record cone : Set where
    field
      cone-apex : cat
      cone-fst : fun cone-apex C
      cone-snd : fun cone-apex D
      cone-coh : nat-iso (Comp f cone-fst) (Comp g cone-snd)

  open cone public
```

We postulate the existence of pullbacks.

```agda
module pullback-cons
  {C D E : cat} (f : fun C E) (g : fun D E)
  where

  postulate pb : cone f g

open pullback-cons public
```

The components of a pullback 

```agda
coh-pb-ty : {C D E : cat} {f : fun C E} {g : fun D E} {A : Ty} → (c : cone f g) →
  (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
  (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → Ty
coh-pb-ty {f = f} {g} {A} c p t₁ t₂ =
  [ (r-whisk-ty g (r-whisk-ty (cone-snd c) A p) (t*-r-whisk-ty (cone-snd c) A p)) ]
    ty-morph-base
      ( r-assoc-morph (cone-snd c) g A p)
      ( ty-morph-base
        ( r-transport-morph (cone-coh c) A p)
        ( ty-morph-base
          ( r-assoc-morph-inv (cone-fst c) f A p)
          ( r-whisk-tm f t₁ _)))
    ⇒
    r-whisk-tm g t₂ _


module pullback-intro'
  {C D E : cat} {f : fun C E} {g : fun D E}
  where

  coh₁-pb-ty : (A : Ty) → (c : cone f g) → (p : t* A ≡ (cone-apex c)) →
    (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) → (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → 
    (coh : Tm (coh-pb-ty c p t₁ t₂)) → Tm A → Ty
  coh₁-pb-ty A c p t₁ t₂ coh a = [ r-whisk-ty (cone-fst c) A p ] t₁ ⇒ r-whisk-tm (cone-fst c) a p

  coh₂-pb-ty : (A : Ty) → (c : cone f g) → (p : t* A ≡ (cone-apex c)) →
    (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) → (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → 
    (coh : Tm (coh-pb-ty c p t₁ t₂)) → Tm A → Ty
  coh₂-pb-ty A c p t₁ t₂ coh a = [ r-whisk-ty (cone-snd c) A p ] t₂ ⇒ r-whisk-tm (cone-snd c) a p

  coh₃-pb-ty : (A : Ty) → (c : cone f g) → (p : t* A ≡ (cone-apex c)) →
    (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) → (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → 
    (coh : Tm (coh-pb-ty c p t₁ t₂)) → (a : Tm A) → Tm (coh₁-pb-ty A c p t₁ t₂ coh a) → 
    Tm (coh₂-pb-ty A c p t₁ t₂ coh a) → Ty
  coh₃-pb-ty ([ A ] x ⇒ y) c p t₁ t₂ coh a coh₁ coh₂ = 
    [ _ ]
    Comp (r-whisk-tm g coh₂ (step (t*-r-whisk-ty _ _ _))) coh ⇒
    Comp
      ( Comp
        ( r-assoc-lax-trans (cone-snd c) g _ p a)
        ( ty-morph-base
          ( shift (r-assoc-morph (cone-snd c) g _ p) _ (step base))
          ( Comp
            ( r-transport-lax-trans (cone-coh c) _ p a)
              ( ty-morph-base
                ( shift (r-transport-morph (cone-coh c) _ p) _ (step base))
                ( r-assoc-lax-trans-inv (cone-fst c) f _ p a)))))
      ( ty-morph-base
        ( shift
          ( ty-morph-comp
            ( ty-morph-comp
              ( r-assoc-morph _ g _ _)
              ( r-transport-morph (cone-coh c) _ _))
            ( r-assoc-morph-inv _ f _ _))
          _ 
          ( step base))
        ( r-whisk-tm f coh₁ (step (t*-r-whisk-ty (cone-fst c) _ p))))

open pullback-intro' public
```

We postulate that pullbacks satisfy a universal property.

```agda
module pullback-intro
  {C D E : cat} {f : fun C E} {g : fun D E} (A : Ty)
  (p : t* A ≡ (cone-apex (pb f g))) (t₁ : Tm (r-whisk-ty (cone-fst (pb f g)) A p))
  (t₂ : Tm (r-whisk-ty (cone-snd (pb f g)) A p)) (coh : Tm (coh-pb-ty (pb f g) p t₁ t₂))
  where

  postulate pair-pb : Tm A
  postulate coh₁-pb : Tm (coh₁-pb-ty A (pb f g) p t₁ t₂ coh pair-pb)
  postulate coh₂-pb : Tm (coh₂-pb-ty A (pb f g) p t₁ t₂ coh pair-pb)
  postulate coh₃-pb : Tm (coh₃-pb-ty A (pb f g) p t₁ t₂ coh pair-pb coh₁-pb coh₂-pb)

open pullback-intro public
```

The predicate of a cone being a pullback 

```agda
module _
  {C D E : cat} (f : fun C E) (g : fun D E)
  where

  record is-pb (c : cone f g) : Set where
    field
      pair :
        (A : Ty) → (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) →
          Tm A
      coh₁ :
        (A : Ty) → (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) → 
          Tm (coh₁-pb-ty A c p t₁ t₂ coh (pair A p t₁ t₂ coh))
      coh₂ :
        (A : Ty) → (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) → 
          Tm (coh₂-pb-ty A c p t₁ t₂ coh (pair A p t₁ t₂ coh))
      coh₃ :
        (A : Ty) → (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) → 
          Tm (coh₃-pb-ty A c p t₁ t₂ coh (pair A p t₁ t₂ coh) (coh₁ A p t₁ t₂ _) (coh₂ A p t₁ t₂ _))
```

Pullbacks are stable under equivalence.