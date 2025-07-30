```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import type-morphisms
open import whiskering
open import functoriality-of-whiskering
open import synthetic-categories

module pullbacks where
```

We postulate the existence of pullbacks.

```agda
module pullback-cons
  {C D E : category} (f : functor C E) (g : functor D E)
  where

  postulate pb : category
  postulate pr₁-pb : functor pb C
  postulate pr₂-pb : functor pb D
  postulate coh-univ : nat-iso (comp f pr₁-pb) (comp g pr₂-pb)

open pullback-cons public

module pullback-intro
  {C D E : category} (f : functor C E) (g : functor D E) (A : Ty) (p : t* A ≡ (pb f g))
  (t₁ : Tm (r-whisk-ty (pr₁-pb f g) A p)) (t₂ : Tm (r-whisk-ty (pr₂-pb f g) A p))
  (coh : Tm
            ([ (r-whisk-ty g (r-whisk-ty (pr₂-pb f g) A p) (t*-r-whisk-ty (pr₂-pb f g) A p)) ]
              morph-base
                ( morph-r-assoc (pr₂-pb f g) g A p)
                ( morph-base
                  ( morph-r-transport (coh-univ f g) A p)
                  ( morph-base
                    ( morph-r-assoc-inv (pr₁-pb f g) f A p)
                    ( r-whisk-tm f _ _ t₁)))
              ⇒
              r-whisk-tm g _ _ t₂))
  where

  postulate pair-pb : Tm A
  postulate coh₁-pb : Tm ([ r-whisk-ty (pr₁-pb f g) A p ] t₁ ⇒ r-whisk-tm (pr₁-pb f g) A p pair-pb)
  postulate coh₂-pb : Tm ([ r-whisk-ty (pr₂-pb f g) A p ] t₂ ⇒ r-whisk-tm (pr₂-pb f g) A p pair-pb)

  f⋆φC : Tm ([ _ ] _ ⇒ _)
  f⋆φC = r-whisk-tm f _ (t*-step (t*-r-whisk-ty (pr₁-pb f g) A p) _ _) coh₁-pb

  w : morph
        ( r-whisk-ty f (r-whisk-ty (pr₁-pb f g) A p) (t*-r-whisk-ty (pr₁-pb f g) _ _))
        ( r-whisk-ty g (r-whisk-ty (pr₂-pb f g) A p) (t*-r-whisk-ty (pr₂-pb f g) _ _))
  w = morph-comp
        ( morph-comp
          ( morph-r-assoc _ g _ _)
          ( morph-r-transport (coh-univ f g) _ _))
        ( morph-r-assoc-inv _ f _ _)

  w⟨f⋆φC⟩ : Tm ([ _ ] _ ⇒ _)
  w⟨f⋆φC⟩ = morph-base (shift w _ (∂*-step _ _ _ (∂*-base _))) f⋆φC

  can : Tm ([ r-whisk-ty g (r-whisk-ty (pr₂-pb f g) A p) (t*-r-whisk-ty (pr₂-pb f g) A p) ] _ ⇒ _)
  can =
    comp
      ( ptw-htpy-r-assoc (pr₂-pb f g) g A p pair-pb)
      ( morph-base
        ( shift (morph-r-assoc (pr₂-pb f g) g A p) _ (∂*-step _ _ _ (∂*-base _)))
        ( comp
          ( ptw-htpy-r-transport (coh-univ f g) A p pair-pb)
            ( morph-base
              ( shift (morph-r-transport (coh-univ f g) A p) _ (∂*-step _ _ _ (∂*-base _)))
              ( ptw-htpy-r-assoc-inv (pr₁-pb f g) f A p pair-pb))))

  postulate
    coh₃-pb :
      Tm ([ _ ]
          comp (r-whisk-tm g _ (t*-step (t*-r-whisk-ty _ _ _) _ _) coh₂-pb) coh ⇒
          comp can w⟨f⋆φC⟩)
```