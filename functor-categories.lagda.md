```agda
{-# OPTIONS --guardedness #-}

open import Data.Product.Base

open import CaTT
open import whiskering
open import functoriality-of-whiskering
open import synthetic-categories
open import terminal-category
open import products

module functor-categories where
```

We postulate the existence of functor categories.

```agda
module functor-category-cons
  (C D : category)
  where

  postulate fun-cat : category
  postulate ev : functor (prod fun-cat C) D

open functor-category-cons public

module functor-category-intro
  {C D : category} {A : Ty} {p : t* A ≡ fun-cat C D}
  (f : Tm
        ( r-whisk-ty
          ( ev C D)
          ( fst-prod-ty C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p))
          ( t*-fst-prod C (fun-cat C D) A p)))
  where

  postulate fun-cat-curry : Tm A
  postulate
    fun-cat-coh :
      Tm ([ _ ]
            f ⇒
            ( r-whisk-tm
              ( ev C D)
              ( fst-prod-ty C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p))
              ( t*-fst-prod C (fun-cat C D) A p)
              ( fst-prod-tm C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p) (deconstructₜ A p fun-cat-curry))))

open functor-category-intro public
```

The universal property of functor categories in the base case.

```agda
fun-cat-curry-base : {T C D : category} → functor (prod T C) D → functor T (fun-cat C D)
fun-cat-curry-base {T} {C} {D} f = fun-cat-curry {C} {D} {[ ⋆ ] T ⇒ fun-cat C D} {p = t*-base _ _} f

fun-cat-coh-base : {T C D : category} → (f : functor (prod T C) D) →
  nat-iso f (comp (ev C D) (pair-prod (comp (fun-cat-curry-base f) (pr₁-prod T C)) (pr₂-prod T C)))
fun-cat-coh-base {T} {C} {D} f = fun-cat-coh {C} {D} {[ ⋆ ] T ⇒ fun-cat C D} {p = t*-base _ _} f
```

We can derive the operation of uncurrying.

```agda
fun-cat-uncurry : {T C D : category} → functor T (fun-cat C D) → functor (prod T C) D
fun-cat-uncurry {T} {C} {D} g = comp (ev C D) (prod-fun g (Id C))
```

The pre/post-composition functors.

```agda
fun-precomp : {C C' D : category} → functor C C' → functor (fun-cat C' D) (fun-cat C D)
fun-precomp {C} {C'} {D} f =
  fun-cat-curry {p = t*-base _ _} (comp (ev C' D) (prod-fun (Id (fun-cat C' D)) f))

fun-postcomp : {C D D' : category} → functor D D' → functor (fun-cat C D) (fun-cat C D')
fun-postcomp {C} {D} {D'} g = fun-cat-curry {p = t*-base _ _} (comp g (ev C D))
```