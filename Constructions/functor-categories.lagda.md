```agda
{-# OPTIONS --guardedness #-}

open import Data.Product.Base

open import CaTT.CaTT
open import CaTT.whiskering
open import CaTT.functoriality-of-whiskering
open import Synthetic-categories.synthetic-categories
open import Constructions.terminal-category
open import Constructions.products

module Constructions.functor-categories where
```

We postulate the existence of fun categories.

```agda
module functor-category-cons
  (C D : cat)
  where

  postulate fun-cat : cat
  postulate ev : fun (prod fun-cat C) D

open functor-category-cons public

module functor-category-intro
  {C D : cat} {A : Ty} {p : t* A ≡ fun-cat C D}
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
              ( fst-prod-tm C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p) (deconstructₜ p fun-cat-curry))
              ( t*-fst-prod C (fun-cat C D) A p)))

open functor-category-intro public
```

The universal property of functor categories in the base case.

```agda
fun-cat-curry-base : {T C D : cat} → fun (prod T C) D → fun T (fun-cat C D)
fun-cat-curry-base {T} {C} {D} f = fun-cat-curry {C} {D} {[ ⋆ ] T ⇒ fun-cat C D} {p = base} f

fun-cat-coh-base : {T C D : cat} → (f : fun (prod T C) D) →
  nat-iso f (Comp (ev C D) (pair-prod (Comp (fun-cat-curry-base f) (pr₁-prod T C)) (pr₂-prod T C)))
fun-cat-coh-base {T} {C} {D} f = fun-cat-coh {C} {D} {[ ⋆ ] T ⇒ fun-cat C D} {p = base} f
```

We can derive the operation of uncurrying.

```agda
fun-cat-uncurry : {T C D : cat} → fun T (fun-cat C D) → fun (prod T C) D
fun-cat-uncurry {T} {C} {D} g = Comp (ev C D) (prod-fun g (Id C))
```

The pre/post-composition functors.

```agda
fun-precomp : {C C' D : cat} → fun C C' → fun (fun-cat C' D) (fun-cat C D)
fun-precomp {C} {C'} {D} f =
  fun-cat-curry {p = base} (Comp (ev C' D) (prod-fun (Id (fun-cat C' D)) f))

fun-postcomp : {C D D' : cat} → fun D D' → fun (fun-cat C D) (fun-cat C D')
fun-postcomp {C} {D} {D'} g = fun-cat-curry {p = base} (Comp g (ev C D))
```