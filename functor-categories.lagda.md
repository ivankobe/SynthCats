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

module functoror-categoryegory-cons
  (C D : category)
  where

  postulate fun-cat : category
  postulate ev : Tm ([ ⋆ ] prod fun-cat C ⇒ D)

open functoror-categoryegory-cons public

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

fun-cat-uncurry : {T C D : category} → functor T (fun-cat C D) → functor (prod T C) D
fun-cat-uncurry {T} {C} {D} g = comp (ev C D) (prod-fun g (Id C))

fun-precomp : {C C' D : category} → functor C C' → functor (fun-cat C' D) (fun-cat C D)
fun-precomp {C} {C'} {D} f =
  fun-cat-curry {p = t*-base _ _} (comp (ev C' D) (prod-fun (Id (fun-cat C' D)) f))

fun-postcomp : {C D D' : category} → functor D D' → functor (fun-cat C D) (fun-cat C D')
fun-postcomp {C} {D} {D'} g = fun-cat-curry {p = t*-base _ _} (comp g (ev C D))

𝟙-prod-r-unit-equiv : (C : category) → equiv (prod C 𝟙) C
𝟙-prod-r-unit-equiv C =
  ( pr₁-prod C 𝟙) ,
  ( pair-prod {p = t*-base _ _} (Id C) (𝟙-proj-cat C) ,
    Inv  (coh₁-prod (Id C) (𝟙-proj-cat C))) ,
  ( pair-prod {p = t*-base _ _} (Id C) (𝟙-proj-cat C) ,
    Inv ( prod-cod-fun-ext
          ( Id (prod C 𝟙))
          ( comp (pair-prod (Id C) (𝟙-proj-cat C)) (pr₁-prod C 𝟙))
          ( comp
            ( comp (Inv (assoc _ _ _)) (l-whisk-fun _ (coh₁-prod _ _)))
            ( comp (Inv (left-unit-law _)) (right-unit-law _)))
          ( 𝟙-proj
            ( [ _ ] (comp (pr₂-prod C 𝟙) (Id (prod C 𝟙))) ⇒
                    (comp (pr₂-prod C 𝟙) (comp (pair-prod (Id C) (𝟙-proj-cat C)) (pr₁-prod C 𝟙))))
            { t*-step (t*-base _ _) _ _}) ))

𝟙-fun-cat-equiv : (C : category) → equiv (fun-cat 𝟙 C) C
𝟙-fun-cat-equiv C = {!   !} , {!   !}
```