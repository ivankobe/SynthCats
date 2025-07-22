```agda
{-# OPTIONS --guardedness #-}

open import Data.Product.Base

open import CaTT
open import whiskering
open import pointwise-homotopies

module synthetic-categories where

category : Set
category = Tm ⋆

functor : (C D : category) → Set
functor C D = Tm ([ ⋆ ] C ⇒ D)

nat-iso : {C D : category} (F G : functor C D) → Set
nat-iso {C} {D} F G = Tm ([ [ ⋆ ] C ⇒ D ] F ⇒ G)

sec : {C D : category} → functor C D → Set
sec {C} {D} f = Σ (functor D C) (λ s → nat-iso (comp f s) (Id D))

ret : {C D : category} → functor C D → Set
ret {C} {D} f = Σ (functor D C) (λ r → nat-iso (comp r f) (Id C))

equiv : (C D : category) → Set
equiv C D = Σ (functor C D) (λ f → sec f × ret f)

deconstructₜ : (A : Ty) → {C : category} → (p : t* A ≡ C) → Tm A → Tm ([ ∂ₜ A p ] ∂ₜ⁻ A p ⇒ ∂ₜ⁺ A p)
deconstructₜ .([ ⋆ ] C ⇒ _) (t*-base C _) α = α
deconstructₜ .([ _ ] t ⇒ u) (t*-step p t u) α = α

constructₜ : (A : Ty) → {C : category} → (p : t* A ≡ C) → Tm ([ ∂ₜ A p ] ∂ₜ⁻ A p ⇒ ∂ₜ⁺ A p) → Tm A
constructₜ .([ ⋆ ] C ⇒ _) (t*-base C _) α = α
constructₜ .([ _ ] t ⇒ u) (t*-step p t u) α = α

src : (A : Ty) → (t u : Tm A) → category
src ⋆ t u = t
src ([ A ] x ⇒ y) _ _ = src A x y

src-eq : (A : Ty) → (t u : Tm A) → s* [ A ] t ⇒ u ≡ src A t u
src-eq ⋆ C D = s*-base _ _
src-eq ([ A ] x ⇒ y) t u = s*-step (src-eq A x y) t u

tgt : (A : Ty) → (t u : Tm A) → category
tgt ⋆ t u = u
tgt ([ A ] x ⇒ y) _ _ = tgt A x y

tgt-eq : (A : Ty) → (t u : Tm A) → t* [ A ] t ⇒ u ≡ tgt A t u
tgt-eq ⋆ C D = t*-base _ _
tgt-eq ([ A ] x ⇒ y) t u = t*-step (tgt-eq A x y) t u

r-whisk-fun : {C D E : category} {f f' : functor C D} → (g : functor D E) → nat-iso f f' →
  nat-iso (comp g f) (comp g f')
r-whisk-fun g φ = r-whisk-tm g _ (t*-step (t*-base _ _) _ _) φ

l-whisk-fun : {C D E : category} {g g' : functor D E} → (f : functor C D) → nat-iso g g' →
  nat-iso (comp g f) (comp g' f)
l-whisk-fun {C} {D} {E} {g} {g'} f ψ rewrite comp-coh g f rewrite comp-coh g' f =
    l-whisk-tm f ([ [ ⋆ ] D ⇒ E ] g ⇒ g') (s*-step (s*-base _ _) _ _) ψ
```