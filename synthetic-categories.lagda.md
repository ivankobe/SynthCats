```agda
{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Product.Base
open import Agda.Builtin.Sigma

open import CaTT
open import whiskering
open import pointwise-homotopies

module synthetic-categories where
```

We want to think of terms of the base type ⋆ as synthetic categories, of terms of type [ ⋆ ] C ⇒ D
as functors, etc.

```agda
cat : Set
cat = Tm ⋆

fun : (C D : cat) → Set
fun C D = Tm ([ ⋆ ] C ⇒ D)

nat-iso : {C D : cat} (F G : fun C D) → Set
nat-iso {C} {D} F G = Tm ([ [ ⋆ ] C ⇒ D ] F ⇒ G)
```

Whiskering of a natural isomorphism by a functor.

```agda
r-whisk-fun : {C D E : cat} {f f' : fun C D} → (g : fun D E) → nat-iso f f' →
  nat-iso (Comp g f) (Comp g f')
r-whisk-fun g φ = r-whisk-tm g _ (t*-step (t*-base _ _) _ _) φ

l-whisk-fun : {C D E : cat} {g g' : fun D E} → (f : fun C D) → nat-iso g g' →
  nat-iso (Comp g f) (Comp g' f)
l-whisk-fun {C} {D} {E} {g} {g'} f ψ rewrite Comp-coh g f rewrite Comp-coh g' f =
    l-whisk-tm f ([ [ ⋆ ] D ⇒ E ] g ⇒ g') (s*-step (s*-base _ _) _ _) ψ
```

A section of a functor f : C → D is given by a functor s : D → C together with a natural isomorphism
f ∘ s → id_D. A retraction of a functor f : C → D is given by a functor s : D → C together with a
natural isomorphism r ∘ f → id_C. Given (synthetic) categories C and D, an equivalence from C to D
is given by a functor f : C → D together with a section and a retracion of f.

```agda
record sec {C D : cat} (f : fun C D) : Set
  where
  field
    sec-map : fun D C
    sec-is-sec : nat-iso (Comp f sec-map) (Id D)

open sec public

record ret {C D : cat} (f : fun C D) : Set
  where
  field
    ret-map : fun D C
    ret-is-ret : nat-iso (Comp ret-map f) (Id C)

open ret public

record equiv (C D : cat) : Set
  where
  field
    equiv-map : fun C D
    equiv-sec : sec equiv-map
    equiv-ret : ret equiv-map

open equiv public

equiv-sec-map : {C D : cat} → equiv C D → fun D C
equiv-sec-map f = sec-map (equiv-sec f)

equiv-ret-map : {C D : cat} → equiv C D → fun D C
equiv-ret-map f = ret-map (equiv-ret f)

equiv-sec-is-sec : {C D : cat} → (f : equiv C D) →
  nat-iso (Comp (equiv-map f) (equiv-sec-map f)) (Id D)
equiv-sec-is-sec f = sec-is-sec (equiv-sec f)

equiv-ret-is-ret : {C D : cat} → (f : equiv C D) →
  nat-iso (Comp (equiv-ret-map f) (equiv-map f)) (Id C)
equiv-ret-is-ret f = ret-is-ret (equiv-ret f)
```

Equivalences can be Composed.

```agda
equiv-comp : {C D E : cat} → equiv D E → equiv C D → equiv C E
equiv-map (equiv-comp g f) = Comp (equiv-map g) (equiv-map f)
sec-map (equiv-sec (equiv-comp g f)) = Comp (equiv-sec-map f) (equiv-sec-map g)
sec-is-sec (equiv-sec (equiv-comp g f)) =
  Comp
    ( equiv-sec-is-sec g)
    ( Comp
      ( r-whisk-fun (equiv-map g) (left-unit-law (equiv-sec-map g)))
      ( Comp
        ( r-whisk-fun (equiv-map g) (l-whisk-fun (equiv-sec-map g) (equiv-sec-is-sec f)))
        ( Comp
          ( r-whisk-fun (equiv-map g) (Assoc (equiv-sec-map g) (equiv-sec-map f) (equiv-map f)))
          ( Inv (Assoc (Comp (equiv-sec-map f) (equiv-sec-map g)) (equiv-map f) (equiv-map g))))))
ret-map (equiv-ret (equiv-comp g f)) = Comp (equiv-ret-map f) (equiv-ret-map g)
ret-is-ret (equiv-ret (equiv-comp g f)) = 
  Comp
    ( equiv-ret-is-ret f)
    ( Comp
      ( r-whisk-fun (equiv-ret-map f) (left-unit-law (equiv-map f)))
      ( Comp
        ( r-whisk-fun (equiv-ret-map f) (l-whisk-fun (equiv-map f) (equiv-ret-is-ret g)))
        ( Comp
          ( r-whisk-fun (equiv-ret-map f) (Assoc (equiv-map f) (equiv-map g) (equiv-ret-map g)))
          ( Inv (Assoc (Comp (equiv-map g) (equiv-map f)) (equiv-ret-map g) (equiv-ret-map f))))))
```

Eqiuivalences are invertible.

```agda
equiv-inv : {C D : cat} → equiv C D → equiv D C
equiv-map (equiv-inv f) = equiv-sec-map f
sec-map (equiv-sec (equiv-inv f)) = equiv-map f
sec-is-sec (equiv-sec (equiv-inv f)) =
  Comp
    ( equiv-ret-is-ret f)
    ( Comp
      ( r-whisk-fun (equiv-ret-map f) (left-unit-law (equiv-map f)))
      ( Comp
        ( r-whisk-fun (equiv-ret-map f) (l-whisk-fun (equiv-map f) (equiv-sec-is-sec f)))
        ( Comp
          ( r-whisk-fun (equiv-ret-map f) (Assoc _ _ _))
          ( Comp
            ( Inv (Assoc _ _ _))
            ( Comp
              ( l-whisk-fun (Comp (equiv-sec-map f) (equiv-map f)) (Inv (equiv-ret-is-ret f)))
              ( Inv (left-unit-law (Comp (equiv-sec-map f) (equiv-map f)))))))))
ret-map (equiv-ret (equiv-inv f)) = equiv-map f
ret-is-ret (equiv-ret (equiv-inv f)) = equiv-sec-is-sec f
```

A section is also a retraction and a retraction is also a section.

```agda
equiv-sec-is-ret : {C D : cat} → (f : equiv C D) →
  nat-iso (Comp (equiv-sec-map f) (equiv-map f)) (Id C)
equiv-sec-is-ret f = equiv-sec-is-sec (equiv-inv f) 

equiv-ret-is-sec : {C D : cat} → (f : equiv C D) →
  nat-iso (Comp (equiv-map f) (equiv-ret-map f)) (Id D)
equiv-ret-is-sec {C} {D} f =
  Comp
    ( equiv-sec-is-sec f)
    ( Comp
      ( r-whisk-fun (equiv-map f) (left-unit-law (equiv-sec-map f)))
      ( Comp
        ( r-whisk-fun (equiv-map f) (l-whisk-fun (equiv-sec-map f) (equiv-ret-is-ret f)))
        ( Comp
          ( r-whisk-fun (equiv-map f) (Assoc _ _ _))
          ( Comp
            ( Inv (Assoc _ _ _))
            ( Comp
              ( r-whisk-fun (Comp (equiv-map f) (equiv-ret-map f)) (Inv (equiv-sec-is-sec f)))
              ( Inv (right-unit-law _)))))))
```

Given a proof p : t* A ≡ C witnessing that dim A > 0 and a term α : A, we obtain a term of type
[ ∂ₜ A p ] ∂ₜ⁻ A p ⇒ ∂ₜ⁺ A p, and vice versa.

```agda
deconstructₜ : (A : Ty) → {C : cat} → (p : t* A ≡ C) → Tm A → Tm ([ ∂ₜ A p ] ∂ₜ⁻ A p ⇒ ∂ₜ⁺ A p)
deconstructₜ .([ ⋆ ] C ⇒ _) (t*-base C _) α = α
deconstructₜ .([ _ ] t ⇒ u) (t*-step p t u) α = α

constructₜ : (A : Ty) → {C : cat} → (p : t* A ≡ C) → Tm ([ ∂ₜ A p ] ∂ₜ⁻ A p ⇒ ∂ₜ⁺ A p) → Tm A
constructₜ .([ ⋆ ] C ⇒ _) (t*-base C _) α = α
constructₜ .([ _ ] t ⇒ u) (t*-step p t u) α = α
```

Operators giving the 0-dimensional source/target of a type.

```agda
src : (A : Ty) → (t u : Tm A) → cat
src ⋆ t u = t
src ([ A ] x ⇒ y) _ _ = src A x y

src-eq : (A : Ty) → (t u : Tm A) → s* [ A ] t ⇒ u ≡ src A t u
src-eq ⋆ C D = s*-base _ _
src-eq ([ A ] x ⇒ y) t u = s*-step (src-eq A x y) t u

tgt : (A : Ty) → (t u : Tm A) → cat
tgt ⋆ t u = u
tgt ([ A ] x ⇒ y) _ _ = tgt A x y

tgt-eq : (A : Ty) → (t u : Tm A) → t* [ A ] t ⇒ u ≡ tgt A t u
tgt-eq ⋆ C D = t*-base _ _
tgt-eq ([ A ] x ⇒ y) t u = t*-step (tgt-eq A x y) t u
```