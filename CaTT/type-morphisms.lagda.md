```agda
{-# OPTIONS --guardedness #-}

open import Function.Base

open import CaTT.CaTT
open import CaTT.whiskering

module CaTT.type-morphisms where
```

Given types A B : Ty, a *type morphism* φ from A to B consists of the following data:
- for every term α : A, a term φ α : B
- for every pair of terms t u : A, a type morphism from [ A ] t ⇒ u to [ B ] φ t ⇒ φ u.

```agda
record ty-morph (A B : Ty) : Set where
  coinductive
  field
    ty-morph-base : Tm A → Tm B
    ty-morph-step :
        {t u : Tm A} → (ty-morph ([ A ] t ⇒ u) ([ B ] (ty-morph-base t) ⇒ (ty-morph-base u)))

open ty-morph public
```

Type morphisms can be composed, and for every type A : Ty,
we have the identity morphism from A to A.

```agda
ty-morph-comp : {A B C : Ty} (ψ : ty-morph B C) → (φ : ty-morph A B) → ty-morph A C
ty-morph-base (ty-morph-comp ψ φ) = λ a → ty-morph-base ψ (ty-morph-base φ a)
ty-morph-step (ty-morph-comp ψ φ) = ty-morph-comp (ty-morph-step ψ) (ty-morph-step φ)

id-ty-morph : (A : Ty) → ty-morph A A
ty-morph-base (id-ty-morph A) = id
ty-morph-step (id-ty-morph A) {t} {u} = id-ty-morph ([ A ] t ⇒ u)
```

Given types A B : Ty and a type morphism φ : A ⇝ B, we define the *shift operator* - for a type A'
with ∂* A' ≡ A, we obtain:
- a type shift-ty φ A'
- a type morphism shift φ A' : A' ⇝ shift-ty φ A'.
Intuitively, shift φ A' is the morphism obtained by applying the coinductive case of the definition
of a type morphism (dim A' - dim A) times.

```agda
mutual
  shift-ty : {A B : Ty} (φ : ty-morph A B) → (A' : Ty) → ∂* A' ≡ A → Ty
  shift-ty {B = B} φ _ base = B
  shift-ty φ ([ A' ] t ⇒ u) (step p) =
    [ (shift-ty φ A' p) ] ty-morph-base (shift φ A' p) t ⇒ ty-morph-base (shift φ A' p) u

  shift : {A B : Ty} (φ : ty-morph A B) → (A' : Ty) → (p : ∂* A' ≡ A) → ty-morph A' (shift-ty φ A' p)
  shift φ _ base = φ
  shift φ ([ A' ] t ⇒ u) (step p) = ty-morph-step (shift φ A' p)
```

The pre/post-composition type morphisms. Given a type X : Ty and a term f : [ B ] C ⇒ D such that
the whiskered type X ⋆ f can be formed, and a type morphism φ : A ⇝ X, we obtain the morphism
φ ⋆ f : A ⇝ X ⋆ f, which we think of as obtained from φ by precomposing with f. By applying this
construction to the identity id_A : A ⇝ A, we obtain the left whiskering morphism f* : A ⇝ A ⋆ f.
The postcomposition morphism and the right whiskering morphism are obtained dually.

```agda
precomp-morph : {A B X : Ty} {C D : Tm B} (φ : ty-morph A X) →
                  (p : s* X ≡ D) → (f : Tm ([ B ] C ⇒ D)) → ty-morph A (l-whisk-ty f X p)
ty-morph-base (precomp-morph φ p f) = λ a → l-whisk-tm f (ty-morph-base φ a) p
ty-morph-step (precomp-morph φ p f) = precomp-morph (shift φ _ _) (step p) f

postcomp-morph : {A B X : Ty} {D E : Tm B} (φ : ty-morph A X) →
                  (p : t* X ≡ D) → (g : Tm ([ B ] D ⇒ E)) → ty-morph A (r-whisk-ty g X p)
ty-morph-base (postcomp-morph φ p g) = λ a → r-whisk-tm g (ty-morph-base φ a) p
ty-morph-step (postcomp-morph φ p g) = postcomp-morph (shift φ _ _) (step p) g

l-whisk-morph : {B : Ty} {C D : Tm B} (X : Ty) → (p : s* X ≡ D)→ (f : Tm ([ B ] C ⇒ D)) →
  ty-morph X (l-whisk-ty f X p)
l-whisk-morph X p f = precomp-morph (id-ty-morph X) p f

r-whisk-morph : {B : Ty} {D E : Tm B} (X : Ty) → (p : t* X ≡ D) → (g : Tm ([ B ] D ⇒ E)) →
  ty-morph X (r-whisk-ty g X p)
r-whisk-morph X p g = postcomp-morph (id-ty-morph X) p g
```