```agda
{-# OPTIONS --guardedness #-}

open import Function.Base

open import CaTT
open import whiskering

module type-morphisms where
```

Given types A B : Ty, a *type morphism* φ from A to B consists of the following data:
- for every term α : A, a term φ α : B
- for every pair of terms t u : A, a type morphism from [ A ] t ⇒ u to [ B ] φ t ⇒ φ u.

```agda
record morph (A B : Ty) : Set
  where
  coinductive
  field
    morph-base : Tm A → Tm B
    morph-step :
      {t u : Tm A} → (morph ([ A ] t ⇒ u) ([ B ] (morph-base t) ⇒ (morph-base u)))

open morph public
```

Type morphisms can be composed, and for every type A : Ty,
we have the identity morphism from A to A.

```agda
morph-comp : {A B C : Ty} (ψ : morph B C) → (φ : morph A B) → morph A C
morph-base (morph-comp ψ φ) = λ a → morph-base ψ (morph-base φ a)
morph-step (morph-comp ψ φ) = morph-comp (morph-step ψ) (morph-step φ)

morph-id : (A : Ty) → morph A A
morph-base (morph-id A) = id
morph-step (morph-id A) {t} {u} = morph-id ([ A ] t ⇒ u)
```

Given types A B : Ty and a type morphism φ : A ⇝ B, we define the *shift operator* - for a type A'
with ∂* A' ≡ A, we obtain:
- a type shift-ty φ A'
- a type morphism shift φ A' : A' ⇝ shift-ty φ A'.
Intuitively, shift φ A' is the morphism obtained by applying the coinductive case of the definition
of a type morphism (dim A' - dim A) times.

```agda
mutual
  shift-ty : {A B : Ty} (φ : morph A B) → (A' : Ty) → ∂* A' ≡ A → Ty
  shift-ty {B = B} φ _ (∂*-base _) = B
  shift-ty φ ([ A' ] t ⇒ u) (∂*-step t u _ p) =
    [ (shift-ty φ A' p) ] morph-base (shift φ A' p) t ⇒ morph-base (shift φ A' p) u

  shift : {A B : Ty} (φ : morph A B) → (A' : Ty) → (p : ∂* A' ≡ A) → morph A' (shift-ty φ A' p)
  shift φ _ (∂*-base _) = φ
  shift φ ([ A' ] t ⇒ u) (∂*-step t u _ p) = morph-step (shift φ A' p)
```

The pre/post-composition type morphisms. Given a type X : Ty and a term f : [ B ] C ⇒ D such that
the whiskered type X ⋆ f can be formed, and a type morphism φ : A ⇝ X, we obtain the morphism
φ ⋆ f : A ⇝ X ⋆ f, which we think of as obtained from φ by precomposing with f. By applying this
construction to the identity id_A : A ⇝ A, we obtain the left whiskering morphism f* : A ⇝ A ⋆ f.
The postcomposition morphism and the right whiskering morphism are obtained dually.

```agda
morph-precomp : {A B X : Ty} {C D : Tm B} (φ : morph A X) →
                  (p : s* X ≡ D) → (f : Tm ([ B ] C ⇒ D)) → morph A (l-whisk-ty f X p)
morph-base (morph-precomp φ p f) = λ a → l-whisk-tm f _ p (morph-base φ a)
morph-step (morph-precomp φ p f) = morph-precomp (shift φ _ _) (s*-step p _ _) f

morph-postcomp : {A B X : Ty} {D E : Tm B} (φ : morph A X) →
                  (p : t* X ≡ D) → (g : Tm ([ B ] D ⇒ E)) → morph A (r-whisk-ty g X p)
morph-base (morph-postcomp φ p g) = λ a → r-whisk-tm g _ p (morph-base φ a)
morph-step (morph-postcomp φ p g) = morph-postcomp (shift φ _ _) (t*-step p _ _) g

l-whisk-morph : {B : Ty} {C D : Tm B} (X : Ty) → (p : s* X ≡ D)→ (f : Tm ([ B ] C ⇒ D)) →
  morph X (l-whisk-ty f X p)
l-whisk-morph X p f = morph-precomp (morph-id X) p f

r-whisk-morph : {B : Ty} {D E : Tm B} (X : Ty) → (p : t* X ≡ D) → (g : Tm ([ B ] D ⇒ E)) →
  morph X (r-whisk-ty g X p)
r-whisk-morph X p g = morph-postcomp (morph-id X) p g
```