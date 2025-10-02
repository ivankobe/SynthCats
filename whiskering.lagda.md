```agda
{-# OPTIONS --allow-unsolved-metas #-}

open import CaTT
open import Agda.Builtin.Equality
```

```agda
module whiskering where
```

The right/left whiskering of a type/term by a term. The right whiskering is constructed as follows.
Fix a type B : Ty and a term g : [ B ] D ⇒ E. Then, for every type A : Ty with t* A ≡ D, we obtain
a type g ⋆ A : Ty, and for every term α : A we obtain a term g ⋆ α : g ⋆ A. The term g ⋆ α is to be
thought of as the codimension-(dim A - dim B) composite of g and α and g ⋆ A is the type in which
the composite lives. Left whiskering is defined dually. The whiskering of terms is formalized as a
postulate, since in CaTT it is produced as a coherence. 

```agda
mutual

  r-whisk-ty : {B : Ty} {D E : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → t* A ≡ D → Ty
  r-whisk-ty {B = B} {_} {E} g ([ _ ] C ⇒ _) (t*-base C _) = [ B ] C ⇒ E
  r-whisk-ty g ([ A ] t ⇒ u) (t*-step {A = A} p t u) =
    [ r-whisk-ty g A p ] r-whisk-tm g A p t ⇒ r-whisk-tm g A p u
    
  postulate
      r-whisk-tm : {B : Ty} {D E : Tm B} (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → (p : t* A ≡ D) →
                    (α : Tm A) → Tm (r-whisk-ty g A p)

mutual

  l-whisk-ty : {B : Ty} {C D : Tm B} → (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → s* A ≡ D → Ty
  l-whisk-ty {B = B} {C} {_} f ([ _ ] _ ⇒ E) (s*-base _ E) = [ B ] C ⇒ E
  l-whisk-ty f ([ A ] t ⇒ u) (s*-step {A = A} p t u) =
    [ l-whisk-ty f A p ] l-whisk-tm f A p t ⇒ l-whisk-tm f A p u

  postulate
    l-whisk-tm : {B : Ty} {C D : Tm B} (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → (p : s* A ≡ D) →
      (α : Tm A) → Tm (l-whisk-ty f A p)
```

Whenever we can right-whisker a type A by a term g : [ B ] D ⇒ E, we have t* (g ⋆ A) ≡ E. Dually,
whenever we can left-whisker  a type A by a term f : [ B ] C ⇒ D, we have s* (A ⋆ f) ≡ C.

```agda
t*-r-whisk-ty : {B : Ty} {D E : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → (p : t* A ≡ D) →
  t* (r-whisk-ty g A p) ≡ E
t*-r-whisk-ty {E = E} _ _ (t*-base C _) = t*-base C E
t*-r-whisk-ty g ([ A ] t ⇒ u) (t*-step p t u) = t*-step (t*-r-whisk-ty g A p) _ _

s*-l-whisk-ty : {B : Ty} {C D : Tm B} → (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → (p : s* A ≡ D) →
  s* (l-whisk-ty f A p) ≡ C
s*-l-whisk-ty {C = C} _ _ (s*-base _ E) = s*-base C E
s*-l-whisk-ty f ([ A ] t ⇒ u) (s*-step p t u) = s*-step (s*-l-whisk-ty f A p) _ _
```

The codimension-1 composition _∘_ is obtained as a special case of whiskering. Due to the
implementation details, we had make a non-canonical choice: We defined the codimension-1 composition
as a special case of *right* whiskering, but we could also have defined it using left whiskering. In
CaTT, the same pasting context is used in both cases, so no choice has to be made. The workaround is
to assume a (propositional) equality between both composites.

```agda
Comp : {A : Ty} {t u v : Tm A} → Tm ([ A ] u ⇒ v) → Tm ([ A ] t ⇒ u) → Tm ([ A ] t ⇒ v)
Comp {A} {t} {u} g f = r-whisk-tm g ([ A ] t ⇒ u) (t*-base _ _) f

Comp' : {A : Ty} {t u v : Tm A} → Tm ([ A ] u ⇒ v) → Tm ([ A ] t ⇒ u) → Tm ([ A ] t ⇒ v)
Comp' {A} {t} {u} {v} g f = l-whisk-tm f ([ A ] u ⇒ v) (s*-base _ _) g

postulate
  Comp-coh : {A : Ty} {t u v : Tm A} → (g : Tm ([ A ] u ⇒ v)) → (f : Tm ([ A ] t ⇒ u)) →
    Comp g f ≡ Comp' g f
```

Composition is unital and associative.

```agda
postulate
  left-unit-law :
    {A : Ty} {a b : Tm A} (f : Tm ([ A ] a ⇒ b)) →
      Tm ([ [ A ] a ⇒ b ] Comp (Id b) f ⇒ f) 

postulate
  right-unit-law :
    {A : Ty} {a b : Tm A} (f : Tm ([ A ] a ⇒ b)) →
      Tm ([ [ A ] a ⇒ b ] Comp f (Id a) ⇒ f)

postulate
  Assoc : {A : Ty} {a b c d : Tm A} → (f : Tm ([ A ] a ⇒ b)) → (g : Tm ([ A ] b ⇒ c)) →
    (h : Tm ([ A ] c ⇒ d)) → Tm ([ [ A ] a ⇒ d ] Comp h (Comp g f) ⇒ Comp (Comp h g) f)
```