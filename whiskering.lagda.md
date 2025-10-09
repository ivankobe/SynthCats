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
  r-whisk-ty {B = B} {_} {E} g ([ _ ] C ⇒ _) base = [ B ] C ⇒ E
  r-whisk-ty g ([ A ] t ⇒ u) (step p) =
    [ r-whisk-ty g A p ] r-whisk-tm g t p ⇒ r-whisk-tm g u p
    
  postulate
      r-whisk-tm : {B : Ty} {D E : Tm B} {A : Ty} (g : Tm ([ B ] D ⇒ E)) →
                    (α : Tm A) → (p : t* A ≡ D) → Tm (r-whisk-ty g A p)

mutual

  l-whisk-ty : {B : Ty} {C D : Tm B} → (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → s* A ≡ D → Ty
  l-whisk-ty {B = B} {C} {_} f ([ _ ] _ ⇒ E) base = [ B ] C ⇒ E
  l-whisk-ty f ([ A ] t ⇒ u) (step p) =
    [ l-whisk-ty f A p ] l-whisk-tm f t p ⇒ l-whisk-tm f u p

  postulate
    l-whisk-tm : {B : Ty} {C D : Tm B} {A : Ty} (f : Tm ([ B ] C ⇒ D)) →
      (α : Tm A) → (p : s* A ≡ D) → Tm (l-whisk-ty f A p)
```

Whenever we can right-whisker a type A by a term g : [ B ] D ⇒ E, we have t* (g ⋆ A) ≡ E. Dually,
whenever we can left-whisker  a type A by a term f : [ B ] C ⇒ D, we have s* (A ⋆ f) ≡ C.

```agda
t*-r-whisk-ty : {B : Ty} {D E : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → (p : t* A ≡ D) →
  t* (r-whisk-ty g A p) ≡ E
t*-r-whisk-ty _ _ base = base
t*-r-whisk-ty g ([ A ] t ⇒ u) (step p) = step (t*-r-whisk-ty g A p)

s*-l-whisk-ty : {B : Ty} {C D : Tm B} → (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → (p : s* A ≡ D) →
  s* (l-whisk-ty f A p) ≡ C
s*-l-whisk-ty {C = C} _ _ base = base
s*-l-whisk-ty f ([ A ] t ⇒ u) (step p) = step (s*-l-whisk-ty f A p)
```

The codimension-1 composition _∘_ is obtained as a special case of whiskering. Due to the
implementation details, we had make a non-canonical choice: We defined the codimension-1 composition
as a special case of *right* whiskering, but we could also have defined it using left whiskering. In
CaTT, the same pasting context is used in both cases, so no choice has to be made. The workaround is
to assume a (propositional) equality between both composites.

```agda
Comp : {A : Ty} {t u v : Tm A} → Tm ([ A ] u ⇒ v) → Tm ([ A ] t ⇒ u) → Tm ([ A ] t ⇒ v)
Comp {A} {t} {u} g f = r-whisk-tm g f base

Comp' : {A : Ty} {t u v : Tm A} → Tm ([ A ] u ⇒ v) → Tm ([ A ] t ⇒ u) → Tm ([ A ] t ⇒ v)
Comp' {A} {t} {u} {v} g f = l-whisk-tm f g base

postulate
  Comp-coh : {A : Ty} {t u v : Tm A} → (g : Tm ([ A ] u ⇒ v)) → (f : Tm ([ A ] t ⇒ u)) →
    Comp g f ≡ Comp' g f
```

Composition is unital and associative.

```agda
postulate
  Left-unit-law :
    {A : Ty} {a b : Tm A} (f : Tm ([ A ] a ⇒ b)) →
      Tm ([ [ A ] a ⇒ b ] Comp (Id b) f ⇒ f) 

postulate
  Right-unit-law :
    {A : Ty} {a b : Tm A} (f : Tm ([ A ] a ⇒ b)) →
      Tm ([ [ A ] a ⇒ b ] Comp f (Id a) ⇒ f)

postulate
  Assoc : {A : Ty} {a b c d : Tm A} → (f : Tm ([ A ] a ⇒ b)) → (g : Tm ([ A ] b ⇒ c)) →
    (h : Tm ([ A ] c ⇒ d)) → Tm ([ [ A ] a ⇒ d ] Comp h (Comp g f) ⇒ Comp (Comp h g) f)
```

Inverses are indeed inverses

```agda
postulate
  Inv-is-sec :
    {A : Ty} {t u : Tm A} {f g : Tm ([ A ] t ⇒ u)} → (α : Tm ([ _ ] f ⇒ g)) → 
      Tm ( [ _ ] Comp α (Inv α) ⇒ Id g)

postulate
  Inv-is-ret :
    {A : Ty} {t u : Tm A} {f g : Tm ([ A ] t ⇒ u)} → (α : Tm ([ _ ] f ⇒ g)) → 
      Tm ( [ _ ] Comp (Inv α) α ⇒ Id f)
```