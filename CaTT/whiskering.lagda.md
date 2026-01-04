```agda
open import CaTT.CaTT
```

```agda
module CaTT.whiskering where
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
```

```agda
mutual

  l-whisk-ty : {B : Ty} {C D : Tm B} → (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → s* A ≡ D → Ty
  l-whisk-ty {B = B} {C} {_} f ([ _ ] _ ⇒ E) base = [ B ] C ⇒ E
  l-whisk-ty f ([ A ] t ⇒ u) (step p) =
    [ l-whisk-ty f A p ] l-whisk-tm f t p ⇒ l-whisk-tm f u p
    
  postulate 
    l-whisk-tm' : {B : Ty} {C D : Tm B} {A : Ty} {a a' : Tm A}
      (f : Tm ([ B ] C ⇒ D)) → (α : Tm ([ A ] a ⇒ a')) → (p : s* ([ A ] a ⇒ a') ≡ D) →
        Tm (l-whisk-ty f ([ A ] a ⇒ a') p)

  l-whisk-tm : {B : Ty} {C D : Tm B} {A : Ty}
      (f : Tm ([ B ] C ⇒ D)) → (α : Tm A) → (p : s* A ≡ D) → Tm (l-whisk-ty f A p)
  l-whisk-tm {B} {A = .([ B ] _ ⇒ _)} f α base = r-whisk-tm α f base
  l-whisk-tm {B} {A = .([ _ ] _ ⇒ _)} f α (step p) = l-whisk-tm' f α (step p)
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

The codimension-1 composition _∘_ is obtained as a special case of whiskering. Since in the case of
whiskering a 1-cell by a 1-cell, the left and the right whiskering are definitionally equal (as is
the case in CaTT), it doesn't matter which of the two definitions we use
