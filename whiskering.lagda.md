```agda
open import CaTT
open import Agda.Builtin.Equality


module whiskering where

mutual

  r-whisk-ty : {B : Ty} {D E : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → t* A ≡ D → Ty
  r-whisk-ty {B = B} {_} {E} g ([ _ ] C ⇒ _) (t*-base C _) = [ B ] C ⇒ E
  r-whisk-ty g ([ A ] t ⇒ u) (t*-step {A = A} p t u) =
    [ r-whisk-ty g A p ] r-whisk-tm g A p t ⇒ r-whisk-tm g A p u
    
  postulate
      r-whisk-tm : {B : Ty} {D E : Tm B} (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → (p : t* A ≡ D) →
                    (α : Tm A) → Tm (r-whisk-ty g A p)

t*-r-whisk-ty : {B : Ty} {D E : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → (p : t* A ≡ D) →
  t* (r-whisk-ty g A p) ≡ E
t*-r-whisk-ty {E = E} _ _ (t*-base C _) = t*-base C E
t*-r-whisk-ty g ([ A ] t ⇒ u) (t*-step p t u) = t*-step (t*-r-whisk-ty g A p) _ _

mutual

  l-whisk-ty : {B : Ty} {C D : Tm B} → (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → s* A ≡ D → Ty
  l-whisk-ty {B = B} {C} {_} f ([ _ ] _ ⇒ E) (s*-base _ E) = [ B ] C ⇒ E
  l-whisk-ty f ([ A ] t ⇒ u) (s*-step {A = A} p t u) =
    [ l-whisk-ty f A p ] l-whisk-tm f A p t ⇒ l-whisk-tm f A p u

  postulate
    l-whisk-tm : {B : Ty} {C D : Tm B} (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → (p : s* A ≡ D) →
      (α : Tm A) → Tm (l-whisk-ty f A p)

s*-l-whisk-ty : {B : Ty} {C D : Tm B} → (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → (p : s* A ≡ D) →
  s* (l-whisk-ty f A p) ≡ C
s*-l-whisk-ty {C = C} _ _ (s*-base _ E) = s*-base C E
s*-l-whisk-ty f ([ A ] t ⇒ u) (s*-step p t u) = s*-step (s*-l-whisk-ty f A p) _ _

comp : {A : Ty} {t u v : Tm A} → Tm ([ A ] u ⇒ v) → Tm ([ A ] t ⇒ u) → Tm ([ A ] t ⇒ v)
comp {A} {t} {u} g f = r-whisk-tm g ([ A ] t ⇒ u) (t*-base _ _) f

postulate
  comp-coh : {A : Ty} {t u v : Tm A} → (g : Tm ([ A ] u ⇒ v)) → (f : Tm ([ A ] t ⇒ u)) →
    (comp g f) ≡ (l-whisk-tm f ([ A ] u ⇒ v) (s*-base _ _) g)

postulate
  left-unit-law :
    {A : Ty} {a b : Tm A} (f : Tm ([ A ] a ⇒ b)) →
      Tm ([ [ A ] a ⇒ b ] comp (Id b) f ⇒ f) 

postulate
  right-unit-law :
    {A : Ty} {a b : Tm A} (f : Tm ([ A ] a ⇒ b)) →
      Tm ([ [ A ] a ⇒ b ] comp f (Id a) ⇒ f)

postulate
  assoc : {A : Ty} {a b c d : Tm A} → (f : Tm ([ A ] a ⇒ b)) → (g : Tm ([ A ] b ⇒ c)) →
    (h : Tm ([ A ] c ⇒ d)) → Tm ([ [ A ] a ⇒ d ] comp h (comp g f) ⇒ comp (comp h g) f)

```