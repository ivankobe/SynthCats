```agda
{-# OPTIONS --guardedness #-}

open import Agda.Builtin.Equality
open import CaTT.CaTT
open import CaTT.whiskering

module CaTT.coherences where

postulate Inv : {A : Ty} {t u : Tm A} {f g : Tm ([ A ] t ⇒ u)} → Tm ([ _ ] f ⇒ g) → Tm ([ _ ] g ⇒ f)

postulate Inv' : {A : Ty} {f g : Tm A} → Tm ([ _ ] f ⇒ g) → Tm ([ _ ] g ⇒ f)

postulate Id : {A : Ty} (a : Tm A) → Tm ([ A ] a ⇒ a)
```

```agda
Comp : {A : Ty} {t u v : Tm A} → Tm ([ A ] u ⇒ v) → Tm ([ A ] t ⇒ u) → Tm ([ A ] t ⇒ v)
Comp {A} {t} {u} {∨} g f = r-whisk-tm {A} {u} {∨} {[ A ] t ⇒ u} g f base

Comp' : {A : Ty} {t u v : Tm A} → Tm ([ A ] u ⇒ v) → Tm ([ A ] t ⇒ u) → Tm ([ A ] t ⇒ v)
Comp' {A} {t} {u} g f = l-whisk-tm f g base

Comp-Eq : {A : Ty} {t u v : Tm A} → (g : Tm ([ A ] u ⇒ v)) → (f : Tm ([ A ] t ⇒ u)) →
  Comp g f ≡ Comp' g f
Comp-Eq g f = refl
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

postulate
  Triangle-identity-right :
    {A : Ty} {t u v : Tm A} → (α : Tm (arrty t u)) → (f : Tm (arrty u v)) →
      Tm
        ( arrty
          ( Comp (Id (Comp f α)) (r-whisk-tm f (Right-unit-law α) (step base)))
          ( Comp (Right-unit-law (Comp f α)) (Assoc (Id t) α f))) 

postulate
  R-whisk-compL : {A : Ty} {x y z : Tm A} {f g h : arr x y} → (φ : arr f g) → (ψ : arr g h) → (k : arr y z) →
    arr ( r-whisk-tm k (Comp ψ φ) (step base))
        ( Comp (r-whisk-tm k ψ (step base)) (r-whisk-tm k φ (step base)))

postulate
  L-whisk-compR : {A : Ty} {x y z : Tm A} {f g h : arr x y} → (k : arr z x) → (φ : arr f g) → (ψ : arr g h) →
    arr ( l-whisk-tm k (Comp ψ φ) (step base))
        ( Comp (l-whisk-tm k ψ (step base)) (l-whisk-tm k φ (step base)))    
```