```agda
module coherences where
```

```agda
open import Data.Product
```

```agda
mutual
  data Ty : Set where
    ⋆ : Ty
    [_]_⇒_ : (A : Ty) → Tm A → Tm A → Ty

  data Tm : Ty → Set where
```


```agda
mutual

  data is-glob-sum : Set → Set where
  
  data is-glob-sum' : (Γ : {!   !}) → (A : Ty) → (x : Tm A) → Set where
    base : {x : Tm ⋆} → is-glob-sum' (Tm ⋆) ⋆ x
    step : {Γ : {!   !}} {A : Ty} {x y : Tm A} {f : Tm ([ A ] x ⇒ y)} → (is-glob-sum' {!  Γ !} ([ A ] x ⇒ y) {! f  !}) → is-glob-sum' {!   !} {!   !} {!   !}

```