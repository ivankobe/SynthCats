```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import synthetic-categories

module terminal-category where
```

We postulate the existence of a terminal category.

```agda
postulate 𝟙 : category
postulate 𝟙-proj : (A : Ty) → {t* A ≡ 𝟙} → Tm A

𝟙-proj-cat : (C : category) → functor C 𝟙
𝟙-proj-cat C = 𝟙-proj ([ ⋆ ] C ⇒ 𝟙) {t*-base _ _}
```