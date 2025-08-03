```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import whiskering
open import type-morphisms
open import functoriality-of-whiskering
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

A category equivalent to the terminal category enjoys the same universal property.

```agda
𝟙-stable-equiv : (C : category) → equiv C 𝟙 → (A : Ty) → (t* A ≡ C) → Tm A
𝟙-stable-equiv C f A p =
  morph-base (morph-r-unit C A p)
    ( morph-base (morph-r-transport (equiv-sec-is-ret f) A p)
      ( morph-base (morph-r-assoc-inv (equiv-map f) (equiv-sec-map f) A p)
        ( r-whisk-tm (equiv-sec-map f) _ (t*-r-whisk-ty (equiv-map f) A p)
          ( 𝟙-proj (r-whisk-ty (equiv-map f) A p) {t*-r-whisk-ty (equiv-map f) A p}))))
```