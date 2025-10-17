```agda
{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import CaTT
open import whiskering
open import type-morphisms
open import functoriality-of-whiskering
open import synthetic-categories

module terminal-category where
```

We postulate the existence of a terminal category.

```agda
postulate trmn-cat : cat
postulate trmn-cat-proj : (A : Ty) → (t* A ≡ trmn-cat) → Tm A

trmn-cat-proj-cat : (C : cat) → fun C trmn-cat
trmn-cat-proj-cat C = trmn-cat-proj ([ ⋆ ] C ⇒ trmn-cat) base
```

A category equivalent to the terminal category enjoys the same universal property.

```agda
is-trmn-cat : (C : cat) → Set
is-trmn-cat C = (A : Ty) → (t* A ≡ C) → Tm A

is-trmn-cat-trmn-cat : is-trmn-cat trmn-cat
is-trmn-cat-trmn-cat A p = trmn-cat-proj A p

-- trmn-cat-stable-equiv : (C : cat) → equiv C trmn-cat → is-trmn-cat C
-- trmn-cat-stable-equiv C f A p =
--   morph-base (morph-r-unit C A p)
--     ( morph-base (morph-r-transport (equiv-sec-is-ret f) A p)
--       ( morph-base (morph-r-assoc-inv (equiv-map f) (equiv-sec-map f) A p)
--         ( r-whisk-tm (equiv-sec-map f) _ (t*-r-whisk-ty (equiv-map f) A p)
--           ( trmn-cat-proj (r-whisk-ty (equiv-map f) A p) {t*-r-whisk-ty (equiv-map f) A p}))))

-- trmn-cat-stable-equiv' : (C C' : cat) → equiv C C' → is-trmn-cat C' → is-trmn-cat C
-- trmn-cat-stable-equiv' C C' f P A p =
--   morph-base (morph-r-unit C A p)
--     ( morph-base (morph-r-transport (equiv-sec-is-ret f) A p)
--       ( morph-base (morph-r-assoc-inv (equiv-map f) (equiv-sec-map f) A p)
--         ( r-whisk-tm (equiv-sec-map f) _ (t*-r-whisk-ty (equiv-map f) A p)
--           ( P (r-whisk-ty (equiv-map f) A p) (t*-r-whisk-ty (equiv-map f) A p)))))

trmn-cat-stable-equiv : {C C' : cat} → equiv C C' → is-trmn-cat C → is-trmn-cat C'
trmn-cat-stable-equiv {C} {C'} f P A p =
  ty-morph-base (r-unit-morph C' A p)
    ( ty-morph-base (r-transport-morph (equiv-ret-is-sec f) A p)
      ( ty-morph-base (r-assoc-morph-inv (equiv-sec-map f) (equiv-map f) A p)
      ( r-whisk-tm
        ( equiv-map f)
        ( P (r-whisk-ty (equiv-sec-map f) A p) (t*-r-whisk-ty (equiv-sec-map f) A p))
        ( t*-r-whisk-ty (equiv-sec-map f) A p))))


trmn-cat-stable-equiv-inv : {C C' : cat} → equiv C C' → is-trmn-cat C' → is-trmn-cat C
trmn-cat-stable-equiv-inv {C} f P A p =
  ty-morph-base (r-unit-morph C A p)
    ( ty-morph-base (r-transport-morph (equiv-sec-is-ret f) A p)
      ( ty-morph-base (r-assoc-morph-inv (equiv-map f) (equiv-sec-map f) A p)
        ( r-whisk-tm
          ( equiv-sec-map f)
          ( P (r-whisk-ty (equiv-map f) A p) (t*-r-whisk-ty (equiv-map f) A p))
          ( t*-r-whisk-ty (equiv-map f) A p))))

trmn-cat-stable-equiv-trmn-cat : {C : cat} → equiv C trmn-cat → is-trmn-cat C
trmn-cat-stable-equiv-trmn-cat f = trmn-cat-stable-equiv-inv f is-trmn-cat-trmn-cat 
```