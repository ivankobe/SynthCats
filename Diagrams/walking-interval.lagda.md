```agda
{-# OPTIONS --guardedness #-}

open import synthetic-categories
open import terminal-category 

module walking-interval where

postulate [1] : category
postulate d₀ : functor 𝟙 [1]
postulate d₁ : functor 𝟙 [1]
```