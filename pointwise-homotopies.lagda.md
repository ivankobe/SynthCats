```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import whiskering
open import type-morphisms

module pointwise-homotopies where

ptw-htpy : {A B : Ty} (φ ψ : morph A B) → Set
ptw-htpy {A} {B} φ ψ = (α : Tm A) → Tm ([ B ] (morph-base φ) α ⇒ (morph-base ψ) α)

record ptw-htpy' {A B : Ty} (φ ψ : morph A B) : Set
  where
  coinductive
  field
    ptw-htpy-base : (α : Tm A) → Tm ([ B ] (morph-base φ) α ⇒ (morph-base ψ) α)
    ptw-htpy-step : {α α' : Tm A} →
      ptw-htpy'
        ( morph-postcomp (morph-step φ) (t*-base _ _) (ptw-htpy-base α'))
        ( morph-precomp (morph-step ψ) (s*-base _ _) (ptw-htpy-base α))

open ptw-htpy' public

ptw-htpy-id : {A B : Ty} (φ : morph A B) → ptw-htpy φ φ
ptw-htpy-id φ a = Id (morph-base φ a)

ptw-htpy-comp : {A B : Ty} {φ ψ ξ : morph A B}
  (Ψ : ptw-htpy ψ ξ) → (Φ : ptw-htpy φ ψ) → ptw-htpy φ ξ
ptw-htpy-comp Ψ Φ a = comp (Ψ a) (Φ a)

ptw-htpy-iso : {A B : Ty} {φ ψ : morph A B} (Φ₀ Φ₁ : ptw-htpy φ ψ) → Set
ptw-htpy-iso {A} {B} {φ} {ψ} Φ₀ Φ₁ = (a : Tm A) →
  Tm ([ ([ B ] morph-base φ a ⇒ morph-base ψ a) ] Φ₀ a ⇒ Φ₁ a)

record ptw-htpy-is-equiv {A B : Ty} {φ ψ : morph A B} (Φ : ptw-htpy φ ψ) : Set
  where
  field
    inv : ptw-htpy ψ φ
    inv-is-sec : ptw-htpy-iso {φ = ψ} {ψ} (ptw-htpy-comp {φ = ψ} {φ} {ψ} Φ inv) (ptw-htpy-id ψ)
    inv-is-ret : ptw-htpy-iso {φ = φ} {φ} (ptw-htpy-comp {φ = φ} {ψ} {φ} inv Φ) (ptw-htpy-id φ)

record ptw-htpy-equiv {A B : Ty} (φ ψ : morph A B) : Set
  where
  field
    ptw-htpy-equiv-ptw-htpy : ptw-htpy φ ψ
    ptw-htpy-equiv-is-equiv : ptw-htpy-is-equiv {φ = φ} {ψ} ptw-htpy-equiv-ptw-htpy

record morph-is-equiv {A B : Ty} (φ : morph A B) : Set
  where
  field
    inv : morph B A
    inv-is-sec : ptw-htpy-equiv (morph-comp φ inv) (morph-id B)
    inv-is-ret : ptw-htpy-equiv (morph-id A) (morph-comp inv φ)

record morph-equiv (A B : Ty) : Set
  where
  field
    morph-equiv-morph : morph A B
    morph-equiv-is-equiv : morph-is-equiv morph-equiv-morph
```