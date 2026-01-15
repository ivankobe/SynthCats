```agda
{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import CaTT.CaTT
open import CaTT.coherences
open import CaTT.whiskering
open import CaTT.type-morphisms
open import CaTT.lax-transformations
open import CaTT.functoriality-of-whiskering
open import CaTT.commutative-squares-pasting
open import Synthetic-categories.synthetic-categories

module Constructions.displayed-types where


module _
  {C D E : cat} {f : fun C E} {g : fun D E}
  where

  record dtype : Set where
    field
      tyL : Ty
      tyA : Ty
      tyR : Ty
      morL : ty-morph tyL tyA
      morR : ty-morph tyR tyA
  open dtype public

  record dterm (A : dtype) : Set where
    field
      tmL : Tm (tyL A)
      tmA : Tm (tyA A)
      tmR : Tm (tyR A)
      isoL : Tm (arrty (ty-morph-base (morL A) tmL) tmA)
      isoR : Tm (arrty (ty-morph-base (morR A) tmR) tmA)
  open dterm public

  cone : (T : cat) → dtype
  tyL (cone T)  = arrty T C
  tyA (cone T)  = arrty T E
  tyR (cone T)  = arrty T D
  morL (cone T) = r-whisk-morph _ base f
  morR (cone T) = r-whisk-morph _ base g

  morph-dtype : {A : dtype} (a b : dterm A) → dtype
  tyL (morph-dtype a b)  = arrty (tmL a) (tmL b)
  tyA (morph-dtype a b)  = arrty (tmA a) (tmA b)
  tyR (morph-dtype a b)  = arrty (tmR a) (tmR b)
  morL (morph-dtype {A} a b) =
    ty-morph-comp
      ( ty-morph-comp
        ( l-whisk-morph _ base (Inv' (isoL a)))
        ( r-whisk-morph _ base (isoL b)))
      ( ty-morph-step (morL A))
  morR (morph-dtype {A} a b) =
    ty-morph-comp
      ( ty-morph-comp
        ( l-whisk-morph _ base (Inv' (isoR a)))
        ( r-whisk-morph _ base (isoR b)))
      ( ty-morph-step (morR A))

  cone-iso : {T : cat} (c c' : dterm (cone T)) → dtype
  cone-iso = morph-dtype 

  cone-iso-iso : {T : cat} {c c' : dterm (cone T)} (φ φ' : dterm (cone-iso c c')) → dtype
  cone-iso-iso = morph-dtype

  record dtype-morph (A B : dtype) : Set where
    field
      Lmor : ty-morph (tyL A) (tyL B)
      Amor : ty-morph (tyA A) (tyA B)
      Rmor : ty-morph (tyR A) (tyR B)
      Llax : lax-trans (ty-morph-comp (morL B) Lmor) (ty-morph-comp Amor (morL A))
      Rlax : lax-trans (ty-morph-comp (morR B) Rmor) (ty-morph-comp Amor (morR A))
  open dtype-morph public

  id-dtype-morph : (A : dtype) → dtype-morph A A
  Lmor (id-dtype-morph A) = id-ty-morph _
  Amor (id-dtype-morph A) = id-ty-morph _
  Rmor (id-dtype-morph A) = id-ty-morph _
  Llax (id-dtype-morph A) = λ _ → Id _
  Rlax (id-dtype-morph A) = λ _ → Id _

  dtype-morph-comp : {A B C : dtype} (ψ : dtype-morph B C) → (φ : dtype-morph A B) → dtype-morph A C
  Lmor (dtype-morph-comp ψ φ)   = ty-morph-comp (Lmor ψ) (Lmor φ)
  Amor (dtype-morph-comp ψ φ)   = ty-morph-comp (Amor ψ) (Amor φ)
  Rmor (dtype-morph-comp ψ φ)   = ty-morph-comp (Rmor ψ) (Rmor φ)
  Llax (dtype-morph-comp ψ φ) α =
    Comp
      ( ty-morph-base (ty-morph-step (Amor ψ)) (Llax φ α))
      ( Llax ψ (ty-morph-base (Lmor φ) α))
  Rlax (dtype-morph-comp ψ φ) α =
    Comp
      ( ty-morph-base (ty-morph-step (Amor ψ)) (Rlax φ α))
      ( Rlax ψ (ty-morph-base (Rmor φ) α))

  whisk-cone-dtype-morph : {S T : cat} (s : fun S T) → dtype-morph (cone T) (cone S)
  Lmor (whisk-cone-dtype-morph s)   = l-whisk-morph _ base s
  Amor (whisk-cone-dtype-morph s)   = l-whisk-morph _ base s
  Rmor (whisk-cone-dtype-morph s)   = l-whisk-morph _ base s
  Llax (whisk-cone-dtype-morph s) α = Assoc s α f
  Rlax (whisk-cone-dtype-morph s) α = Assoc s α g

  record dtype-lax-trans {A B : dtype} (φ ψ : dtype-morph A B) : Set where
    field
      laxL  : lax-trans (Lmor φ) (Lmor ψ)
      laxA  : lax-trans (Amor φ) (Amor ψ)
      laxR  : lax-trans (Rmor φ) (Rmor ψ)
      3isoL : lax-3-iso {_} {_}
        { ty-morph-comp (morL B) (Lmor φ)}
        { ty-morph-comp (Amor ψ) (morL A)} 
        ( lax-trans-comp {_} {_}
          { ty-morph-comp (morL B) (Lmor φ)}
          { ty-morph-comp (morL B) (Lmor ψ)}
          { ty-morph-comp (Amor ψ) (morL A)}
          ( Llax ψ)
          ( r-whisk-lax-trans {_} {_} {_} {Lmor φ} {Lmor ψ} laxL (morL B)))
        ( lax-trans-comp {_} {_}
          { ty-morph-comp (morL B) (Lmor φ)}
          { ty-morph-comp (Amor φ) (morL A)}
          { ty-morph-comp (Amor ψ) (morL A)}
          ( l-whisk-lax-trans {_} {_} {_} {Amor φ} {Amor ψ} (morL A) laxA)
          ( Llax φ))
      3isoR : lax-3-iso {_} {_}
        { ty-morph-comp (morR B) (Rmor φ)}
        { ty-morph-comp (Amor ψ) (morR A)}
        ( lax-trans-comp {_} {_}
          { ty-morph-comp (morR B) (Rmor φ)}
          { ty-morph-comp (morR B) (Rmor ψ)}
          { ty-morph-comp (Amor ψ) (morR A)}
          ( Rlax ψ)
          ( r-whisk-lax-trans {_} {_} {_} {Rmor φ} {Rmor ψ} laxR (morR B)))
        ( lax-trans-comp {_} {_}
          { ty-morph-comp (morR B) (Rmor φ)}
          { ty-morph-comp (Amor φ) (morR A)}
          { ty-morph-comp (Amor ψ) (morR A)}
          ( l-whisk-lax-trans {_} {_} {_}
            { Amor φ}
            { Amor ψ}
            ( morR A)
            ( laxA))
          ( Rlax φ))
  open dtype-lax-trans public

  dtype-lax-trans-comp : {A B : dtype} {φ ψ ξ : dtype-morph A B} →
    dtype-lax-trans ψ ξ → dtype-lax-trans φ ψ  → dtype-lax-trans φ ξ
  laxL (dtype-lax-trans-comp {φ = φ} {ψ} {ξ} Ψ Φ) = lax-trans-comp {_} {_}
    {Lmor φ} {Lmor ψ} {Lmor ξ} (laxL Ψ) (laxL Φ)
  laxA (dtype-lax-trans-comp {φ = φ} {ψ} {ξ} Ψ Φ) = lax-trans-comp {_} {_}
    {Amor φ} {Amor ψ} {Amor ξ} (laxA Ψ) (laxA Φ)
  laxR (dtype-lax-trans-comp {φ = φ} {ψ} {ξ} Ψ Φ) = lax-trans-comp {_} {_}
    {Rmor φ} {Rmor ψ} {Rmor ξ} (laxR Ψ) (laxR Φ)  
  3isoL (dtype-lax-trans-comp {φ = φ} {ψ} {ξ} Ψ Φ) α =
    tr-sq-sq-tr {!   !} (3isoL Φ α) (3isoL Ψ α) (Inv {!  !})
  3isoR (dtype-lax-trans-comp {φ = φ} {ψ} {ξ} Ψ Φ) α = {!   !}

  whisk-cone-unit : (T : cat) → dtype-lax-trans (whisk-cone-dtype-morph (Id T)) (id-dtype-morph (cone T))
  laxL (whisk-cone-unit T) = Right-unit-law
  laxA (whisk-cone-unit T) = Right-unit-law 
  laxR (whisk-cone-unit T) = Right-unit-law 
  3isoL (whisk-cone-unit T) α = Triangle-identity-right α f
  3isoR (whisk-cone-unit T) α = Triangle-identity-right α g

  whisk-cone-assoc : {T S R : cat} (s : fun S T) → (r : fun R S) → 
    dtype-lax-trans {cone T} {cone R}
      ( dtype-morph-comp (whisk-cone-dtype-morph r) (whisk-cone-dtype-morph s))
      ( whisk-cone-dtype-morph (Comp s r))
  laxL (whisk-cone-assoc s t) h =  Inv (Assoc t s h)
  laxA (whisk-cone-assoc s r) h = Inv (Assoc r s h)
  laxR (whisk-cone-assoc s r) h = Inv (Assoc r s h)
  3isoL (whisk-cone-assoc s r) h = {!   !}
  3isoR (whisk-cone-assoc s r) h = {!   !}
```