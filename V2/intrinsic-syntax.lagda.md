```agda
{-# OPTIONS --rewriting #-}

module V2.intrinsic-syntax where

open import Agda.Builtin.Equality
open import Agda.Builtin.Equality.Rewrite
open import Data.Bool.Base
open import Data.Bool.Properties

mutual

  data Ctx : Set where
    ∅ : Ctx
    _,_ : (Γ : Ctx) → Ty Γ → Ctx

  data Ty : Ctx → Set where
    Ob : {Γ : Ctx} → Ty Γ
    [_]_⇒_ : {Γ : Ctx} → (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ
    _[_]ty : {Γ Δ : Ctx} → Ty Γ → Sub Δ Γ → Ty Δ

  data Sub : Ctx → Ctx → Set where
    ⟨⟩ : {Δ : Ctx} → Sub Δ ∅
    p : {Γ : Ctx} {A : Ty Γ} → Sub (Γ , A) Γ
    id : {Γ : Ctx} → Sub Γ Γ
    _∘_ : {Γ Δ Θ : Ctx} → Sub Δ Γ → Sub Θ Δ → Sub Θ Γ
    ⟨_,_⟩ : {Γ Δ : Ctx} {A : Ty Γ} → (σ : Sub Δ Γ) 
          → Tm Δ (A [ σ ]ty) → Sub Δ (Γ , A)

  data Tm : (Γ : Ctx) → Ty Γ → Set where
    var₀ : {Γ : Ctx} {A : Ty Γ} → Tm (Γ , A) (A [ p ]ty)
    _[_]tm : {Γ Δ : Ctx} {A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]ty)
    -- Coherences to be added later

----------------------------------------------------------------------
-- EQUATIONS
----------------------------------------------------------------------

-- Type substitution equations
postulate
  Ob-[] : {Γ Δ : Ctx} {σ : Sub Δ Γ} 
        → (Ob [ σ ]ty) ≡ Ob
  
  Hom-[] : {Γ Δ : Ctx} {A : Ty Γ} {t u : Tm Γ A} {σ : Sub Δ Γ}
         → (([ A ] t ⇒ u) [ σ ]ty) ≡ ([ A [ σ ]ty ] (t [ σ ]tm) ⇒ (u [ σ ]tm))

-- Identity laws on types
postulate
  [id]ty : {Γ : Ctx} {A : Ty Γ} 
         → (A [ id ]ty) ≡ A

  [][]ty : {Γ Δ Θ : Ctx} {A : Ty Γ} {σ : Sub Δ Γ} {τ : Sub Θ Δ}
         → ((A [ σ ]ty) [ τ ]ty) ≡ (A [ σ ∘ τ ]ty)

{-# REWRITE Ob-[] #-}
{-# REWRITE Hom-[] #-}
{-# REWRITE [id]ty #-}
{-# REWRITE [][]ty #-}

postulate
  [id]tm : {Γ : Ctx} {A : Ty Γ} {t : Tm Γ A}
         → (t [ id ]tm) ≡ t
  
  id∘ : {Γ Δ : Ctx} {σ : Sub Δ Γ}
      → (id ∘ σ) ≡ σ
  
  ∘id : {Γ Δ : Ctx} {σ : Sub Δ Γ}
      → (σ ∘ id) ≡ σ

  ∘assoc : {Γ Δ Θ Ξ : Ctx} {σ : Sub Δ Γ} {τ : Sub Θ Δ} {ρ : Sub Ξ Θ}
         → ((σ ∘ τ) ∘ ρ) ≡ (σ ∘ (τ ∘ ρ))
  
  [][]tm : {Γ Δ Θ : Ctx} {A : Ty Γ} {t : Tm Γ A} {σ : Sub Δ Γ} {τ : Sub Θ Δ}
         → ((t [ σ ]tm) [ τ ]tm) ≡ (t [ σ ∘ τ ]tm)

  p∘⟨⟩ : {Γ Δ : Ctx} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ]ty)}
       → ((p {Γ} {A} ) ∘ ⟨ σ , t ⟩) ≡ σ

{-# REWRITE [id]tm #-}
{-# REWRITE id∘ #-}
{-# REWRITE ∘id #-}
{-# REWRITE ∘assoc #-}
{-# REWRITE [][]tm #-}
{-# REWRITE p∘⟨⟩ #-}

postulate
  var₀[⟨⟩] : {Γ Δ : Ctx} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ]ty)}
           → (var₀ {Γ} {A} [ ⟨ σ , t ⟩ ]tm) ≡ t

  ⟨⟩∘ : {Γ Δ Θ : Ctx} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ]ty)} {τ : Sub Θ Δ}
        → (⟨_,_⟩ {A = A} σ t) ∘ τ ≡ ⟨ σ ∘ τ , (t [ τ ]tm)⟩

  ⟨p,var₀⟩ : {Γ : Ctx} {A : Ty Γ}
           → ⟨ p , var₀ ⟩ ≡ id {Γ , A}

{-# REWRITE var₀[⟨⟩] #-}
{-# REWRITE ⟨⟩∘ #-}
{-# REWRITE ⟨p,var₀⟩ #-}

example : {Γ : Ctx} {A : Ty Γ} → Tm Γ A → Tm Γ A
example t = t [ id ]tm

test1 : {Γ : Ctx} {A : Ty Γ} → (A [ id ]ty) ≡ A
test1 = refl

test2 : {Γ Δ Θ : Ctx} {A : Ty Γ} {σ : Sub Δ Γ} {τ : Sub Θ Δ}
      → ((A [ σ ]ty) [ τ ]ty) ≡ (A [ σ ∘ τ ]ty)
test2 = refl

test3 : {Γ Δ : Ctx} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ]ty)}
      → (var₀ {A = A} [ ⟨ σ , t ⟩ ]tm) ≡ t
test3 = refl

data Var : Ctx → Set where
    intro : (Γ : Ctx) → (A : Ty Γ) → Var (Γ , A)
    weak  : (Γ : Ctx) → (A : Ty Γ) → Var Γ → Var (Γ , A)

var-to-type : {Γ : Ctx} → Var Γ → Ty Γ
var-to-type (intro Γ A) = A [ p ]ty
var-to-type (weak Γ A x) = (var-to-type x) [ p ]ty

var : {Γ : Ctx} → (x : Var Γ) → Tm Γ (var-to-type x)
var (intro Γ A) = var₀
var (weak Γ A x) = (var x) [ p ]tm

lookup : {Γ Δ : Ctx} → (x : Var Γ) → (σ : Sub Δ Γ) → Tm Δ ((var-to-type x) [ σ ]ty)
lookup x σ = (var x) [ σ ]tm

var-lookup : {Γ Δ : Ctx} (x : Var Γ) (σ : Sub Δ Γ)
             → (var x [ σ ]tm) ≡ lookup x σ
var-lookup x σ = refl

lookup-intro : {Γ Δ : Ctx} {A : Ty Γ} {σ : Sub Δ Γ} {t : Tm Δ (A [ σ ]ty)}
          → lookup (intro Γ A) (⟨_,_⟩ {A = A} σ t) ≡ t
lookup-intro = refl

lookup-weak : {Γ Δ : Ctx} {A B : Ty Γ} {x : Var Γ} {σ : Sub Δ Γ} {t : Tm Δ (B [ σ ]ty)}
          → lookup (weak Γ B x) (⟨_,_⟩ {A = B} σ t) ≡ lookup x σ
lookup-weak = refl

∃-var : (Γ : Ctx) → ((x : Var Γ) → Bool) → Bool
∃-var ∅ f = false
∃-var (Γ , A) f = (f (intro Γ A)) ∨ (∃-var Γ (λ x → f (weak _ _ x)))

∀-var : (Γ : Ctx) → ((x : Var Γ) → Bool) → Bool
∀-var ∅ f = true
∀-var (Γ , A) f = (f (intro Γ A)) ∧ (∀-var Γ (λ x → f (weak _ _ x)))

mutual
  depends-on-var-type : {Γ : Ctx} → Var Γ → Ty Γ → Bool
  depends-on-var-type x Ob = false
  depends-on-var-type x ([ A ] t ⇒ u) =
    depends-on-var-term x t ∨ depends-on-var-type x A ∨ depends-on-var-term x u
  depends-on-var-type x (_[_]ty {Γ = Δ} A σ) =
    ∃-var Δ (λ y → (depends-on-var-term x ((var y) [ σ ]tm)) ∧ (depends-on-var-type y A))

  {-# TERMINATING #-}
  depends-on-var-term : {Γ : Ctx} {A : Ty Γ} → Var Γ → Tm Γ A → Bool
  depends-on-var-term (intro _ _) var₀ = true
  depends-on-var-term (weak _ _ x) var₀ = false
  depends-on-var-term x (_[_]tm {Γ = Δ} t σ) =
    ∃-var Δ (λ y → (depends-on-var-term x ((var y) [ σ ]tm)) ∧ (depends-on-var-term y t))
```