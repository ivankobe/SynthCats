```agda
module V3.CaTT where

open import Data.Bool.Base
open import Data.Bool.Properties

mutual

  data Ctx : Set where
    ∅ : Ctx
    _,_ :  (Γ : Ctx) → Ty Γ → Ctx

  data Ty : Ctx → Set where
    _↑ : {Γ : Ctx} {B : Ty Γ} → Ty Γ → Ty (Γ , B)
    Ob : {Γ : Ctx} → Ty Γ
    [_]_⇒_ : {Γ : Ctx} → (A : Ty Γ) → Tm Γ A → Tm Γ A → Ty Γ

  data Tm : (Γ : Ctx) → Ty Γ → Set where
    var : {Γ : Ctx} {A : Ty Γ} → Γ ∋ A → Tm Γ A

  data _∋_ : (Γ : Ctx) → Ty Γ → Set where
    here : {Γ : Ctx} {A : Ty Γ} → (Γ , A) ∋ (A ↑)
    there : {Γ : Ctx} {A B : Ty Γ} → Γ ∋ A → (Γ , B) ∋ (A ↑)

mutual

  data Sub : Ctx → Ctx → Set where
    ⟨⟩ : {Γ : Ctx} → Sub Γ ∅
    ⟨_,_⟩ : {Δ Γ : Ctx} → (σ : Sub Δ Γ) → {A : Ty Γ} → Tm Δ (A [ σ ]ty) → Sub Δ (Γ , A)

  _[_]ty : {Γ Δ : Ctx} → Ty Δ → Sub Γ Δ → Ty Γ
  (A ↑) [ ⟨ σ , _ ⟩ ]ty = A [ σ ]ty
  Ob [ σ ]ty = Ob
  ([ A ] t ⇒ u) [ σ ]ty = [ A [ σ ]ty ] (t [ σ ]tm) ⇒ (u [ σ ]tm)

  _[_]tm : {Γ Δ : Ctx} {A : Ty Δ} → Tm Δ A → (σ : Sub Γ Δ) → Tm Γ (A [ σ ]ty)
  var here [ ⟨ σ , t ⟩ ]tm = t
  var (there x) [ ⟨ σ , t ⟩ ]tm = var x [ σ ]tm

data occurs-tm : {Γ : Ctx} {A B : Ty Γ} (x : Γ ∋ A) → Tm Γ B → Set where
  occurs-tm-here : {Γ : Ctx} {A : Ty Γ} → occurs-tm (here {A = A}) (var here)
  occurs-tm-there : {Γ : Ctx} {A B  : Ty Γ} → (x : Γ ∋ A) → occurs-tm (there {B = B} x) (var (there x))

data occurs-ty : {Γ : Ctx} {A : Ty Γ} (x : Γ ∋ A) → (B : Ty Γ) → Set where
  occurs-ty-source : {Γ : Ctx} {A B : Ty Γ} (x : Γ ∋ A) → (t u : Tm Γ B) → occurs-tm x t → occurs-ty x ([ B ] t ⇒ u)
  occurs-ty-base : {Γ : Ctx} {A B : Ty Γ} (x : Γ ∋ A) → (t u : Tm Γ B) → occurs-ty x A → occurs-ty x ([ B ] t ⇒ u)
  occurs-ty-target : {Γ : Ctx} {A B : Ty Γ} (x : Γ ∋ A) → (t u : Tm Γ B) → occurs-tm x u → occurs-ty x ([ B ] t ⇒ u)

occurs-tm-pred : {Γ : Ctx} {A B : Ty Γ} (x : Γ ∋ A) → Tm Γ B → Bool
occurs-tm-pred here (var here) = true
occurs-tm-pred here (var (there y)) = false
occurs-tm-pred (there x) (var here) = false
occurs-tm-pred (there x) (var (there y)) = true

occurs-ty-pred : {Γ : Ctx} {A : Ty Γ} (x : Γ ∋ A) → (B : Ty Γ) → Bool
occurs-ty-pred here (B ↑) = false
occurs-ty-pred (there x) (B ↑) = occurs-ty-pred x B
occurs-ty-pred x Ob = false
occurs-ty-pred x ([ B ] t ⇒ u) = occurs-tm-pred x t ∨ occurs-ty-pred x B ∨ occurs-tm-pred x u
```