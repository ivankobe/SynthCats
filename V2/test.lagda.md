```agda

module V2.test where

mutual

  data Ctx : Set where
    ∅ : Ctx
    _,_ : (Γ : Ctx ) → ( A : Ty Γ) → Ctx

  data Var : Ctx → Set where
    intro : (Γ : Ctx ) → ( A : Ty Γ) → Var (Γ , A )
    weak : (Γ : Ctx ) → ( A : Ty Γ) → Var Γ → Var (Γ , A )



  data Ty : Ctx → Set where
    Ob : {Γ : Ctx } → Ty Γ
    [_]_⇒_ : {Γ : Ctx } → ( A : Ty Γ) → ( t : Tm Γ A ) → ( u : Tm Γ A ) → Ty Γ

  data Tm : (Γ : Ctx ) → Ty Γ → Set where
    var : {Γ : Ctx } → ( x : Var Γ) → Tm Γ ( var-to-type x )

  data Sub : Ctx → Ctx → Set where
    ⟨⟩ : {∆ : Ctx } → Sub ∆ ∅
    ⟨_,_⟩ : {Γ ∆ : Ctx } { A : Ty Γ} → (σ : Sub ∆ Γ) → Tm ∆ ( A [ σ ] ty ) → Sub ∆ (Γ , A)

  weaken-ty : {Γ : Ctx } → ( B : Ty Γ) → Ty Γ → Ty (Γ , B)
  weaken-ty B Ob = Ob

```