```agda

module V2.intrinsic-syntax where

mutual

  data Ctx : Set
  data Ty : Ctx → Set
  data EqTy : {Γ : Ctx} (A B : Ty Γ) → Set
  data Tm : {Γ : Ctx} → Ty Γ → Set
  data EqTm : {Γ : Ctx} {A : Ty Γ} (t u : Tm A) → Set
  data Sub : Ctx → Ctx → Set
  data EqSub : {Γ Δ : Ctx} → Sub Γ Δ → Sub Γ Δ → Set
  postulate _∘_ : {Θ Δ Γ : Ctx} (γ : Sub Δ Γ) → (δ : Sub Θ Δ) → Sub Θ Γ
  postulate _[_]ty : {Γ Δ : Ctx} → Ty Γ → Sub Δ Γ → Ty Δ
  postulate _[_]tm : {Γ Δ : Ctx} {A : Ty Γ} → Tm A → (σ : Sub Δ Γ) → Tm (A [ σ ]ty)

  data Ctx where
    ∅ : Ctx
    _,_ : (Γ : Ctx) → (A : Ty Γ) → Ctx

  data Sub where
    id : {Γ : Ctx} → Sub Γ Γ
    ⟨_,_⟩ : {Γ Δ : Ctx} → (σ : Sub Δ Γ) → (A : Ty Γ) → Tm (A [ σ ]ty) → Sub Δ (Γ , A)
    wk : (Γ : Ctx) → (A : Ty Γ) → Sub (Γ , A) Γ

  data EqSub where
    assoc-sub : {Ξ Θ Δ Γ : Ctx} (γ : Sub Δ Γ) (δ : Sub Θ Δ) (θ : Sub Ξ Θ) → EqSub (γ ∘ (δ ∘ θ)) ((γ  ∘ δ) ∘ θ)
    unit-left-sub : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → EqSub (id ∘ γ) γ
    unit-right-sub : {Δ Γ : Ctx} → (γ : Sub Δ Γ) → EqSub (γ ∘ id) γ

  data Tm where
    var : {Γ : Ctx} (A : Ty Γ) → Tm (A [ (wk Γ A) ]ty)

  data Ty where
    Ob : {Γ : Ctx} → Ty Γ
    [_]_⇒_ : {Γ : Ctx} → (A : Ty Γ) → (t : Tm A) → (u : Tm A) → Ty Γ

  data EqTy where
    id-ty : {Γ : Ctx} (A : Ty Γ) → EqTy (A [ id ]ty) A
    comp-ty : {Θ Δ Γ : Ctx} (γ : Sub Δ Γ) → (δ : Sub Θ Δ) → (A : Ty Γ) →
      EqTy (A [ (γ ∘ δ) ]ty) ((A [ γ ]ty) [ δ ]ty)

  data EqTm where
    comp-tm : {Θ Δ Γ : Ctx} (γ : Sub Δ Γ) → (δ : Sub Θ Δ) → {A : Ty Γ} → (t : Tm A) →
      EqTm (t [ (γ ∘ δ) ]tm) (TrEqTy' ((t [ γ ]tm) [ δ ]tm) (comp-ty γ δ A))

  postulate TrEqTy : {Γ : Ctx} {A B : Ty Γ} (t : Tm A) → EqTy A B → Tm B
  postulate TrEqTy' : {Γ : Ctx} {A B : Ty Γ} (t : Tm B) → EqTy A B → Tm A
  
```

-- ```agda
-- mutual
--   -- Positive dependency for terms: x ∈ Var(t:A)
--   data _∈Var-term_ : {Γ : Ctx} {A : Ty Γ} → Var Γ → Tm Γ A → Set where
--     -- VAR-SELF: x ∈ Var(x)
--     var-self : {Γ : Ctx} → (x : Var Γ)
--              → x ∈Var-term (var Γ x)
  
--     -- VARDEP-TERM-WEAKEN: if x ∈ Var(t) in Γ, then x ∈ Var(t) in Γ.B
--     vardep-term-weaken : {Γ : Ctx} {A B : Ty Γ} {t : Tm Γ A}
--                        → (x : Var Γ) → x ∈Var-term t
--                        → (weak Γ B x) ∈Var-term (weaken-tm B t)
  
--     -- VARDEP-FROM-TYPE: if x ∈ Var(A), then x ∈ Var(t) for any t:A
--     vardep-from-type : {Γ : Ctx} {A : Ty Γ}
--                      → (x : Var Γ) → (t : Tm Γ A)
--                      → x ∈Var-type A
--                      → x ∈Var-term t
  
--     -- VARDEP-SUBST: dependency through substitution
--     -- If x ∈ Var(t) in Γ, σ : Δ → Γ, and y ∈ Var(σ(x)), then y ∈ Var(t[σ])
--     vardep-subst : {Γ Δ : Ctx} {A : Ty Γ}
--                  → (x : Var Γ) → (t : Tm Γ A)
--                  → (σ : Sub Δ Γ)
--                  → (y : Var Δ)
--                  → x ∈Var-term t
--                  → y ∈Var-term (apply-sub-to-var σ x)
--                  → y ∈Var-term (t [ σ ]tm)
  
--   -- Positive dependency for types: x ∈ Var(A)
--   data _∈Var-type_ : {Γ : Ctx} → Var Γ → Ty Γ → Set where
--     -- VARDEP-TYPE-WEAKEN: if x ∈ Var(A) in Γ, then x ∈ Var(A) in Γ.B
--     vardep-type-weaken : {Γ : Ctx} {A B : Ty Γ}
--                        → (x : Var Γ) → x ∈Var-type A
--                        → (weak Γ B x) ∈Var-type (weaken-ty B A)
  
--     -- VARDEP-HOM-SRC: if x ∈ Var(t), then x ∈ Var([A] t ⇒ u)
--     vardep-hom-src : {Γ : Ctx} {A : Ty Γ} {t u : Tm Γ A}
--                    → (x : Var Γ) → x ∈Var-term t
--                    → x ∈Var-type ([ A ] t ⇒ u)
  
--     -- VARDEP-HOM-TGT: if x ∈ Var(u), then x ∈ Var([A] t ⇒ u)
--     vardep-hom-tgt : {Γ : Ctx} {A : Ty Γ} {t u : Tm Γ A}
--                    → (x : Var Γ) → x ∈Var-term u
--                    → x ∈Var-type ([ A ] t ⇒ u)
  
--     -- VARDEP-HOM-BASE: if x ∈ Var(A), then x ∈ Var([A] t ⇒ u)
--     vardep-hom-base : {Γ : Ctx} {A : Ty Γ} {t u : Tm Γ A}
--                     → (x : Var Γ) → x ∈Var-type A
--                     → x ∈Var-type ([ A ] t ⇒ u)
  
--   -- Helper: apply substitution to a variable (returns the term σ(x))
--   postulate
--     apply-sub-to-var : {Γ Δ : Ctx} → Sub Δ Γ → Var Γ → Tm Δ {! type !}
--     weaken-ty : {Γ : Ctx} → (B : Ty Γ) → Ty Γ → Ty (Γ . B)
--    