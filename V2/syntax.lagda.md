```agda

module V2.syntax where

--   data Var : Ctx → Set where
--     intro : (Γ : Ctx) → (A : Ty Γ) → Var (Γ . A)
--     weak  : (Γ : Ctx) → (A : Ty Γ) → Var Γ → Var (Γ . A)
  
```
--   -- Types in a context
--   data Ty : Ctx → Set where
--     Ob : {Γ : Ctx} → Ty Γ
--     [_]_⇒_ : {Γ : Ctx} → (A : Ty Γ) → (t : Tm Γ A) → (u : Tm Γ A) → Ty Γ
  
--   -- Terms of a type in a context
--   data Tm : (Γ : Ctx) → Ty Γ → Set where
--     var : (Γ : Ctx) → (x : Var Γ) → Tm Γ (var-to-type Γ x)
--     -- Coherences and other term constructors to be added later
  
--   -- For types and terms, we need substitution operations
--   -- These will be defined mutually with the main data types
--   postulate
--     _[_]ty : {Γ Δ : Ctx} → Ty Γ → Sub Δ Γ → Ty Δ
--     _[_]tm : {Γ Δ : Ctx} {A : Ty Γ} → Tm Γ A → (σ : Sub Δ Γ) → Tm Δ (A [ σ ]ty)
  
--   -- For every variable in Γ, we need to record its corresponding type
--   -- This should also be defined mutually
--   postulate
--     var-to-type : {Γ : Ctx} → Var Γ → Ty Γ
  
--   -- Substitutions from Δ to Γ
--   data Sub : Ctx → Ctx → Set where
--     ⟨⟩ : {Δ : Ctx} → Sub Δ ∅
--     ⟨_,_↦_⟩ : {Γ Δ : Ctx} → (σ : Sub Δ Γ) → (x : Var Γ)
--             → Tm Δ ((var-to-type Γ x) [ σ ]ty) → Sub Δ (Γ . (var-to-type Γ x))
-- ```

-- ## Positive dependency
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