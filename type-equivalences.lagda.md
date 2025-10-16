```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import whiskering
-- open import synthetic-categories
open import type-morphisms
open import lax-transformations
-- open import functoriality-of-whiskering

module type-equivalences where
```

A type morphism φ : A ⇝ B is an *equivalence* if there is a type morphism ψ : B ⇝ A together with
lax isos ψφ ≅ id_A and φψ ≅ id_B. 

```agda
record ty-morph-is-equiv {A B : Ty} (φ : ty-morph A B) : Set
  where
  field
    ty-morph-is-equiv-inv-map : ty-morph B A
    ty-morph-is-equiv-inv-is-sec :
      lax-iso (ty-morph-comp φ ty-morph-is-equiv-inv-map) (id-ty-morph B)
    ty-morph-is-equiv-inv-is-ret :
      lax-iso (id-ty-morph A) (ty-morph-comp ty-morph-is-equiv-inv-map φ)

open ty-morph-is-equiv public

record ty-equiv (A B : Ty) : Set
  where
  field
    ty-equiv-morph : ty-morph A B
    ty-equiv-is-equiv : ty-morph-is-equiv ty-equiv-morph

open ty-equiv public
```

The componenets of a type equivalence.

```agda
ty-equiv-map : {A B : Ty} → ty-equiv A B → ty-morph A B
ty-equiv-map = ty-equiv-morph

ty-equiv-inv-map : {A B : Ty} → ty-equiv A B → ty-morph B A
ty-equiv-inv-map φ = ty-morph-is-equiv-inv-map (ty-equiv-is-equiv φ)

ty-equiv-inv-is-sec : {A B : Ty} → (φ : ty-equiv A B) →
  lax-iso (ty-morph-comp (ty-equiv-morph φ) (ty-equiv-inv-map φ)) (id-ty-morph B)
ty-equiv-inv-is-sec φ = ty-morph-is-equiv-inv-is-sec (ty-equiv-is-equiv φ)

ty-equiv-inv-is-sec-map : {A B : Ty} → (φ : ty-equiv A B) →
  lax-trans (ty-morph-comp (ty-equiv-morph φ) (ty-equiv-inv-map φ)) (id-ty-morph B)
ty-equiv-inv-is-sec-map φ = lax-iso-map (ty-equiv-inv-is-sec φ)

ty-equiv-inv-is-sec-inv-map : {A B : Ty} → (φ : ty-equiv A B) →
  lax-trans (id-ty-morph B) (ty-morph-comp (ty-equiv-morph φ) (ty-equiv-inv-map φ))
ty-equiv-inv-is-sec-inv-map φ = lax-iso-inv-map (ty-equiv-inv-is-sec φ)

ty-morph-is-equiv-is-sec-iso : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-iso (ty-morph-comp φ (ty-morph-is-equiv-inv-map P)) (id-ty-morph B)
ty-morph-is-equiv-is-sec-iso φ = ty-morph-is-equiv-inv-is-sec 

ty-morph-is-equiv-inv-is-sec-map : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-trans (ty-morph-comp φ (ty-morph-is-equiv-inv-map P)) (id-ty-morph B)
ty-morph-is-equiv-inv-is-sec-map φ P = lax-iso-map (ty-morph-is-equiv-inv-is-sec P)

ty-morph-is-equiv-inv-is-sec-inv : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-trans (id-ty-morph B) (ty-morph-comp φ (ty-morph-is-equiv-inv-map P))
ty-morph-is-equiv-inv-is-sec-inv φ P = lax-iso-inv-map (ty-morph-is-equiv-inv-is-sec P)  

ty-morph-is-equiv-is-sec-map-is-iso : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-trans-is-iso {φ = ty-morph-comp φ (ty-morph-is-equiv-inv-map P)} {id-ty-morph B}
    ( ty-morph-is-equiv-inv-is-sec-map φ P)
ty-morph-is-equiv-is-sec-map-is-iso φ P = lax-iso-is-iso (ty-morph-is-equiv-is-sec-iso φ P)

ty-equiv-inv-is-ret : {A B : Ty} → (φ : ty-equiv A B) →
  lax-iso (id-ty-morph A) (ty-morph-comp (ty-equiv-inv-map φ) (ty-equiv-morph φ))
ty-equiv-inv-is-ret φ = ty-morph-is-equiv-inv-is-ret (ty-equiv-is-equiv φ)

ty-equiv-inv-is-ret-map : {A B : Ty} → (φ : ty-equiv A B) →
  lax-trans (id-ty-morph A) (ty-morph-comp (ty-equiv-inv-map φ) (ty-equiv-morph φ))
ty-equiv-inv-is-ret-map φ = lax-iso-map (ty-equiv-inv-is-ret φ)

ty-equiv-inv-is-ret-inv-map : {A B : Ty} → (φ : ty-equiv A B) →
  lax-trans (ty-morph-comp (ty-equiv-inv-map φ) (ty-equiv-morph φ)) (id-ty-morph A)
ty-equiv-inv-is-ret-inv-map φ = lax-iso-inv-map (ty-equiv-inv-is-ret φ)

ty-morph-is-equiv-inv-is-ret-iso : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-iso (id-ty-morph A) (ty-morph-comp (ty-morph-is-equiv-inv-map P) φ)
ty-morph-is-equiv-inv-is-ret-iso φ = ty-morph-is-equiv-inv-is-ret

ty-morph-is-equiv-inv-is-ret-map : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-trans (id-ty-morph A) (ty-morph-comp (ty-morph-is-equiv-inv-map P) φ)
ty-morph-is-equiv-inv-is-ret-map φ P = lax-iso-map (ty-morph-is-equiv-inv-is-ret P)

ty-morph-is-equiv-inv-is-ret-inv : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-trans (ty-morph-comp (ty-morph-is-equiv-inv-map P) φ) (id-ty-morph A)
ty-morph-is-equiv-inv-is-ret-inv φ P = lax-iso-inv-map (ty-morph-is-equiv-inv-is-ret P)

ty-morph-is-equiv-inv-is-ret-is-iso : {A B : Ty} (φ : ty-morph A B) → (P : ty-morph-is-equiv φ) →
  lax-trans-is-iso {φ = id-ty-morph A} {ty-morph-comp (ty-morph-is-equiv-inv-map P) φ}
    ( ty-morph-is-equiv-inv-is-ret-map φ P)
ty-morph-is-equiv-inv-is-ret-is-iso φ P = lax-iso-is-iso (ty-morph-is-equiv-inv-is-ret-iso φ P)
```

The inverse of a type equivalence is a type equivalence.

```agda
ty-morph-is-equiv-inv : {A B : Ty} {φ : ty-morph A B}
  (P : ty-morph-is-equiv φ) → ty-morph-is-equiv (ty-morph-is-equiv-inv-map P)
ty-morph-is-equiv-inv {φ = φ} P = record
  { ty-morph-is-equiv-inv-map = φ
  ; ty-morph-is-equiv-inv-is-sec = lax-iso-inv (ty-morph-is-equiv-inv-is-ret P)
  ; ty-morph-is-equiv-inv-is-ret = lax-iso-inv (ty-morph-is-equiv-inv-is-sec P)
  }
```

# Properties of type equivalences.

The identity type morphism is an equivalence.

```agda
id-ty-morph-is-equiv : (A : Ty) → ty-morph-is-equiv (id-ty-morph A)
id-ty-morph-is-equiv A = record
  { ty-morph-is-equiv-inv-map = id-ty-morph A
  ; ty-morph-is-equiv-inv-is-sec = record {
      lax-iso-lax-trans = id-lax-trans (id-ty-morph A) ;
      lax-iso-is-iso = record
        { lax-trans-is-iso-inv = id-lax-trans (id-ty-morph A)
        ; lax-trans-is-iso-inv-is-sec = λ α → Left-unit-law _
        ; lax-trans-is-iso-inv-is-ret = λ α → Right-unit-law _
        }
      }
  ; ty-morph-is-equiv-inv-is-ret = record {
    lax-iso-lax-trans = id-lax-trans (id-ty-morph A) ;
    lax-iso-is-iso = record
      { lax-trans-is-iso-inv = id-lax-trans (id-ty-morph A)
      ; lax-trans-is-iso-inv-is-sec = λ α → Left-unit-law _
      ; lax-trans-is-iso-inv-is-ret = λ α → Right-unit-law _
      }
    }
  }
```

If a type morphism f : A ⇝ B is an equivalence and tere is a lax isomorphism α : f ≅ f',
then f' is an equivalence. 

```agda
ty-equiv-lax-iso-is-equiv :  {A B : Ty} {t u : Tm A} {v w : Tm B}
  {f f' : ty-morph ([ A ] t ⇒ u) ([ B ] v ⇒ w)} (p : ty-morph-is-equiv f) →
    (φ : lax-iso f f') → ty-morph-is-equiv f'
ty-equiv-lax-iso-is-equiv {f = f} {f'} p φ = record
  { ty-morph-is-equiv-inv-map = ty-morph-is-equiv-inv-map p
  ; ty-morph-is-equiv-inv-is-sec = record
    { lax-iso-lax-trans = λ b →
        Comp
          ( ty-morph-is-equiv-inv-is-sec-map f p b)
          ( lax-iso-inv-map φ _) ;
      lax-iso-is-iso = lax-trans-nonzero-dim-is-iso _
      }
  ; ty-morph-is-equiv-inv-is-ret = record
    { lax-iso-lax-trans = λ a → 
        Comp
          ( ty-morph-base (ty-morph-step (ty-morph-is-equiv-inv-map p)) (lax-iso-lax-trans φ a))
          ( ty-morph-is-equiv-inv-is-ret-map f p a) ;
      lax-iso-is-iso = lax-trans-nonzero-dim-is-iso _ }
  }
```

Definitions of sections and retractions.

```agda
record ty-morph-has-sec {A B : Ty} (φ : ty-morph A B) : Set where
  coinductive
  field
    ty-morph-has-sec-sec : ty-morph B A
    ty-morph-has-sec-is-sec : lax-iso (ty-morph-comp φ ty-morph-has-sec-sec)  (id-ty-morph B)

open ty-morph-has-sec public

record ty-morph-has-ret {A B : Ty} (φ : ty-morph A B) : Set where
  coinductive
  field
    ty-morph-has-ret-ret : ty-morph B A
    ty-morph-has-ret-is-ret : lax-iso (id-ty-morph A) (ty-morph-comp ty-morph-has-ret-ret φ)

open ty-morph-has-ret public
```

If a type morphism has both a section and a retraction, then it is an equivalence.

```agda
ty-morph-sec-ret-equiv : {A B : Ty} {t u : Tm A} {v w : Tm B}
  {φ : ty-morph ([ A ] t ⇒ u) ([ B ] v ⇒ w)}
    (σ : ty-morph-has-sec φ) → (ρ : ty-morph-has-ret φ) → ty-morph-is-equiv φ
ty-morph-sec-ret-equiv {φ = φ} σ ρ = record
  { ty-morph-is-equiv-inv-map = ty-morph-has-sec-sec σ
  ; ty-morph-is-equiv-inv-is-sec = record {
      lax-iso-lax-trans = lax-iso-map (ty-morph-has-sec-is-sec σ) ;
      lax-iso-is-iso = lax-trans-nonzero-dim-is-iso _ }
  ; ty-morph-is-equiv-inv-is-ret = record {
      lax-iso-lax-trans = λ a →
        Comp
          ( lax-iso-inv-map (ty-morph-has-ret-is-ret ρ) _)
          ( Comp
            ( ty-morph-base
              ( ty-morph-step (ty-morph-has-ret-ret ρ))
              ( lax-iso-inv-map (ty-morph-has-sec-is-sec σ) (ty-morph-base φ a)))
            ( lax-iso-map (ty-morph-has-ret-is-ret ρ) _)) ;
      lax-iso-is-iso = lax-trans-nonzero-dim-is-iso _ }
  }
```

Type equivalences satisfy the three for two property.

--- ```agda
ty-equiv-comp : {A B C : Ty} {t u : Tm A} {v w : Tm B} {z x : Tm C}
  {φ : ty-morph ( [ A ] t ⇒ u) ([ B ] v ⇒ w)}
  {ψ : ty-morph ([ B ] v ⇒ w) ([ C ] z ⇒ x)} (P : ty-morph-is-equiv φ) → (P' : ty-morph-is-equiv ψ) →
    ty-morph-is-equiv (ty-morph-comp ψ φ) 
ty-equiv-comp {φ = φ} {ψ} P P' = record
  { ty-morph-is-equiv-inv-map =
      ty-morph-comp (ty-morph-is-equiv-inv-map P) (ty-morph-is-equiv-inv-map P')
  ; ty-morph-is-equiv-inv-is-sec = record {
      lax-iso-lax-trans = λ a →
        Comp
          ( ty-morph-is-equiv-inv-is-sec-map ψ P' a)
          ( ty-morph-base
            ( ty-morph-step ψ)
            ( ty-morph-is-equiv-inv-is-sec-map φ P _)) ;
      lax-iso-is-iso = lax-trans-nonzero-dim-is-iso _ }
  ; ty-morph-is-equiv-inv-is-ret = record {
      lax-iso-lax-trans = λ a →
        Comp
          ( ty-morph-base
            ( ty-morph-step (ty-morph-is-equiv-inv-map P))
            ( ty-morph-is-equiv-inv-is-ret-map ψ P' _))
          ( ty-morph-is-equiv-inv-is-ret-map φ P a) ;
      lax-iso-is-iso = lax-trans-nonzero-dim-is-iso _ }
  }

ty-morph-is-equiv-left-factor-lax-iso : {A B C : Ty} {φ : ty-morph A B} {ψ : ty-morph B C}
  (P : ty-morph-is-equiv ψ) → (P' : ty-morph-is-equiv (ty-morph-comp ψ φ)) →
    lax-iso φ (ty-morph-comp (ty-morph-is-equiv-inv-map P) (ty-morph-comp ψ φ))
ty-morph-is-equiv-left-factor-lax-iso {φ = φ} {ψ} P P' = record
  { lax-iso-lax-trans = λ a → ty-morph-is-equiv-inv-is-ret-map ψ P (ty-morph-base φ a) ;
    lax-iso-is-iso = record
      { lax-trans-is-iso-inv = λ a →
          lax-trans-is-iso-inv (ty-morph-is-equiv-inv-is-ret-is-iso ψ P) (ty-morph-base φ a)
      ; lax-trans-is-iso-inv-is-sec = λ a →
          lax-trans-is-iso-inv-is-sec (ty-morph-is-equiv-inv-is-ret-is-iso ψ P) (ty-morph-base φ a)
      ; lax-trans-is-iso-inv-is-ret = λ a → 
          lax-trans-is-iso-inv-is-ret (ty-morph-is-equiv-inv-is-ret-is-iso ψ P) (ty-morph-base φ a)
      } 
    }

ty-morph-is-equiv-left-factor : {A B C : Ty} {t u : Tm A} {v w : Tm B} {z x : Tm C} 
  {φ : ty-morph ([ A ] t ⇒ u) ([ B ] v ⇒ w)} {ψ : ty-morph ([ B ] v ⇒ w) ([ C ] z ⇒ x)}
    (P : ty-morph-is-equiv ψ) → (P' : ty-morph-is-equiv (ty-morph-comp ψ φ)) → ty-morph-is-equiv φ
ty-morph-is-equiv-left-factor {φ = φ} {ψ} P P' =
  ty-equiv-lax-iso-is-equiv
    ( ty-equiv-comp P' (ty-morph-is-equiv-inv P))
    ( lax-iso-inv (ty-morph-is-equiv-left-factor-lax-iso P P'))

ty-morph-is-equiv-right-factor-lax-iso : {A B C : Ty} {t u : Tm A} {v w : Tm B} {z x : Tm C} 
  {φ : ty-morph ([ A ] t ⇒ u) ([ B ] v ⇒ w)} {ψ : ty-morph ([ B ] v ⇒ w) ([ C ] z ⇒ x)}
    (P : ty-morph-is-equiv φ) → (P' : ty-morph-is-equiv (ty-morph-comp ψ φ)) →
      lax-iso ψ (ty-morph-comp (ty-morph-comp ψ φ) (ty-morph-is-equiv-inv-map P))
ty-morph-is-equiv-right-factor-lax-iso {φ = φ} {ψ} P P' = record
  { lax-iso-lax-trans = λ b →
      ty-morph-base (ty-morph-step ψ) (ty-morph-is-equiv-inv-is-sec-inv φ P b) ;
    lax-iso-is-iso = lax-trans-nonzero-dim-is-iso _ }

ty-morph-is-equiv-right-factor : {A B C : Ty} {t u : Tm A} {v w : Tm B} {z x : Tm C} 
  {φ : ty-morph ([ A ] t ⇒ u) ([ B ] v ⇒ w)} {ψ : ty-morph ([ B ] v ⇒ w) ([ C ] z ⇒ x)}
    (P : ty-morph-is-equiv φ) → (P' : ty-morph-is-equiv (ty-morph-comp ψ φ)) → ty-morph-is-equiv ψ
ty-morph-is-equiv-right-factor {φ = φ} {ψ} P P' =
  ty-equiv-lax-iso-is-equiv
    ( ty-equiv-comp (ty-morph-is-equiv-inv P) P')
    ( lax-iso-inv (ty-morph-is-equiv-right-factor-lax-iso P P')) 
```

Type equivalences satisfy the six-for-two property.

```agda
ty-equiv-6-for-2-middle-factor-sec : {A B C D : Ty} {a' a'' : Tm A} {b' b'' : Tm B} {c' c'' : Tm C}
  {d' d'' : Tm D} (f : ty-morph ([ A ] a' ⇒ a'') ([ B ] b' ⇒ b'')) →
  (g : ty-morph ([ B ] b' ⇒ b'') ([ C ] c' ⇒ c'')) →
  (h : ty-morph ([ C ] c' ⇒ c'') ([ D ] d' ⇒ d'')) → 
  ty-morph-is-equiv (ty-morph-comp g f) → ty-morph-is-equiv (ty-morph-comp h g) → ty-morph-has-sec g
ty-equiv-6-for-2-middle-factor-sec f g h P P' = record {
  ty-morph-has-sec-sec = ty-morph-comp f (ty-morph-is-equiv-inv-map P) ;
  ty-morph-has-sec-is-sec = record {
    lax-iso-lax-trans = λ c → ty-morph-is-equiv-inv-is-sec-map (ty-morph-comp g f) P c ;
    lax-iso-is-iso = lax-trans-nonzero-dim-is-iso _ } }

ty-equiv-6-for-2-middle-factor-ret : {A B C D : Ty} {a' a'' : Tm A} {b' b'' : Tm B} {c' c'' : Tm C}
  {d' d'' : Tm D} (f : ty-morph ([ A ] a' ⇒ a'') ([ B ] b' ⇒ b'')) →
  (g : ty-morph ([ B ] b' ⇒ b'') ([ C ] c' ⇒ c'')) →
  (h : ty-morph ([ C ] c' ⇒ c'') ([ D ] d' ⇒ d'')) → 
  ty-morph-is-equiv (ty-morph-comp g f) → ty-morph-is-equiv (ty-morph-comp h g) → ty-morph-has-ret g
ty-equiv-6-for-2-middle-factor-ret f g h P P' = record {
  ty-morph-has-ret-ret = ty-morph-comp (ty-morph-is-equiv-inv-map P') h ;
  ty-morph-has-ret-is-ret = record {
    lax-iso-lax-trans = λ b → ty-morph-is-equiv-inv-is-ret-map (ty-morph-comp h g) P' b ;
    lax-iso-is-iso = lax-trans-nonzero-dim-is-iso _ } }

ty-equiv-6-for-2-middle-factor : {A B C D : Ty} {a' a'' : Tm A} {b' b'' : Tm B} {c' c'' : Tm C}
  {d' d'' : Tm D} (f : ty-morph ([ A ] a' ⇒ a'') ([ B ] b' ⇒ b'')) →
  (g : ty-morph ([ B ] b' ⇒ b'') ([ C ] c' ⇒ c'')) →
  (h : ty-morph ([ C ] c' ⇒ c'') ([ D ] d' ⇒ d'')) → 
  ty-morph-is-equiv (ty-morph-comp g f) → ty-morph-is-equiv (ty-morph-comp h g) → ty-morph-is-equiv g
ty-equiv-6-for-2-middle-factor f g h P P' =
  ty-morph-sec-ret-equiv
    ( ty-equiv-6-for-2-middle-factor-sec f g h P P' )
    ( ty-equiv-6-for-2-middle-factor-ret f g h P P')

ty-equiv-6-for-2-left-factor : {A B C D : Ty} {a' a'' : Tm A} {b' b'' : Tm B} {c' c'' : Tm C}
  {d' d'' : Tm D} (f : ty-morph ([ A ] a' ⇒ a'') ([ B ] b' ⇒ b'')) →
  (g : ty-morph ([ B ] b' ⇒ b'') ([ C ] c' ⇒ c'')) →
  (h : ty-morph ([ C ] c' ⇒ c'') ([ D ] d' ⇒ d'')) → 
  ty-morph-is-equiv (ty-morph-comp g f) → ty-morph-is-equiv (ty-morph-comp h g) → ty-morph-is-equiv f
ty-equiv-6-for-2-left-factor f g h P P' =
  ty-morph-is-equiv-left-factor (ty-equiv-6-for-2-middle-factor f g h P P') P

ty-equiv-6-for-2-right-factor : {A B C D : Ty} {a' a'' : Tm A} {b' b'' : Tm B} {c' c'' : Tm C}
  {d' d'' : Tm D} (f : ty-morph ([ A ] a' ⇒ a'') ([ B ] b' ⇒ b'')) →
  (g : ty-morph ([ B ] b' ⇒ b'') ([ C ] c' ⇒ c'')) →
  (h : ty-morph ([ C ] c' ⇒ c'') ([ D ] d' ⇒ d'')) → 
  ty-morph-is-equiv (ty-morph-comp g f) → ty-morph-is-equiv (ty-morph-comp h g) → ty-morph-is-equiv h
ty-equiv-6-for-2-right-factor f g h P P' =
  ty-morph-is-equiv-right-factor (ty-equiv-6-for-2-middle-factor f g h P P') P'
```
