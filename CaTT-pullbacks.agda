{-# OPTIONS --guardedness #-}

open import Data.Nat
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Function.Base
open import Data.Product.Base

module CaTT-pullbacks where

mutual

  data Ty : Set where
    ⋆ : Ty
    [_]_⇒_ : (A : Ty) → Tm A → Tm A → Ty

  postulate Tm : Ty → Set

postulate Inv : {A : Ty} {t u : Tm A} → Tm ([ A ] t ⇒ u)  → Tm ([ A ] u ⇒ t)

postulate Id : {A : Ty} (a : Tm A) → Tm ([ A ] a ⇒ a)

dim : Ty → ℕ
dim ⋆ = 0
dim ([ A ] _ ⇒ _) = suc (dim A)

data t*_≡_ {B : Ty} : Ty → Tm B → Set where 
  t*-base : (C D : Tm B) → t* ([ B ] C ⇒ D) ≡ D
  t*-step : {A : Ty} {D : Tm B} →  (t* A ≡ D) → (t u : Tm A) → t* ([ A ] t ⇒ u) ≡ D

data s*_≡_ {B : Ty} : Ty → Tm B → Set where 
  s*-base : (D E : Tm B) → s* ([ B ] D ⇒ E) ≡ D
  s*-step : {A : Ty} {D : Tm B} → (s* A ≡ D) → (t u : Tm A) → s* ([ A ] t ⇒ u) ≡ D

data ∂*_≡_ : Ty → Ty → Set where
  ∂*-base : (A : Ty) → ∂* A ≡ A
  ∂*-step : {A : Ty} (t u : Tm A) → (B : Ty) → ∂* A ≡ B → ∂* ([ A ] t ⇒ u) ≡ B

mutual

  r-whisk-ty : {B : Ty} {D E : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → t* A ≡ D → Ty
  r-whisk-ty {B = B} {_} {E} g ([ _ ] C ⇒ _) (t*-base C _) = [ B ] C ⇒ E
  r-whisk-ty g ([ A ] t ⇒ u) (t*-step {A = A} p t u) =
    [ r-whisk-ty g A p ] r-whisk-tm g A p t ⇒ r-whisk-tm g A p u
    
  postulate
      r-whisk-tm : {B : Ty} {D E : Tm B} (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → (p : t* A ≡ D) →
                    (α : Tm A) → Tm (r-whisk-ty g A p)

Comp : {A : Ty} {t u v : Tm A} → Tm ([ A ] u ⇒ v) → Tm ([ A ] t ⇒ u) → Tm ([ A ] t ⇒ v)
Comp {A} {t} {u} g f = r-whisk-tm g ([ A ] t ⇒ u) (t*-base _ _) f

t*-r-whisk-ty : {B : Ty} {D E : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (A : Ty) → (p : t* A ≡ D) →
  t* (r-whisk-ty g A p) ≡ E
t*-r-whisk-ty {E = E} _ _ (t*-base C _) = t*-base C E
t*-r-whisk-ty g ([ A ] t ⇒ u) (t*-step p t u) = t*-step (t*-r-whisk-ty g A p) _ _

mutual

  l-whisk-ty : {B : Ty} {C D : Tm B} → (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → s* A ≡ D → Ty
  l-whisk-ty {B = B} {C} {_} f ([ _ ] _ ⇒ E) (s*-base _ E) = [ B ] C ⇒ E
  l-whisk-ty f ([ A ] t ⇒ u) (s*-step {A = A} p t u) =
    [ l-whisk-ty f A p ] l-whisk-tm f A p t ⇒ l-whisk-tm f A p u

  postulate
    l-whisk-tm : {B : Ty} {C D : Tm B} (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → (p : s* A ≡ D) →
      (α : Tm A) → Tm (l-whisk-ty f A p)

s*-l-whisk-ty : {B : Ty} {C D : Tm B} → (f : Tm ([ B ] C ⇒ D)) → (A : Ty) → (p : s* A ≡ D) →
  s* (l-whisk-ty f A p) ≡ C
s*-l-whisk-ty {C = C} _ _ (s*-base _ E) = s*-base C E
s*-l-whisk-ty f ([ A ] t ⇒ u) (s*-step p t u) = s*-step (s*-l-whisk-ty f A p) _ _

record morph (A B : Ty) : Set
  where
  coinductive
  field
    morph-base : Tm A → Tm B
    morph-step :
      {t u : Tm A} → (morph ([ A ] t ⇒ u) ([ B ] (morph-base t) ⇒ (morph-base u)))

open morph public

morph-comp : {A B C : Ty} (ψ : morph B C) → (φ : morph A B) → morph A C
morph-base (morph-comp ψ φ) = λ a → morph-base ψ (morph-base φ a)
morph-step (morph-comp ψ φ) = morph-comp (morph-step ψ) (morph-step φ)

morph-id : (A : Ty) → morph A A
morph-base (morph-id A) = id
morph-step (morph-id A) {t} {u} = morph-id ([ A ] t ⇒ u)

mutual

  shift-ty : {A B : Ty} (φ : morph A B) → (A' : Ty) → ∂* A' ≡ A → Ty
  shift-ty {B = B} φ _ (∂*-base _) = B
  shift-ty φ ([ A' ] t ⇒ u) (∂*-step t u _ p) =
    [ (shift-ty φ A' p) ] morph-base (shift φ A' p) t ⇒ morph-base (shift φ A' p) u

  shift : {A B : Ty} (φ : morph A B) → (A' : Ty) → (p : ∂* A' ≡ A) → morph A' (shift-ty φ A' p)
  shift φ _ (∂*-base _) = φ
  shift φ ([ A' ] t ⇒ u) (∂*-step t u _ p) = morph-step (shift φ A' p)
    
morph-precomp : {A B X : Ty} {C D : Tm B} (φ : morph A X) →
                  (p : s* X ≡ D) → (f : Tm ([ B ] C ⇒ D)) → morph A (l-whisk-ty f X p)
morph-base (morph-precomp φ p f) = λ a → l-whisk-tm f _ p (morph-base φ a)
morph-step (morph-precomp φ p f) = morph-precomp (shift φ _ _) (s*-step p _ _) f

morph-postcomp : {A B X : Ty} {D E : Tm B} (φ : morph A X) →
                  (p : t* X ≡ D) → (g : Tm ([ B ] D ⇒ E)) → morph A (r-whisk-ty g X p)
morph-base (morph-postcomp φ p g) = λ a → r-whisk-tm g _ p (morph-base φ a)
morph-step (morph-postcomp φ p g) = morph-postcomp (shift φ _ _) (t*-step p _ _) g

l-whisk-morph : {B : Ty} {C D : Tm B} (X : Ty) → (p : s* X ≡ D)→ (f : Tm ([ B ] C ⇒ D)) →
  morph X (l-whisk-ty f X p)
l-whisk-morph X p f = morph-precomp (morph-id X) p f

r-whisk-morph : {B : Ty} {D E : Tm B} (X : Ty) → (p : t* X ≡ D) → (g : Tm ([ B ] D ⇒ E)) →
  morph X (r-whisk-ty g X p)
r-whisk-morph X p g = morph-postcomp (morph-id X) p g

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
ptw-htpy-comp Ψ Φ a = Comp (Ψ a) (Φ a)

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

mutual

  morph-r-unit :
    {B : Ty} (D : Tm B) → (B' : Ty) → (p : t* B' ≡ D) → morph (r-whisk-ty (Id D) B' p) B'
  morph-r-unit {B = B} D ([ _ ] C ⇒ D) (t*-base _ _) = morph-id ([ B ] C ⇒ D)
  morph-r-unit D ([ B' ] t ⇒ u) (t*-step p t u) =
    morph-precomp
      (morph-postcomp
        (shift
          (morph-r-unit D B' p)
          (r-whisk-ty (Id D) ([ B' ] t ⇒ u) (t*-step p _ _))
          (∂*-step _ _ _ _))
        (t*-base _ _)
        (ptw-htpy-r-unit D B' p u))
      (s*-base _ _)
      (Inv (ptw-htpy-r-unit D B' p t))

  ptw-htpy-r-unit : {B : Ty} (D : Tm B) → (B' : Ty) → (p : t* B' ≡ D) →
    ptw-htpy (morph-comp (morph-r-unit D B' p) (r-whisk-morph B' p (Id D))) (morph-id B')
  ptw-htpy-r-unit = r-unit-coh

  postulate
    r-unit-coh : {B : Ty} (D : Tm B) → (B' : Ty) → (p : t* B' ≡ D) → (b : Tm B') → Tm
      ([ B' ] morph-base (morph-r-unit D B' p) (morph-base (r-whisk-morph B' p (Id D)) b) ⇒
              morph-base (morph-id B') b)

  morph-r-assoc : {B : Ty} {D E F : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
    (B' : Ty) → (p : t* B' ≡ D) →
      morph
        ( r-whisk-ty (Comp h g) B' p)
        ( r-whisk-ty h (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p)) 
  morph-r-assoc {B = B} {F = F} g h ([ _ ] C ⇒ _) (t*-base _ _) = morph-id ([ B ] C ⇒ F)
  morph-r-assoc g h ([ B' ] t ⇒ u) (t*-step p t u) =
    morph-postcomp
      ( morph-precomp
        ( shift
          ( morph-r-assoc g h B' p)
          ( [ r-whisk-ty (Comp h g) B' p ]
            r-whisk-tm (Comp h g) B' p t ⇒
            r-whisk-tm (Comp h g) B' p u)
          ( ∂*-step _ _ _ _))
        ( s*-base _ _)
        ( Inv (ptw-htpy-r-assoc g h B' p t)))
      ( t*-base _ _)
      ( ptw-htpy-r-assoc g h B' p u)

  ptw-htpy-r-assoc : {B : Ty} {D E F : Tm B} (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
    (B' : Ty) → (p : t* B' ≡ D) →
      ptw-htpy
        ( morph-comp
          ( morph-r-assoc g h B' p)
          ( r-whisk-morph B' p (Comp h g)))
        ( morph-comp
          ( r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
          ( r-whisk-morph B' p g))
  ptw-htpy-r-assoc = r-assoc-coh

  postulate
    r-assoc-coh : {B : Ty} {D E F : Tm B} (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) → 
      (B' : Ty) → (p : t* B' ≡ D) → (b : Tm B') → 
        Tm
          ([ r-whisk-ty h (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) ]
            morph-base (morph-r-assoc g h B' p)
            (morph-base (r-whisk-morph B' p (Comp h g)) b) ⇒
            morph-base
            (r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
            (morph-base (r-whisk-morph B' p g) b))

  morph-r-assoc-inv : {B : Ty} {D E F : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
    (B' : Ty) → (p : t* B' ≡ D) →
      morph
        ( r-whisk-ty h (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p)) 
        ( r-whisk-ty (Comp h g) B' p)
  morph-r-assoc-inv {B = B} {F = F} g h ([ _ ] C ⇒ _) (t*-base C _) = morph-id ([ B ] C ⇒ F)
  morph-r-assoc-inv g h ([ B' ] t ⇒ u) (t*-step p t u) =
    morph-precomp
      ( morph-postcomp
        ( shift
          ( morph-r-assoc-inv g h B' p)
          ( r-whisk-ty
            ( h)
            ( r-whisk-ty g ([ B' ] t ⇒ u) (t*-step p _ _))
            ( t*-r-whisk-ty g ([ B' ] t ⇒ u) (t*-step p _ _)))
          ( ∂*-step _ _ _ _))
        ( t*-base _ _)
        ( ptw-htpy-r-assoc-inv g h B' p u))
      ( s*-base _ _)
      ( Inv (ptw-htpy-r-assoc-inv g h B' p t))

  ptw-htpy-r-assoc-inv : {B : Ty} {D E F : Tm B} (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
    (B' : Ty) → (p : t* B' ≡ D) →
      ptw-htpy
        ( morph-comp
          ( morph-r-assoc-inv g h B' p)
          ( morph-comp
            ( r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
            ( r-whisk-morph B' p g)))
        ( r-whisk-morph B' p (Comp h g))
  ptw-htpy-r-assoc-inv = r-assoc-inv-coh

  postulate
    r-assoc-inv-coh : {B : Ty} {D E F : Tm B} (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
      (B' : Ty) → (p : t* B' ≡ D) → (b : Tm B') → 
        Tm
          ([ r-whisk-ty (Comp h g) B' p ]
            morph-base (morph-r-assoc-inv g h B' p)
            (morph-base
              (r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
              (morph-base (r-whisk-morph B' p g) b))
            ⇒ morph-base (r-whisk-morph B' p (Comp h g)) b)

  morph-r-transport : {B : Ty} {D E : Tm B}  {g g' : Tm ([ B ] D ⇒ E)} (β : Tm ([ _ ] g ⇒ g')) →
    (B' : Ty) → (p : t* B' ≡ D) → morph (r-whisk-ty g B' p) (r-whisk-ty g' B' p)
  morph-r-transport {B = B} {E = E} β ([ _ ] C ⇒ _) (t*-base C _) = morph-id ([ B ] C ⇒ E)
  morph-r-transport {g = g} {g'} β ([ B' ] t ⇒ u) (t*-step p t u) =
    morph-precomp
      ( morph-postcomp
        ( shift
          ( morph-r-transport β B' p)
          ( r-whisk-ty g ([ B' ] t ⇒ u) (t*-step p _ _))
          ( ∂*-step _ _ _ _))
        ( t*-base _ _)
        ( ptw-htpy-r-transport β B' p u))
      ( s*-base _ _)
      ( Inv (ptw-htpy-r-transport β B' p t))
    
  ptw-htpy-r-transport : {B : Ty} {D E : Tm B}  {g g' : Tm ([ B ] D ⇒ E)}
    (β : Tm ([ _ ] g ⇒ g')) → (B' : Ty) → (p : t* B' ≡ D) →
    ptw-htpy
      ( morph-comp (morph-r-transport β B' p) (r-whisk-morph B' p g))
      ( r-whisk-morph B' p g')
  ptw-htpy-r-transport = r-transport-coh

  postulate
    r-transport-coh : {B : Ty} {D E : Tm B}  {g g' : Tm ([ B ] D ⇒ E)}
      (β : Tm ([ _ ] g ⇒ g')) → (B' : Ty) → (p : t* B' ≡ D) → (b : Tm B') → 
        Tm
          ([ r-whisk-ty g' B' p ]
            morph-base (morph-r-transport β B' p) (morph-base (r-whisk-morph B' p g) b) ⇒
            morph-base (r-whisk-morph B' p g') b)

category : Set
category = Tm ⋆

functor : (C D : category) → Set
functor C D = Tm ([ ⋆ ] C ⇒ D)

nat-iso : {C D : category} (F G : functor C D) → Set
nat-iso {C} {D} F G = Tm ([ [ ⋆ ] C ⇒ D ] F ⇒ G)

postulate 𝟙 : category
postulate 𝟙-proj : (A : Ty) → {t* A ≡ 𝟙} → Tm A

𝟙-proj-cat : (C : category) → functor C 𝟙
𝟙-proj-cat C = 𝟙-proj ([ ⋆ ] C ⇒ 𝟙) {t*-base _ _}

module prod-cons
  (C D : category)
  where

  postulate prod : category
  postulate pr₁-prod : functor prod C
  postulate pr₂-prod : functor prod D

open prod-cons public

module prod-intro
  {C D : category} {A : Ty} {p : t* A ≡ (prod C D)}
  (f : Tm (r-whisk-ty (pr₁-prod C D) A p)) (g : Tm (r-whisk-ty (pr₂-prod C D) A p))
  where

  postulate
    pair-prod : Tm A
  postulate
    coh₁-prod : Tm ([ r-whisk-ty (pr₁-prod C D) A p ] f ⇒ r-whisk-tm (pr₁-prod C D) A p pair-prod)
  postulate 
    coh₂-prod : Tm ([ r-whisk-ty (pr₂-prod C D) A p ] g ⇒ r-whisk-tm (pr₂-prod C D) A p pair-prod)

open prod-intro public

prod-fun : {C D C' D' : category} → functor C D  → functor C' D' → functor (prod C C') (prod D D')
prod-fun {C} {D} {C'} {D'} f g =
  pair-prod
    { p = t*-base (prod C C') (prod D D')}
    ( Comp f (pr₁-prod C C'))
    ( Comp g (pr₂-prod C C'))

module pullback-cons
  {C D E : category} (f : functor C E) (g : functor D E)
  where

  postulate pb : category
  postulate pr₁-pb : functor pb C
  postulate pr₂-pb : functor pb D
  postulate coh-univ : nat-iso (Comp f pr₁-pb) (Comp g pr₂-pb)

open pullback-cons public

module pullback-intro
  {C D E : category} (f : functor C E) (g : functor D E) (A : Ty) (p : t* A ≡ (pb f g))
  (t₁ : Tm (r-whisk-ty (pr₁-pb f g) A p)) (t₂ : Tm (r-whisk-ty (pr₂-pb f g) A p))
  (coh : Tm
            ([ (r-whisk-ty g (r-whisk-ty (pr₂-pb f g) A p) (t*-r-whisk-ty (pr₂-pb f g) A p)) ]
              morph-base
                ( morph-r-assoc (pr₂-pb f g) g A p)
                ( morph-base
                  ( morph-r-transport (coh-univ f g) A p)
                  ( morph-base
                    ( morph-r-assoc-inv (pr₁-pb f g) f A p)
                    ( r-whisk-tm f _ _ t₁)))
              ⇒
              r-whisk-tm g _ _ t₂))
  where

  postulate pair-pb : Tm A
  postulate coh₁-pb : Tm ([ r-whisk-ty (pr₁-pb f g) A p ] t₁ ⇒ r-whisk-tm (pr₁-pb f g) A p pair-pb)
  postulate coh₂-pb : Tm ([ r-whisk-ty (pr₂-pb f g) A p ] t₂ ⇒ r-whisk-tm (pr₂-pb f g) A p pair-pb)

  f⋆φC : Tm ([ _ ] _ ⇒ _)
  f⋆φC = r-whisk-tm f _ (t*-step (t*-r-whisk-ty (pr₁-pb f g) A p) _ _) coh₁-pb

  w : morph
        ( r-whisk-ty f (r-whisk-ty (pr₁-pb f g) A p) (t*-r-whisk-ty (pr₁-pb f g) _ _))
        ( r-whisk-ty g (r-whisk-ty (pr₂-pb f g) A p) (t*-r-whisk-ty (pr₂-pb f g) _ _))
  w = morph-comp
        ( morph-comp
          ( morph-r-assoc _ g _ _)
          ( morph-r-transport (coh-univ f g) _ _))
        ( morph-r-assoc-inv _ f _ _)

  w⟨f⋆φC⟩ : Tm ([ _ ] _ ⇒ _)
  w⟨f⋆φC⟩ = morph-base (shift w _ (∂*-step _ _ _ (∂*-base _))) f⋆φC

  can : Tm ([ r-whisk-ty g (r-whisk-ty (pr₂-pb f g) A p) (t*-r-whisk-ty (pr₂-pb f g) A p) ] _ ⇒ _)
  can =
    Comp
      ( ptw-htpy-r-assoc (pr₂-pb f g) g A p pair-pb)
      ( morph-base
        ( shift (morph-r-assoc (pr₂-pb f g) g A p) _ (∂*-step _ _ _ (∂*-base _)))
        ( Comp
          ( ptw-htpy-r-transport (coh-univ f g) A p pair-pb)
            ( morph-base
              ( shift (morph-r-transport (coh-univ f g) A p) _ (∂*-step _ _ _ (∂*-base _)))
              ( ptw-htpy-r-assoc-inv (pr₁-pb f g) f A p pair-pb))))

  postulate
    coh₃-pb :
      Tm ([ _ ]
          Comp (r-whisk-tm g _ (t*-step (t*-r-whisk-ty _ _ _) _ _) coh₂-pb) coh ⇒
          Comp can w⟨f⋆φC⟩)

src : (A : Ty) → (t u : Tm A) → category
src ⋆ t u = t
src ([ A ] x ⇒ y) _ _ = src A x y

src-eq : (A : Ty) → (t u : Tm A) → s* [ A ] t ⇒ u ≡ src A t u
src-eq ⋆ C D = s*-base _ _
src-eq ([ A ] x ⇒ y) t u = s*-step (src-eq A x y) t u

tgt : (A : Ty) → (t u : Tm A) → category
tgt ⋆ t u = u
tgt ([ A ] x ⇒ y) _ _ = tgt A x y

tgt-eq : (A : Ty) → (t u : Tm A) → t* [ A ] t ⇒ u ≡ tgt A t u
tgt-eq ⋆ C D = t*-base _ _
tgt-eq ([ A ] x ⇒ y) t u = t*-step (tgt-eq A x y) t u

mutual

  snd-prod-ty : (C : category) → (A : Ty) → (t u : Tm A) → Ty
  snd-prod-ty C ⋆ D E = [ ⋆ ] prod C D ⇒ prod C E
  snd-prod-ty C ([ A ] x ⇒ y) t u =
    [ snd-prod-ty C A x y ] snd-prod-tm C A x y t ⇒ snd-prod-tm C A x y u

  snd-prod-tm : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm (snd-prod-ty C A t u)
  snd-prod-tm C A t u α = pair-prod (snd-prod-comm₁ C A t u) (snd-prod-comm₂ C A t u α)

  snd-prod-ty-tgt : (C : category) → (A : Ty) → (t u : Tm A) →
    t* (snd-prod-ty C A t u) ≡ (prod C (tgt A t u))
  snd-prod-ty-tgt C ⋆ D E = t*-base _ _
  snd-prod-ty-tgt C ([ A ] x ⇒ y) t u = t*-step (snd-prod-ty-tgt C A x y) _ _

  snd-prod-comm₁ : (C : category) → (A : Ty) → (t u : Tm A) →
    Tm (r-whisk-ty (pr₁-prod C (tgt A t u)) (snd-prod-ty C A t u) (snd-prod-ty-tgt C A t u))
  snd-prod-comm₁ C ⋆ D E = pr₁-prod C D
  snd-prod-comm₁ C ([ A ] x ⇒ y) t u =
    Comp (snd-prod-iso₁ C A x y u) (Inv (snd-prod-iso₁ C A x y t))

  snd-prod-comm₂ : (C : category) → (A : Ty) → (t u : Tm A) → (β : Tm ([ A ] t ⇒ u)) →
    Tm (r-whisk-ty (pr₂-prod C (tgt A t u)) (snd-prod-ty C A t u) (snd-prod-ty-tgt C A t u))
  snd-prod-comm₂ C ⋆ D E f = Comp f (pr₂-prod C D)
  snd-prod-comm₂ C ([ A ] x ⇒ y) f g β =
    Comp
      ( snd-prod-iso₂ C A x y g)
      ( Comp
        ( snd-prod-coh C f g)
        ( Inv (snd-prod-iso₂ C A x y f)))

  postulate
    snd-prod-coh : (C : category) → {A : Ty} → {x y : Tm A} → (f g : Tm ([ A ] x ⇒ y)) →
      Tm ([ _ ] snd-prod-comm₂ C A x y f ⇒ snd-prod-comm₂ C A x y g)

  snd-prod-iso₁ : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        snd-prod-comm₁ C A t u ⇒
        r-whisk-tm (pr₁-prod C _) _ (snd-prod-ty-tgt C A t u) (snd-prod-tm C A t u α))
  snd-prod-iso₁ C A t u α = coh₁-prod _ _

  snd-prod-iso₂ : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        snd-prod-comm₂ C A t u α ⇒
        r-whisk-tm (pr₂-prod C (tgt A t u)) _ (snd-prod-ty-tgt C A t u) (snd-prod-tm C A t u α))
  snd-prod-iso₂ C A t u α = coh₂-prod _ _

mutual

  fst-prod-ty : (C : category) → (A : Ty) → (t u : Tm A) → Ty
  fst-prod-ty C ⋆ D E = [ ⋆ ] prod D C ⇒ prod E C
  fst-prod-ty C ([ A ] x ⇒ y) t u =
    [ fst-prod-ty C A x y ] fst-prod-tm C A x y t ⇒ fst-prod-tm C A x y u

  fst-prod-tm : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm (fst-prod-ty C A t u)
  fst-prod-tm C A t u α = pair-prod (fst-prod-comm₁ C A t u α) (fst-prod-comm₂ C A t u)

  fst-prod-ty-tgt : (C : category) → (A : Ty) → (t u : Tm A) →
    t* (fst-prod-ty C A t u) ≡ (prod (tgt A t u) C)
  fst-prod-ty-tgt C ⋆ D E = t*-base _ _
  fst-prod-ty-tgt C ([ A ] x ⇒ y) t u = t*-step (fst-prod-ty-tgt C A x y) _ _

  fst-prod-comm₂ : (C : category) → (A : Ty) → (t u : Tm A) →
    Tm (r-whisk-ty (pr₂-prod (tgt A t u) C) (fst-prod-ty C A t u) (fst-prod-ty-tgt C A t u))
  fst-prod-comm₂ C ⋆ D E = pr₂-prod D C
  fst-prod-comm₂ C ([ A ] x ⇒ y) t u =
    Comp (fst-prod-iso₂ C A x y u) (Inv (fst-prod-iso₂ C A x y t))

  fst-prod-comm₁ : (C : category) → (A : Ty) → (t u : Tm A) → (β : Tm ([ A ] t ⇒ u)) →
    Tm (r-whisk-ty (pr₁-prod (tgt A t u) C) (fst-prod-ty C A t u) (fst-prod-ty-tgt C A t u))
  fst-prod-comm₁ C ⋆ D E f = Comp f (pr₁-prod D C)
  fst-prod-comm₁ C ([ A ] x ⇒ y) f g β =
    Comp
      ( fst-prod-iso₁ C A x y g)
      ( Comp
        ( fst-prod-coh C f g)
        ( Inv (fst-prod-iso₁ C A x y f)))

  postulate
    fst-prod-coh : (C : category) → {A : Ty} → {x y : Tm A} → (f g : Tm ([ A ] x ⇒ y)) →
      Tm ([ _ ] fst-prod-comm₁ C A x y f ⇒ fst-prod-comm₁ C A x y g)

  fst-prod-iso₂ : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        fst-prod-comm₂ C A t u ⇒
        r-whisk-tm (pr₂-prod _ C) _ (fst-prod-ty-tgt C A t u) (fst-prod-tm C A t u α))
  fst-prod-iso₂ C A t u α = coh₂-prod _ _

  fst-prod-iso₁ : (C : category) → (A : Ty) → (t u : Tm A) → (α : Tm ([ A ] t ⇒ u)) →
    Tm ([ _ ]
        fst-prod-comm₁ C A t u α ⇒
        r-whisk-tm (pr₁-prod (tgt A t u) C) _ (fst-prod-ty-tgt C A t u) (fst-prod-tm C A t u α))
  fst-prod-iso₁ C A t u α = coh₁-prod _ _

module functoror-categoryegory-cons
  (C D : category)
  where

  postulate fun-cat : category
  postulate ev : Tm ([ ⋆ ] prod fun-cat C ⇒ D)

open functoror-categoryegory-cons public

∂ₜ : (A : Ty) → {C : category} → (p : t* A ≡ C) → Ty
∂ₜ ([ _ ] _ ⇒ _) (t*-base _ _) = ⋆
∂ₜ ([ A ] _ ⇒ _) (t*-step _ _ _) = A

∂ₜ⁺ : (A : Ty) → {C : category} → (p : t* A ≡ C) → Tm (∂ₜ A p)
∂ₜ⁺ ([ _ ] _ ⇒ u) (t*-base _ _) = u
∂ₜ⁺ ([ _ ] _ ⇒ u) (t*-step _ _ _) = u

∂ₜ⁻ : (A : Ty) → {C : category} → (p : t* A ≡ C) → Tm (∂ₜ A p)
∂ₜ⁻ ([ _ ] t ⇒ _) (t*-base _ _) = t
∂ₜ⁻ ([ _ ] t ⇒ _) (t*-step _ _ _) = t

t*-fst-prod : (C D : category) → (A : Ty) → (p : t* A ≡ D) →
  t* fst-prod-ty C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p) ≡ prod D C
t*-fst-prod C D ([ .⋆ ] x ⇒ .D) (t*-base .x .D) = t*-base _ _
t*-fst-prod C D ([ [ .⋆ ] t ⇒ .D ] x ⇒ y) (t*-step (t*-base .t .D) .x .y) =
  t*-step (t*-base _ _) _ _
t*-fst-prod C D ([ [ A ] t ⇒ u ] x ⇒ y) (t*-step (t*-step p .t .u) .x .y) =
  t*-step (t*-fst-prod C D ([ A ] t ⇒ u) (t*-step p t u)) _ _

deconstructₜ : (A : Ty) → {C : category} → (p : t* A ≡ C) → Tm A → Tm ([ ∂ₜ A p ] ∂ₜ⁻ A p ⇒ ∂ₜ⁺ A p)
deconstructₜ .([ ⋆ ] C ⇒ _) (t*-base C _) α = α
deconstructₜ .([ _ ] t ⇒ u) (t*-step p t u) α = α

constructₜ : (A : Ty) → {C : category} → (p : t* A ≡ C) → Tm ([ ∂ₜ A p ] ∂ₜ⁻ A p ⇒ ∂ₜ⁺ A p) → Tm A
constructₜ .([ ⋆ ] C ⇒ _) (t*-base C _) α = α
constructₜ .([ _ ] t ⇒ u) (t*-step p t u) α = α

module functor-category-intro
  {C D : category} {A : Ty} {p : t* A ≡ fun-cat C D}
  (f : Tm
        ( r-whisk-ty
          ( ev C D)
          ( fst-prod-ty C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p))
          ( t*-fst-prod C (fun-cat C D) A p)))
  where

  postulate fun-cat-curry : Tm A
  postulate
    fun-cat-coh :
      Tm ([ _ ]
            f ⇒
            ( r-whisk-tm
              ( ev C D)
              ( fst-prod-ty C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p))
              ( t*-fst-prod C (fun-cat C D) A p)
              ( fst-prod-tm C (∂ₜ A p) (∂ₜ⁻ A p) (∂ₜ⁺ A p) (deconstructₜ A p fun-cat-curry))))

open functor-category-intro public

fun-cat-uncurry : {T C D : category} → functor T (fun-cat C D) → functor (prod T C) D
fun-cat-uncurry {T} {C} {D} g = Comp (ev C D) (prod-fun g (Id C))

fun-precomp : {C C' D : category} → functor C C' → functor (fun-cat C' D) (fun-cat C D)
fun-precomp {C} {C'} {D} f =
  fun-cat-curry {p = t*-base _ _} (Comp (ev C' D) (prod-fun (Id (fun-cat C' D)) f))

fun-postcomp : {C D D' : category} → functor D D' → functor (fun-cat C D) (fun-cat C D')
fun-postcomp {C} {D} {D'} g = fun-cat-curry {p = t*-base _ _} (Comp g (ev C D))

sec : {C D : category} → functor C D → Set
sec {C} {D} f = Σ (functor D C) (λ s → nat-iso (Comp f s) (Id D))

ret : {C D : category} → functor C D → Set
ret {C} {D} f = Σ (functor D C) (λ r → nat-iso (Comp r f) (Id C))

equiv : (C D : category) → Set
equiv C D = Σ (functor C D) (λ f → sec f × ret f)

𝟙-prod-r-unit-equiv : (C : category) → equiv (prod C 𝟙) C
𝟙-prod-r-unit-equiv C =
  (pr₁-prod C 𝟙) ,
  (pair-prod {p = t*-base _ _} (Id C) (𝟙-proj-cat C) , Inv  (coh₁-prod (Id C) (𝟙-proj-cat C))) ,
  (pair-prod {p = t*-base _ _} (Id C) (𝟙-proj-cat C) , {!   !})

𝟙-fun-cat-equiv : (C : category) → equiv (fun-cat 𝟙 C) C
𝟙-fun-cat-equiv C = {!   !} , {!   !}

postulate [1] : category
postulate d₀ : functor [1] 𝟙
postulate d₁ : functor [1] 𝟙

is-grpd : category → Set
is-grpd C =
  Σ ( functor (fun-cat [1] C) C)
    ( λ s → nat-iso (Comp (fun-precomp (𝟙-proj-cat [1])) {! s  !}) {!   !})

-- module groupoid-core-cons
--   where
