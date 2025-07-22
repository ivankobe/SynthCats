```agda
{-# OPTIONS --guardedness #-}

open import CaTT
open import whiskering
open import type-morphisms
open import pointwise-homotopies
open import synthetic-categories

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
        ( r-whisk-ty (comp h g) B' p)
        ( r-whisk-ty h (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p)) 
  morph-r-assoc {B = B} {F = F} g h ([ _ ] C ⇒ _) (t*-base _ _) = morph-id ([ B ] C ⇒ F)
  morph-r-assoc g h ([ B' ] t ⇒ u) (t*-step p t u) =
    morph-postcomp
      ( morph-precomp
        ( shift
          ( morph-r-assoc g h B' p)
          ( [ r-whisk-ty (comp h g) B' p ]
            r-whisk-tm (comp h g) B' p t ⇒
            r-whisk-tm (comp h g) B' p u)
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
          ( r-whisk-morph B' p (comp h g)))
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
            (morph-base (r-whisk-morph B' p (comp h g)) b) ⇒
            morph-base
            (r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
            (morph-base (r-whisk-morph B' p g) b))

  morph-r-assoc-inv : {B : Ty} {D E F : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
    (B' : Ty) → (p : t* B' ≡ D) →
      morph
        ( r-whisk-ty h (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p)) 
        ( r-whisk-ty (comp h g) B' p)
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
        ( r-whisk-morph B' p (comp h g))
  ptw-htpy-r-assoc-inv = r-assoc-inv-coh

  postulate
    r-assoc-inv-coh : {B : Ty} {D E F : Tm B} (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
      (B' : Ty) → (p : t* B' ≡ D) → (b : Tm B') → 
        Tm
          ([ r-whisk-ty (comp h g) B' p ]
            morph-base (morph-r-assoc-inv g h B' p)
            (morph-base
              (r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
              (morph-base (r-whisk-morph B' p g) b))
            ⇒ morph-base (r-whisk-morph B' p (comp h g)) b)

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
```