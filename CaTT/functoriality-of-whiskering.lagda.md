```agda
{-# OPTIONS --guardedness #-}

open import CaTT.CaTT
open import CaTT.coherences
open import CaTT.whiskering
open import CaTT.type-morphisms
open import CaTT.lax-transformations
```

```agda
module CaTT.functoriality-of-whiskering where
```

The operation of right (left) whiskering is functorial in the following sense.
- For every type B' with t* B' ≡ D, we have a morphism u_D : id_D ⋆ B' ⇝ B' together with a
  pointwise homotopy u_D ∘ rw_{id_D} ⇒ id_B'.
- For every type B' with t* B' ≡ D, where D : B, and terms g : [ B ] D ⇒ E and h : [ B ] E ⇒ F,
  we have a morphism a_{g,h} : (h ∘ g) ⋆ B' ⇝ h ⋆ (g ⋆ B') together with a pointwise homotopy
  a_{g,h} ∘ rw_{g∘h} ⇒ rw_h ∘ rw_g.
- For every type B' with t* B' ≡ D, where D : B, and terms g g' : [ B ] D ⇒ E and a term
  β : [ [ B ] D ⇒ E ] g ⇒ g', we have a morphism tr_β : g ⋆ B' ⇝ g' ⋆ B' together with a
  pointwise homotopy tr_β ∘ rw_g ⇒ rw_g'.

```agda
mutual

  r-unit-morph :
    {B : Ty} (D : Tm B) → (B' : Ty) → (p : t* B' ≡ D) → ty-morph (r-whisk-ty (Id D) B' p) B'
  r-unit-morph {B = B} D ([ _ ] C ⇒ D) base = id-ty-morph ([ B ] C ⇒ D)
  r-unit-morph D ([ [ B' ] x ⇒ y ] t ⇒ u) (step p) =
    precomp-morph
      ( postcomp-morph
        ( shift
          ( r-unit-morph D ([ B' ] x ⇒ y) p)
          ( r-whisk-ty (Id D) ([ [ B' ] x ⇒ y ] t ⇒ u) (step p))
          ( step base))
        ( base)
        ( r-unit-lax-trans D ([ B' ] x ⇒ y) p u))
      ( base)
      ( Inv (r-unit-lax-trans D ([ B' ] x ⇒ y) p t))

  r-unit-lax-trans : {B : Ty} (D : Tm B) → (B' : Ty) → (p : t* B' ≡ D) →
    lax-trans (ty-morph-comp (r-unit-morph D B' p) (r-whisk-morph B' p (Id D))) (id-ty-morph B')
  r-unit-lax-trans D .([ _ ] _ ⇒ D) base = Left-unit-law
  r-unit-lax-trans D .([ _ ] _ ⇒ _) (step p) = R-unit-coh D _ (step p)

  r-unit-lax-trans-inv : {B : Ty} (D : Tm B) → (B' : Ty) → (p : t* B' ≡ D) →
    lax-trans (ty-morph-comp (r-whisk-morph B' p (Id D)) (r-unit-morph D B' p)) (id-ty-morph _)
  r-unit-lax-trans-inv D .([ _ ] _ ⇒ D) base = Left-unit-law
  r-unit-lax-trans-inv D .([ _ ] _ ⇒ _) (step p) = R-unit-coh-inv D _ (step p)
  
  postulate
    R-unit-coh : {B : Ty} (D : Tm B) → (B' : Ty) → (p : t* B' ≡ D) → (b : Tm B') → Tm
      ([ B' ] ty-morph-base (r-unit-morph D B' p) (ty-morph-base (r-whisk-morph B' p (Id D)) b) ⇒
              ty-morph-base (id-ty-morph B') b)

  postulate
    R-unit-coh-inv : {B : Ty} (D : Tm B) → (B' : Ty) → (p : t* B' ≡ D) → (b : Tm _) → Tm
      ([ _ ] ty-morph-base (r-whisk-morph B' p (Id D)) (ty-morph-base (r-unit-morph D B' p) b) ⇒
              ty-morph-base (id-ty-morph _) b)

  r-assoc-morph : {B : Ty} {D E F : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
    (B' : Ty) → (p : t* B' ≡ D) →
      ty-morph
        ( r-whisk-ty (Comp h g) B' p)
        ( r-whisk-ty h (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p)) 
  r-assoc-morph {B = B} {F = F} g h ([ _ ] C ⇒ _) base = id-ty-morph ([ B ] C ⇒ F)
  r-assoc-morph g h ([ [ B' ] x ⇒ y ] t ⇒ u) (step base) =
    precomp-morph
      ( postcomp-morph
        ( shift
          ( r-assoc-morph g h ([ B' ] x ⇒ y) base)
          ( [ _ ] r-whisk-tm (Comp h g) t base ⇒ r-whisk-tm (Comp h g) u base)
          ( step base))
        ( base)
        ( r-assoc-lax-trans g h ([ B' ] x ⇒ y) base u))
      ( base)
      ( Inv (r-assoc-lax-trans g h ([ B' ] x ⇒ y) base t))
  r-assoc-morph g h ([ [ B' ] x ⇒ y ] t ⇒ u) (step (step p)) =
    precomp-morph
      ( postcomp-morph
        ( shift
          ( r-assoc-morph g h ([ B' ] x ⇒ y) (step p))
          ( [ _ ] r-whisk-tm (Comp h g) t (step p) ⇒ r-whisk-tm (Comp h g) u (step p))
          ( step base))
        ( base)
        ( r-assoc-lax-trans g h ([ B' ] x ⇒ y) (step p) u))
      ( base)
      ( Inv (r-assoc-lax-trans g h ([ B' ] x ⇒ y) (step p) t))

  r-assoc-lax-trans : {B : Ty} {D E F : Tm B} (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
    (B' : Ty) → (p : t* B' ≡ D) →
      lax-trans
        ( ty-morph-comp
          ( r-assoc-morph g h B' p)
          ( r-whisk-morph B' p (Comp h g)))
        ( ty-morph-comp
          ( r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
          ( r-whisk-morph B' p g))
  r-assoc-lax-trans g h .([ _ ] _ ⇒ _) base = λ α → Inv (Assoc _ _ _)
  r-assoc-lax-trans g h .([ _ ] _ ⇒ _) (step p) = R-assoc-coh _ _ _ (step p)

  postulate
    R-assoc-coh : {B : Ty} {D E F : Tm B} (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) → 
      (B' : Ty) → (p : t* B' ≡ D) → (b : Tm B') → 
        Tm
          ([ r-whisk-ty h (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) ]
            ty-morph-base (r-assoc-morph g h B' p)
            (ty-morph-base (r-whisk-morph B' p (Comp h g)) b) ⇒
            ty-morph-base
            (r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
            (ty-morph-base (r-whisk-morph B' p g) b))

  r-assoc-morph-inv : {B : Ty} {D E F : Tm B} → (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
    (B' : Ty) → (p : t* B' ≡ D) →
      ty-morph
        ( r-whisk-ty h (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p)) 
        ( r-whisk-ty (Comp h g) B' p)
  r-assoc-morph-inv {B = B} {F = F} g h ([ _ ] C ⇒ _) base = id-ty-morph ([ B ] C ⇒ F)
  r-assoc-morph-inv g h ([ [ B' ] x ⇒ y ] t ⇒ u) (step base) =
    precomp-morph
      ( postcomp-morph
        ( shift
          ( r-assoc-morph-inv g h ([ B' ] x ⇒ y) base)
          ( r-whisk-ty
            ( h)
            ( r-whisk-ty g ([ _ ] t ⇒ u) (step _))
            ( t*-r-whisk-ty g ([ _ ] t ⇒ u) (step _)))
          ( step base))
        ( base)
        ( r-assoc-lax-trans-inv g h ([ B' ] x ⇒ y) base u))
      ( base)
      ( Inv (r-assoc-lax-trans-inv g h ([ B' ] x ⇒ y) base t))
  r-assoc-morph-inv g h ([ [ B' ] x ⇒ y ] t ⇒ u) (step (step p)) =
    precomp-morph
      ( postcomp-morph
        ( shift
          ( r-assoc-morph-inv g h ([ B' ] x ⇒ y) (step p))
          ( r-whisk-ty
            ( h)
            ( r-whisk-ty g ([ _ ] t ⇒ u) (step _))
            ( t*-r-whisk-ty g ([ _ ] t ⇒ u) (step _)))
          ( step base))
        ( base)
        ( r-assoc-lax-trans-inv g h ([ B' ] x ⇒ y) (step p) u))
      ( base)
      ( Inv (r-assoc-lax-trans-inv g h ([ B' ] x ⇒ y) (step p) t))

  r-assoc-lax-trans-inv : {B : Ty} {D E F : Tm B} (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
    (B' : Ty) → (p : t* B' ≡ D) →
      lax-trans
        ( ty-morph-comp
          ( r-assoc-morph-inv g h B' p)
          ( ty-morph-comp
            ( r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
            ( r-whisk-morph B' p g)))
        ( r-whisk-morph B' p (Comp h g))
  r-assoc-lax-trans-inv g h .([ _ ] _ ⇒ _) base = λ α → Assoc _ _ _
  r-assoc-lax-trans-inv g h .([ _ ] _ ⇒ _) (step p) = R-assoc-inv-coh _ _ _ (step p)

  postulate
    R-assoc-inv-coh : {B : Ty} {D E F : Tm B} (g : Tm ([ B ] D ⇒ E)) → (h : Tm ([ B ] E ⇒ F)) →
      (B' : Ty) → (p : t* B' ≡ D) → (b : Tm B') → 
        Tm
          ([ r-whisk-ty (Comp h g) B' p ]
            ty-morph-base (r-assoc-morph-inv g h B' p)
            ( ty-morph-base
              ( r-whisk-morph (r-whisk-ty g B' p) (t*-r-whisk-ty g B' p) h)
              ( ty-morph-base (r-whisk-morph B' p g) b))
            ⇒ ty-morph-base (r-whisk-morph B' p (Comp h g)) b)

  r-transport-morph : {B : Ty} {D E : Tm B}  {g g' : Tm ([ B ] D ⇒ E)} (β : Tm ([ _ ] g ⇒ g')) →
    (B' : Ty) → (p : t* B' ≡ D) → ty-morph (r-whisk-ty g B' p) (r-whisk-ty g' B' p)
  r-transport-morph {B = B} {E = E} β ([ _ ] C ⇒ _) base = id-ty-morph ([ B ] C ⇒ E)
  r-transport-morph {g = g} {g'} β ([ [ B' ] x ⇒ y ] t ⇒ u) (step base) =
    precomp-morph
      ( postcomp-morph
        ( shift
          ( r-transport-morph β ([ B' ] x ⇒ y) base)
          ( r-whisk-ty g ([ [ B' ] x ⇒ y ] t ⇒ u) (step base))
          ( step base))
        ( base)
        ( r-transport-lax-trans β ([ B' ] x ⇒ y) base u))
      ( base)
      ( Inv (r-transport-lax-trans β ([ B' ] x ⇒ y) base t))
  r-transport-morph {g = g} {g'} β ([ [ B' ] x ⇒ y ] t ⇒ u) (step (step p)) =
    precomp-morph
      ( postcomp-morph
        ( shift
          ( r-transport-morph β ([ B' ] x ⇒ y) (step p))
          ( r-whisk-ty g ([ [ B' ] x ⇒ y ] t ⇒ u) (step (step p)))
          ( step base))
        ( base)
        ( r-transport-lax-trans β ([ B' ] x ⇒ y) (step p) u))
      ( base)
      ( Inv (r-transport-lax-trans β ([ B' ] x ⇒ y) (step p) t))
    
  r-transport-lax-trans : {B : Ty} {D E : Tm B}  {g g' : Tm ([ B ] D ⇒ E)}
    (β : Tm ([ _ ] g ⇒ g')) → (B' : Ty) → (p : t* B' ≡ D) →
    lax-trans
      ( ty-morph-comp (r-transport-morph β B' p) (r-whisk-morph B' p g))
      ( r-whisk-morph B' p g')
  r-transport-lax-trans β .([ _ ] _ ⇒ _) base = λ α → l-whisk-tm α β (step base)
  r-transport-lax-trans β .([ _ ] _ ⇒ _) (step p) = R-transport-coh _ _ (step p)

  postulate
    R-transport-coh : {B : Ty} {D E : Tm B}  {g g' : Tm ([ B ] D ⇒ E)}
      (β : Tm ([ _ ] g ⇒ g')) → (B' : Ty) → (p : t* B' ≡ D) → (b : Tm B') → 
        Tm
          ([ r-whisk-ty g' B' p ]
            ty-morph-base (r-transport-morph β B' p) (ty-morph-base (r-whisk-morph B' p g) b) ⇒
            ty-morph-base (r-whisk-morph B' p g') b)
```