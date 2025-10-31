```agda
{-# OPTIONS --guardedness #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import CaTT.CaTT
open import CaTT.commutative-squares-pasting
open import CaTT.type-morphisms
open import CaTT.whiskering
open import CaTT.functoriality-of-whiskering
open import CaTT.commutative-squares-pasting
open import Synthetic-categories.synthetic-categories

module Constructions.pullbacks where
```

The datatype of cones over a cospan.

```agda
module _
  {C D E : cat} (f : fun C E) (g : fun D E)
  where

  record cone : Set where
    field
      cone-apex : cat
      cone-fst : fun cone-apex C
      cone-snd : fun cone-apex D
      cone-coh : nat-iso (Comp f cone-fst) (Comp g cone-snd)

  open cone public
```

We postulate the existence of pullbacks.

```agda
module pullback-cons
  {C D E : cat} (f : fun C E) (g : fun D E)
  where

  postulate pb : cone f g

open pullback-cons public
```

The components of a pullback 

```agda
coh-pb-ty : {C D E : cat} {f : fun C E} {g : fun D E} {A : Ty} (c : cone f g) →
  (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
  (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → Ty
coh-pb-ty {f = f} {g} {A} c p t₁ t₂ =
  [ (r-whisk-ty g (r-whisk-ty (cone-snd c) A p) (t*-r-whisk-ty (cone-snd c) A p)) ]
    ty-morph-base
      ( r-assoc-morph (cone-snd c) g A p)
      ( ty-morph-base
        ( r-transport-morph (cone-coh c) A p)
        ( ty-morph-base
          ( r-assoc-morph-inv (cone-fst c) f A p)
          ( r-whisk-tm f t₁ _)))
    ⇒
    r-whisk-tm g t₂ _


module pullback-intro'
  {C D E : cat} {f : fun C E} {g : fun D E}
  where

  coh₁-pb-ty : (A : Ty) → (c : cone f g) → (p : t* A ≡ (cone-apex c)) →
    (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) → (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → 
    (coh : Tm (coh-pb-ty c p t₁ t₂)) → Tm A → Ty
  coh₁-pb-ty A c p t₁ t₂ coh a = [ r-whisk-ty (cone-fst c) A p ] t₁ ⇒ r-whisk-tm (cone-fst c) a p

  coh₂-pb-ty : (A : Ty) → (c : cone f g) → (p : t* A ≡ (cone-apex c)) →
    (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) → (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → 
    (coh : Tm (coh-pb-ty c p t₁ t₂)) → Tm A → Ty
  coh₂-pb-ty A c p t₁ t₂ coh a = [ r-whisk-ty (cone-snd c) A p ] t₂ ⇒ r-whisk-tm (cone-snd c) a p

  coh₃-pb-ty : (A : Ty) → (c : cone f g) → (p : t* A ≡ (cone-apex c)) →
    (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) → (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → 
    (coh : Tm (coh-pb-ty c p t₁ t₂)) → (a : Tm A) → Tm (coh₁-pb-ty A c p t₁ t₂ coh a) → 
    Tm (coh₂-pb-ty A c p t₁ t₂ coh a) → Ty
  coh₃-pb-ty ([ A ] x ⇒ y) c p t₁ t₂ coh a coh₁ coh₂ = 
    [ _ ]
    Comp (r-whisk-tm g coh₂ (step (t*-r-whisk-ty _ _ _))) coh ⇒
    Comp
      ( Comp
        ( r-assoc-lax-trans (cone-snd c) g _ p a)
        ( ty-morph-base
          ( shift (r-assoc-morph (cone-snd c) g _ p) _ (step base))
          ( Comp
            ( r-transport-lax-trans (cone-coh c) _ p a)
              ( ty-morph-base
                ( shift (r-transport-morph (cone-coh c) _ p) _ (step base))
                ( r-assoc-lax-trans-inv (cone-fst c) f _ p a)))))
      ( ty-morph-base
        ( shift
          ( ty-morph-comp
            ( ty-morph-comp
              ( r-assoc-morph _ g _ _)
              ( r-transport-morph (cone-coh c) _ _))
            ( r-assoc-morph-inv _ f _ _))
          _ 
          ( step base))
        ( r-whisk-tm f coh₁ (step (t*-r-whisk-ty (cone-fst c) _ p))))

open pullback-intro' public
```

We postulate that pullbacks satisfy a universal property.

```agda
module pullback-intro
  {C D E : cat} {f : fun C E} {g : fun D E} (A : Ty)
  (p : t* A ≡ (cone-apex (pb f g))) (t₁ : Tm (r-whisk-ty (cone-fst (pb f g)) A p))
  (t₂ : Tm (r-whisk-ty (cone-snd (pb f g)) A p)) (coh : Tm (coh-pb-ty (pb f g) p t₁ t₂))
  where

  postulate pair-pb : Tm A
  postulate coh₁-pb : Tm (coh₁-pb-ty A (pb f g) p t₁ t₂ coh pair-pb)
  postulate coh₂-pb : Tm (coh₂-pb-ty A (pb f g) p t₁ t₂ coh pair-pb)
  postulate coh₃-pb : Tm (coh₃-pb-ty A (pb f g) p t₁ t₂ coh pair-pb coh₁-pb coh₂-pb)

open pullback-intro public
```

The predicate of a cone being a pullback 

```agda
module _
  {C D E : cat} {f : fun C E} {g : fun D E}
  where

  record is-pb (c : cone f g) : Set where
    field
      pair :
        (A : Ty) → (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) →
          Tm A
      coh₁ :
        (A : Ty) → (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) → 
          Tm (coh₁-pb-ty A c p t₁ t₂ coh (pair A p t₁ t₂ coh))
      coh₂ :
        (A : Ty) → (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) → 
          Tm (coh₂-pb-ty A c p t₁ t₂ coh (pair A p t₁ t₂ coh))
      coh₃ :
        (A : Ty) → (p : t* A ≡ (cone-apex c)) → (t₁ : Tm (r-whisk-ty (cone-fst c) A p)) →
        (t₂ : Tm (r-whisk-ty (cone-snd c) A p)) → (coh : Tm (coh-pb-ty c p t₁ t₂)) → 
          Tm (coh₃-pb-ty A c p t₁ t₂ coh (pair A p t₁ t₂ coh) (coh₁ A p t₁ t₂ _) (coh₂ A p t₁ t₂ _))

pb-is-pb : {C D E : cat} (f : fun C E) → (g : fun D E) → is-pb (pb f g)
pb-is-pb f g = record {
  pair = pair-pb ;
  coh₁ = coh₁-pb ;
  coh₂ = coh₂-pb ;
  coh₃ = coh₃-pb }
```

The datatype of cone diagrams, of isos of cone diagrams, and of isos of those isos.

```agda
module _
  {C D E : cat} (f : fun C E) (g : fun D E) (T : cat)
  where

  record cone-diagram : Set where
    field
      cone-diagram-fst : fun T C
      cone-diagram-snd : fun T D
      cone-diagram-coh : nat-iso (Comp f cone-diagram-fst) (Comp g cone-diagram-snd)

  open cone-diagram public
```

```
module _
  {C D E T : cat} {f : fun C E} {g : fun D E}
  where

  record cone-diagram-iso (c c' : cone-diagram f g T) : Set where
    field
      cone-diagram-iso-fst : nat-iso (cone-diagram-fst c) (cone-diagram-fst c')
      cone-diagram-iso-snd : nat-iso (cone-diagram-snd c) (cone-diagram-snd c')
      cone-diagram-iso-coh :
        3-iso
          ( Comp
            ( cone-diagram-coh c')
            ( r-whisk-tm f cone-diagram-iso-fst (step base)))
          ( Comp
            ( r-whisk-tm g cone-diagram-iso-snd (step base))
            ( cone-diagram-coh c))
  
  open cone-diagram-iso public
```

```agda
module _
  {C D E T : cat} {f : fun C E} {g : fun D E} {c c' : cone-diagram f g T}
  where

  record cone-diagram-iso-iso (Φ Ψ : cone-diagram-iso c c') : Set where
    field
      cone-diagram-iso-iso-fst : 3-iso (cone-diagram-iso-fst Φ) (cone-diagram-iso-fst Ψ)
      cone-diagram-iso-iso-snd : 3-iso (cone-diagram-iso-snd Φ) (cone-diagram-iso-snd Ψ)
      cone-diagram-iso-iso-coh :
        4-iso
          ( Comp
            ( cone-diagram-iso-coh Ψ)
            ( r-whisk-tm
              ( cone-diagram-coh c')
              ( r-whisk-tm f cone-diagram-iso-iso-fst (step (step base)))
              ( step base)))
          ( Comp
            ( l-whisk-tm
              ( cone-diagram-coh c)
              ( r-whisk-tm g cone-diagram-iso-iso-snd (step (step base)))
              ( step base))
            ( cone-diagram-iso-coh Φ))
  
  open cone-diagram-iso-iso public
```

Given a functor s: S → T and a cone diagram c = (t₁, t₂, τ) on T we obtain another cone
diagram s^∗(c) := (t₁ ◦ s, t₂ ◦ s, τ ∗ id_s). Similarly, every natural isomorphism s_1 ≅ s_2
of functors 𝑆 → 𝑇 induces an isomorphism s_1^∗(c) ≅ s_2^∗(c) of cone diagrams.

** whiskering of cone diagrams **

```agda
base-change-cone-diagram : {C D E T S : cat} {f : fun C E} {g : fun D E}
  (c : cone-diagram f g T) → (s : fun S T) → cone-diagram f g S
base-change-cone-diagram {f = f} {g} c s = record
  { cone-diagram-fst = Comp (cone-diagram-fst c) s
  ; cone-diagram-snd = Comp (cone-diagram-snd c) s
  ; cone-diagram-coh =
      Comp
        ( Inv (Assoc s (cone-diagram-snd c) g))
        ( Comp
          ( l-whisk-fun s (cone-diagram-coh c))
          ( Assoc s (cone-diagram-fst c) f))
  }
```

Similarly, every natural isomorphism s_1 ≅ s_2 of functors 𝑆 → 𝑇 induces an isomorphism
s_1^∗(c) ≅ s_2^∗(c) of cone diagrams. To see this, we need a two new coherences, one showing that
right whiskering is compatible with associativity isomorphisms, i.e. that for be a type B,
terms a, b, b', b'' : B, morphisms f : b ⇒ b', g : b' ⇒ b'' and s,s' : a ⇒ b', and an isomorphism
φ : s ⇒ s', there is an isomorphism ((gf)⋆φ)∘a ≅ a∘(f⋆(g⋆φ)), where a is the associativity
isomorphism. The other coherence we need is the one showing that codimension-2-composition is
compatible with whiskering in the sense that given a diagram


      ------f-----   ------g----
    /             🡖 /           🡖
    C     ⇓φ       D      ⇓ψ     E
    \             🡕 \           🡕
      ------f'----   ------g'---

in a type B, the square

  gf ===== ψ⋆f ====> g'f 
  ||                  ||
  ||                  ||
  g⋆φ                 g'⋆φ
  ||                  ||
  ||                  ||
  v                   v
  gf' ==== ψ⋆f' ====> g'f'

commutes.

```agda
postulate
  r-whisk-assoc-coh : {B : Ty} {a b b' b'' : Tm B} (f : Tm ([ _ ] b ⇒ b')) →
    (g : Tm ([ _ ] b' ⇒ b'')) → {s s' : Tm ([ _ ] a ⇒ b)} → (φ : Tm ([ _ ] s ⇒ s')) →
      Tm ([ _ ]
        ( Comp
          ( Assoc _ _ _)
          ( r-whisk-tm g (r-whisk-tm f φ (step base)) (step base))) ⇒
        ( Comp
          ( r-whisk-tm (Comp g f) φ (step base))
          ( Assoc _ _ _)))

r-whisk-assoc-inv-coh : {B : Ty} {a b b' b'' : Tm B} (f : Tm ([ _ ] b ⇒ b')) →
  (g : Tm ([ _ ] b' ⇒ b'')) → {s s' : Tm ([ _ ] a ⇒ b)} → (φ : Tm ([ _ ] s ⇒ s')) →
    Tm ([ _ ]
      Comp
        ( Inv (Assoc _ _ _))
        ( r-whisk-tm (Comp g f) φ (step base)) ⇒
      Comp
        ( r-whisk-tm g (r-whisk-tm f φ (step base)) (step base))
        ( Inv (Assoc _ _ _)))
r-whisk-assoc-inv-coh f g φ =
  square-iso-inv
    ( _)
    ( _)
    ( r-whisk-tm g (r-whisk-tm f φ (step base)) (step base))
    ( r-whisk-tm (Comp g f) φ (step base))
    ( r-whisk-assoc-coh _ _ _)


postulate
  codim-2-comp-whisk-coh : {B : Ty} {C D E : Tm B} {f f' : Tm ([ _ ] C ⇒ D)}
    {g g' : Tm ([ _ ] D ⇒ E)} (φ : Tm ([ _ ] f ⇒ f')) → (ψ : Tm ([ _ ] g ⇒ g')) →
      Tm ([ _ ]
        Comp
          ( l-whisk-tm f' ψ (step base))
          ( r-whisk-tm g φ (step base)) ⇒
        Comp
          ( r-whisk-tm g' φ (step base))
          ( l-whisk-tm f ψ (step base)))

base-change-cone-diagram-iso : {C D E T S : cat} {f : fun C E} {g : fun D E}
  {c : cone-diagram f g T} {s s' : fun S T} (φ : nat-iso s s') →
    cone-diagram-iso (base-change-cone-diagram c s) (base-change-cone-diagram c s')
base-change-cone-diagram-iso {f = f} {g = g} {c = c} φ = record
  { cone-diagram-iso-fst = r-whisk-tm (cone-diagram-fst c) φ (step base)
  ; cone-diagram-iso-snd = r-whisk-tm (cone-diagram-snd c) φ (step base)
  ; cone-diagram-iso-coh =
      3-square-pasting-left-assoc
        ( r-whisk-assoc-coh (cone-diagram-fst c) f φ)
        ( codim-2-comp-whisk-coh φ (cone-diagram-coh c))
        ( r-whisk-assoc-inv-coh (cone-diagram-snd c) g φ)
  }
```

```agda
module _
  {C D E : cat}
  where

  cone-diagram-of-cone : {f : fun C E} {g : fun D E} (c : cone f g) → cone-diagram f g (cone-apex c)
  cone-diagram-of-cone c = record
    { cone-diagram-fst = cone-fst c ; 
      cone-diagram-snd = cone-snd c ; 
      cone-diagram-coh = cone-coh c }

  pb' : (f : fun C E) → (g : fun D E) →  cone-diagram f g (cone-apex (pb f g))
  pb' f g = cone-diagram-of-cone (pb f g)
```

```agda
module _
  {C D E T : cat} {f : fun C E} {g : fun D E}
  where 

  pb-ax₁ : cone-diagram f g T → fun T (cone-apex (pb f g))
  pb-ax₁ c = pair-pb (arrty _ _) base (cone-diagram-fst c) (cone-diagram-snd c) (cone-diagram-coh c)

  pb-ax₂ : (c : cone-diagram f g T) → cone-diagram-iso c (base-change-cone-diagram (pb' f g) (pb-ax₁ c))
  pb-ax₂ c = record
    { cone-diagram-iso-fst =
        coh₁-pb _ base (cone-diagram-fst c) (cone-diagram-snd c) (cone-diagram-coh c)
    ; cone-diagram-iso-snd =
        coh₂-pb _ base (cone-diagram-fst c) (cone-diagram-snd c) (cone-diagram-coh c)
    ; cone-diagram-iso-coh = 
        Inv (coh₃-pb _ base (cone-diagram-fst c) (cone-diagram-snd c) (cone-diagram-coh c))
    }

  pb-ax₃ : {T : cat} {s t : fun T (cone-apex (pb f g))} →
    cone-diagram-iso (base-change-cone-diagram (pb' f g) s) (base-change-cone-diagram (pb' f g) t) →
      nat-iso s t
  pb-ax₃ {s = s} {t} Φ =
    pair-pb
      ( [ _ ] s ⇒ t)
      ( step base)
      ( cone-diagram-iso-fst Φ) 
      ( cone-diagram-iso-snd Φ)
      ( inv-reassoc-pb (cone-diagram-iso-coh Φ))

  pb-ax₄ : {T : cat} {s t : fun T (cone-apex (pb f g))} → 
    (Φ : cone-diagram-iso
      ( base-change-cone-diagram (pb' f g) s)
      ( base-change-cone-diagram (pb' f g) t)) →
      cone-diagram-iso-iso Φ (base-change-cone-diagram-iso (pb-ax₃ Φ))
  pb-ax₄ Φ = record
    { cone-diagram-iso-iso-fst =
        coh₁-pb
          ( _)
          ( step base)
          ( cone-diagram-iso-fst Φ)
          ( cone-diagram-iso-snd Φ)
          ( inv-reassoc-pb (cone-diagram-iso-coh Φ))
    ; cone-diagram-iso-iso-snd =
        coh₂-pb
          (  _)
          ( step base)
          ( cone-diagram-iso-fst Φ)
          ( cone-diagram-iso-snd Φ)
          ( inv-reassoc-pb (cone-diagram-iso-coh Φ))
    ; cone-diagram-iso-iso-coh = {! coh₃-pb !}
    }    

```