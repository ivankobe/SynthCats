```agda
open import CaTT.CaTT
open import CaTT.whiskering
```

```agda
module CaTT.commutative-squares-pasting where
```

In a type A, given two commutative squares

  x ---f----> y           y ---g----> a
  |           |           |           |
  p           q           q           r
  |    ⇗φ     |           ∣    ⇗ψ     |
  v           v           v           v
  z ---u----> w           w ---v----> b

together with isomorphisms ψφ as indicated, we construct an isomorphism filling the composite rectangle.

```agda
square-pasting : {B : Ty} {x y a z w b : Tm B} {f : Tm ([ _ ] x ⇒ y)} {g : Tm ([ _ ] y ⇒ a)}
  {u : Tm ([ _ ] z ⇒ w)} {v : Tm ([ _ ] w ⇒ b)} {p : Tm ([ _ ] x ⇒ z)} {q : Tm ([ _ ] y ⇒ w)}
  {r : Tm ([ _ ] a ⇒ b)} (φ : Tm ([ _ ] Comp u p ⇒ Comp q f)) →
  (ψ : Tm ([ _ ] Comp v q ⇒ Comp r g)) → Tm ([ _ ] Comp (Comp v u) p ⇒ Comp r (Comp g f))
square-pasting {f = f} {v = v} φ ψ =
  Comp
    ( Comp
      ( Comp
        (Comp
          ( Inv (Assoc _ _ _))
          ( l-whisk-tm f ψ (step base)))
        ( Assoc _ _ _))
      ( r-whisk-tm v φ (step base)))
    ( Inv (Assoc _ _ _))
```

We now do the same for three squares. Note that there is a handedness to this operation in choosing
the way of associating the horisontal composites.

  x ---f----> y       y ---g----> a       a ---h----> c
  |           |       |           |       |           |
  p           q       q           r       r           s
  |    ⇗φ     |       ∣    ⇗ψ     |       |     ⇗χ    |
  v           v       v           v       v           v
  z ---u----> w       w ---v----> b       b ---m----> d.

```agda
3-square-pasting-left-assoc :  {B : Ty} {x y a c z w b d : Tm B} {f : Tm ([ _ ] x ⇒ y)}
  {g : Tm ([ _ ] y ⇒ a)} {h : Tm ([ _ ] a ⇒ c)} {u : Tm ([ _ ] z ⇒ w)} {v : Tm ([ _ ] w ⇒ b)}
  {m : (Tm ([ _ ] b ⇒ d))} {p : Tm ([ _ ] x ⇒ z)} {q : Tm ([ _ ] y ⇒ w)} {r : Tm ([ _ ] a ⇒ b)}
  {s : Tm ([ _ ] c ⇒ d)} (φ : Tm ([ _ ] Comp u p ⇒ Comp q f)) →
  (ψ : Tm ([ _ ] Comp v q ⇒ Comp r g)) → (χ : Tm( [ _ ] Comp m r ⇒ Comp s h)) →
    Tm ([ _ ] Comp (Comp m (Comp v u)) p ⇒ Comp s (Comp h (Comp g f)))
3-square-pasting-left-assoc φ ψ χ = square-pasting (square-pasting φ ψ) χ

3-square-pasting-right-assoc :  {B : Ty} {x y a c z w b d : Tm B} {f : Tm ([ _ ] x ⇒ y)}
  {g : Tm ([ _ ] y ⇒ a)} {h : Tm ([ _ ] a ⇒ c)} {u : Tm ([ _ ] z ⇒ w)} {v : Tm ([ _ ] w ⇒ b)}
  {m : (Tm ([ _ ] b ⇒ d))} {p : Tm ([ _ ] x ⇒ z)} {q : Tm ([ _ ] y ⇒ w)} {r : Tm ([ _ ] a ⇒ b)}
  {s : Tm ([ _ ] c ⇒ d)} (φ : Tm ([ _ ] Comp u p ⇒ Comp q f)) →
  (ψ : Tm ([ _ ] Comp v q ⇒ Comp r g)) → (χ : Tm( [ _ ] Comp m r ⇒ Comp s h)) →
    Tm ([ _ ] Comp (Comp (Comp m v) u) p ⇒ Comp s (Comp (Comp h g) f))
3-square-pasting-right-assoc φ ψ χ = square-pasting φ (square-pasting ψ χ)
```

If the horizontal maps in a commutative square in a type B are invertible, then inverting them also
yields a commutative square.

  x ---f----> y           y --f^-1--> x
  |           |           |           |
  p           q           q           p
  |    ⇗      |           ∣    ⇗      |
  v           v           v           v
  z ---g----> w           w --g^-1--> y.

Two special cases of this are:
  - if B is of nonzero dimension
  - if B = ⋆ and f and g are equivalences.

```agda
square-iso-inv : {B : Ty} {b b' : Tm B} {x y z w : Tm ([ _ ] b ⇒ b')} (f : arr x y) →
  (g : arr z w) → (p : arr x z) → (q : arr y w) → arr (Comp g p) (Comp q f) →
    arr (Comp (Inv g) q) (Comp p (Inv f))
square-iso-inv  {y = y} {z = z} f g p q φ = 
  Inv
    ( Comp ( Right-unit-law _)
      ( Comp (r-whisk-tm _ (Inv-is-sec f) (step base))
        ( Comp (Inv (Assoc _ _ _))
          ( l-whisk-tm _ (Comp (Assoc _ _ _)
            ( Comp
              ( Comp
                ( Comp
                  ( r-whisk-tm (Inv g) φ (step base))
                  ( Inv (Assoc _ _ _)))
                ( l-whisk-tm p (Inv (Inv-is-ret g)) (step base)))
              ( Inv (Left-unit-law p))))
            ( step base)))))
```


H : gp ≅ qf
------------
g^-1gpf^-1 = g^-1qff^-1

W : g^-1q ≅ pf^-1