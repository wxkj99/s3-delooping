{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.SpanPi1.WordAlgebra where

-- Noncommutative group-law calculations valid in every group.
-- These simplify words independently of the geometric covering maps.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (module GroupTheory)

module Words {ℓ} (G : Group ℓ) where
  open GroupStr (snd G)
  open GroupTheory G

  square cube fifth : fst G → fst G
  square a = a · a
  cube a = (a · a) · a
  fifth a = square a · cube a

  z : fst G → fst G → fst G
  z x y = inv y · x

  -- Retain the literal words BEFORE the simplifications below.
  schreier-O : fst G → fst G → fst G
  schreier-O x y = (y · y) · inv x

  schreier-I : fst G → fst G → fst G
  schreier-I x y = ((cube (x · inv y) · inv x) · inv y) · x

  abstract
    inv-times-cube : (a : fst G) → inv a · cube a ≡ square a
    inv-times-cube a = cong (inv a ·_) (sym (·Assoc a a a))
      ∙ ·Assoc (inv a) a (square a)
      ∙ cong (_· square a) (·InvL a) ∙ ·IdL (square a)

    O-word : (x y : fst G) → square x ≡ cube y
      → schreier-O x y ≡ z x y
    O-word x y rel = ·CancelR x
      (sym (·Assoc (square y) (inv x) x)
       ∙ cong (square y ·_) (·InvL x) ∙ ·IdR (square y)
       ∙ sym (sym (·Assoc (inv y) x x)
         ∙ cong (inv y ·_) rel ∙ inv-times-cube y))

    O-kill : (x y : fst G) → square x ≡ cube y
      → schreier-O x y ≡ 1g → (x ≡ 1g) × (y ≡ 1g)
    O-kill x y rel kill = xy ∙ y-one , y-one
      where
      xy : x ≡ y
      xy = invUniqueR (sym (O-word x y rel) ∙ kill) ∙ invInv y
      y-one : y ≡ 1g
      y-one = ·CancelL (square y)
        (sym (cong square (sym xy) ∙ rel) ∙ sym (·IdR (square y)))

    conjugate-mul : (a b c : fst G)
      → ((a · b) · inv a) · ((a · c) · inv a)
        ≡ (a · (b · c)) · inv a
    conjugate-mul a b c =
      ((a · b) · inv a) · ((a · c) · inv a)
        ≡⟨ cong (((a · b) · inv a) ·_) (sym (·Assoc a c (inv a)))
           ∙ ·Assoc ((a · b) · inv a) a (c · inv a)
           ∙ cong (_· (c · inv a)) (sym (·Assoc (a · b) (inv a) a)) ⟩
      ((a · b) · (inv a · a)) · (c · inv a)
        ≡⟨ cong (λ t → ((a · b) · t) · (c · inv a)) (·InvL a) ⟩
      ((a · b) · 1g) · (c · inv a)
        ≡⟨ cong (_· (c · inv a)) (·IdR (a · b))
           ∙ ·Assoc (a · b) c (inv a)
           ∙ cong (_· inv a) (sym (·Assoc a b c)) ⟩
      (a · (b · c)) · inv a ∎

    conjugate-cube : (a b : fst G)
      → cube ((a · b) · inv a) ≡ (a · cube b) · inv a
    conjugate-cube a b =
      cong (_· ((a · b) · inv a)) (conjugate-mul a b b)
      ∙ conjugate-mul a (square b) b

    conjugate-z : (x y : fst G) → (x · z x y) · inv x ≡ x · inv y
    conjugate-z x y =
      (x · (inv y · x)) · inv x
        ≡⟨ cong (_· inv x) (·Assoc x (inv y) x)
           ∙ sym (·Assoc (x · inv y) x (inv x)) ⟩
      (x · inv y) · (x · inv x)
        ≡⟨ cong ((x · inv y) ·_) (·InvR x) ⟩
      (x · inv y) · 1g ≡⟨ ·IdR (x · inv y) ⟩
      x · inv y ∎

    -- The intermediate x z³ x⁻² z is recorded literally.  In particular
    -- the inverse square is NOT dropped as if the central fibre were 1.
    I-word-unsimplified : (x y : fst G)
      → schreier-I x y ≡ ((x · cube (z x y)) · inv (square x)) · z x y
    I-word-unsimplified x y =
      cong (λ t → ((t · inv x) · inv y) · x)
        (cong cube (sym (conjugate-z x y)) ∙ conjugate-cube x (z x y))
      ∙ ( ((((x · cube (z x y)) · inv x) · inv x) · inv y) · x
          ≡⟨ sym (·Assoc (((x · cube (z x y)) · inv x) · inv x) (inv y) x)
             ∙ cong (_· (inv y · x))
                 (sym (·Assoc (x · cube (z x y)) (inv x) (inv x))) ⟩
        ((x · cube (z x y)) · (inv x · inv x)) · (inv y · x)
          ≡⟨ cong (λ t → ((x · cube (z x y)) · t) · z x y)
               (sym (invDistr x x)) ⟩
        ((x · cube (z x y)) · inv (square x)) · z x y ∎ )

    cube-inverse-fifth : (a : fst G)
      → (cube a · inv (fifth a)) · a ≡ inv a
    cube-inverse-fifth a =
      cong (λ t → (cube a · t) · a) (invDistr (square a) (cube a))
      ∙ cong (_· a) (·Assoc (cube a) (inv (cube a)) (inv (square a)))
      ∙ cong (λ t → (t · inv (square a)) · a) (·InvR (cube a))
      ∙ cong (_· a) (·IdL (inv (square a)))
      ∙ cong (_· a) (invDistr a a)
      ∙ sym (·Assoc (inv a) (inv a) a)
      ∙ cong (inv a ·_) (·InvL a) ∙ ·IdR (inv a)

    x-inverse-z : (x y : fst G) → x · inv (z x y) ≡ y
    x-inverse-z x y = cong (x ·_) (invDistr (inv y) x)
      ∙ ·Assoc x (inv x) (inv (inv y))
      ∙ cong (_· inv (inv y)) (·InvR x)
      ∙ ·IdL (inv (inv y)) ∙ invInv y

    I-word : (x y : fst G) → square x ≡ fifth (z x y)
      → schreier-I x y ≡ y
    I-word x y rel = I-word-unsimplified x y
      ∙ cong (λ t → ((x · cube (z x y)) · inv t) · z x y) rel
      ∙ ( ((x · cube (z x y)) · inv (fifth (z x y))) · z x y
          ≡⟨ cong (_· z x y)
               (sym (·Assoc x (cube (z x y)) (inv (fifth (z x y)))))
             ∙ sym (·Assoc x (cube (z x y) · inv (fifth (z x y))) (z x y)) ⟩
        x · ((cube (z x y) · inv (fifth (z x y))) · z x y)
          ≡⟨ cong (x ·_) (cube-inverse-fifth (z x y)) ⟩
        x · inv (z x y) ≡⟨ x-inverse-z x y ⟩ y ∎ )

    I-kill : (x y : fst G) → square x ≡ cube y
      → square x ≡ fifth (z x y) → schreier-I x y ≡ 1g
      → (x ≡ 1g) × (y ≡ 1g)
    I-kill x y rel₂ rel₅ kill = x-one , y-one
      where
      y-one : y ≡ 1g
      y-one = sym (I-word x y rel₅) ∙ kill
      x-square : square x ≡ 1g
      x-square = rel₂ ∙ cong cube y-one
        ∙ cong (_· 1g) (·IdL 1g) ∙ ·IdL 1g
      zx : z x y ≡ x
      zx = cong (λ t → inv t · x) y-one
        ∙ cong (_· x) inv1g ∙ ·IdL x
      x-fifth : fifth x ≡ 1g
      x-fifth = sym (cong fifth zx) ∙ sym rel₅ ∙ x-square
      fifth-reduction : fifth x ≡ x
      fifth-reduction = cong₂ _·_ x-square (cong (_· x) x-square)
        ∙ ·IdL (1g · x) ∙ ·IdL x
      x-one : x ≡ 1g
      x-one = sym fifth-reduction ∙ x-fifth
