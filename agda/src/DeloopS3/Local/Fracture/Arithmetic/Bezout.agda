{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Arithmetic.Bezout where

-- Bézout matrices on double loops.  The second row of
-- the invertible matrix forgets the pullback path.  Thus EVERY filler
-- gives an equivalence, without identifying any two fillers.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPathrEquiv ; compPathlEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP ; Σ-cong-equiv ; Σ-cong-equiv-snd ; Σ-assoc-Iso)
import Cubical.Data.Int as Z
open import Cubical.Homotopy.Loopspace using (Ω ; EH)
open import DeloopS3.Local.Base using (powLoop)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (PB)
open import DeloopS3.Local.Fracture.Arithmetic.IntegerLoops

record Bezout (m n : ℕ) : Type where
  constructor bezout
  field
    a b : Z.ℤ
    identity : a Z.· Z.pos m Z.+ b Z.· Z.pos n ≡ Z.pos 1

bezout-3-10 : Bezout 3 10
bezout-3-10 = bezout (Z.pos 7) (Z.negsuc 1) refl

module Matrix (X : Pointed ℓ-zero) (m n : ℕ) (bez : Bezout m n) where
  private
    mm = Z.pos m
    nn = Z.pos n
  open Bezout bez
  open CommutativeLoops (typ (Ω X)) (pt (Ω X)) (EH {A = X} 0)

  M N : Y × Y → Y × Y
  M (x , y) = linear mm (Z.- nn) x y , linear b a x y
  N (u , v) = linear a nn u v , linear (Z.- b) mm u v

  private
    diag₁ : mm Z.· a Z.+ (Z.- nn) Z.· (Z.- b) ≡ Z.pos 1
    diag₁ = cong₂ Z._+_ (Z.·Comm mm a)
      (sym (Z.-DistLR· nn b) ∙ Z.·Comm nn b) ∙ identity
    diag₂ : b Z.· nn Z.+ a Z.· mm ≡ Z.pos 1
    diag₂ = Z.+Comm (b Z.· nn) (a Z.· mm) ∙ identity
    off₁ : mm Z.· nn Z.+ (Z.- nn) Z.· mm ≡ Z.pos 0
    off₁ = cong (mm Z.· nn Z.+_)
      (sym (Z.-DistL· nn mm) ∙ cong Z.-_ (Z.·Comm nn mm))
      ∙ Z.-Cancel (mm Z.· nn)
    off₂ : b Z.· a Z.+ a Z.· (Z.- b) ≡ Z.pos 0
    off₂ = cong (b Z.· a Z.+_)
      (sym (Z.-DistR· a b) ∙ cong Z.-_ (Z.·Comm a b))
      ∙ Z.-Cancel (b Z.· a)
    diag₃ : a Z.· mm Z.+ nn Z.· b ≡ Z.pos 1
    diag₃ = cong (a Z.· mm Z.+_) (Z.·Comm nn b) ∙ identity
    diag₄ : (Z.- b) Z.· (Z.- nn) Z.+ mm Z.· a ≡ Z.pos 1
    diag₄ = cong₂ Z._+_ (sym (Z.-DistLR· b nn)) (Z.·Comm mm a) ∙ diag₂
    off₃ : a Z.· (Z.- nn) Z.+ nn Z.· a ≡ Z.pos 0
    off₃ = cong₂ Z._+_ (sym (Z.-DistR· a nn)) (Z.·Comm nn a)
      ∙ Z.-Cancel' (a Z.· nn)
    off₄ : (Z.- b) Z.· mm Z.+ mm Z.· b ≡ Z.pos 0
    off₄ = cong₂ Z._+_ (sym (Z.-DistL· b mm)) (Z.·Comm mm b)
      ∙ Z.-Cancel' (b Z.· mm)

    row₁ : (c d : Z.ℤ) → c ≡ Z.pos 1 → d ≡ Z.pos 0
      → (x y : Y) → linear c d x y ≡ x
    row₁ c d ec ed x y = cong₂ (λ c d → linear c d x y) ec ed
      ∙ sym (rUnit (scalar (Z.pos 1) x)) ∙ scalar-one x
    row₂ : (c d : Z.ℤ) → c ≡ Z.pos 0 → d ≡ Z.pos 1
      → (x y : Y) → linear c d x y ≡ y
    row₂ c d ec ed x y = cong₂ (λ c d → linear c d x y) ec ed
      ∙ sym (lUnit (scalar (Z.pos 1) y)) ∙ scalar-one y

  MN : (z : Y × Y) → M (N z) ≡ z
  MN (x , y) = ΣPathP
    ((linear-expand mm (Z.- nn) a nn (Z.- b) mm x y
      ∙ row₁ _ _ diag₁ off₁ x y) ,
     (linear-expand b a a nn (Z.- b) mm x y
      ∙ row₂ _ _ off₂ diag₂ x y))

  NM : (z : Y × Y) → N (M z) ≡ z
  NM (x , y) = ΣPathP
    ((linear-expand a nn mm (Z.- nn) b a x y
      ∙ row₁ _ _ diag₃ off₃ x y) ,
     (linear-expand (Z.- b) mm mm (Z.- nn) b a x y
      ∙ row₂ _ _ off₄ diag₄ x y))

  matrixEquiv : (Y × Y) ≃ (Y × Y)
  matrixEquiv = isoToEquiv (iso M N MN NM)

  D : Y × Y → Y
  D z = fst (M z)

  private
    translate : (x y : Y) → (powLoop m x ≡ powLoop n y) ≃ (D (x , y) ≡ refl)
    translate x y = compEquiv
      (compr≡Equiv (powLoop m x) (powLoop n y) (sym (powLoop n y)))
      (compEquiv (compPathrEquiv (rCancel (powLoop n y)))
        (compPathlEquiv (cong (powLoop m x ∙_) (scalar-neg nn y))))

    toDifference : PB (powLoop {X = typ (Ω X)} {x = refl} m)
      (powLoop {X = typ (Ω X)} {x = refl} n) ≃ fiber D refl
    toDifference = compEquiv
      (Σ-cong-equiv-snd (λ x → Σ-cong-equiv-snd (translate x)))
      (isoToEquiv (invIso Σ-assoc-Iso))

    firstRow : fiber D refl ≃ fiber (fst {A = Y} {B = λ _ → Y}) refl
    firstRow = Σ-cong-equiv matrixEquiv (λ z → idEquiv (D z ≡ refl))

    projection : Iso (fiber (fst {A = Y} {B = λ _ → Y}) refl) Y
    Iso.fun projection ((u , v) , p) = v
    Iso.inv projection v = (refl , v) , refl
    Iso.sec projection v = refl
    Iso.ret projection ((u , v) , p) i = (p (~ i) , v) , λ j → p (~ i ∨ j)

  -- The carrier is literally b*x+a*y; it never inspects the path.
  second-row-equivalence : PB (powLoop {X = typ (Ω X)} {x = refl} m)
    (powLoop {X = typ (Ω X)} {x = refl} n) ≃ Y
  second-row-equivalence = compEquiv toDifference
    (compEquiv firstRow (isoToEquiv projection))

  second-row-β : (x y : Y) (p : powLoop m x ≡ powLoop n y)
    → fst second-row-equivalence (x , y , p) ≡ linear b a x y
  second-row-β x y p = refl

  gap-isEquiv : (h : (z : Y) → powLoop m (powLoop n z) ≡ powLoop n (powLoop m z))
    → isEquiv (λ z → (powLoop n z , powLoop m z , h z))
  gap-isEquiv h = isEquiv[equivFunA≃B∘f]→isEquiv[f]
    (λ z → (powLoop n z , powLoop m z , h z)) second-row-equivalence
    (subst isEquiv (sym (funExt composite)) (idIsEquiv Y))
    where
    composite : (z : Y) → linear b a (powLoop n z) (powLoop m z) ≡ z
    composite z = cong₂ _∙_ (sym (scalar-mul b nn z)) (sym (scalar-mul a mm z))
      ∙ sym (scalar-add (b Z.· nn) (a Z.· mm) z)
      ∙ cong (λ k → scalar k z) diag₂ ∙ scalar-one z

double-power-square : (X : Pointed ℓ-zero) (m n : ℕ) → Bezout m n
  → (h : (z : typ (Ω (Ω X)))
    → powLoop m (powLoop n z) ≡ powLoop n (powLoop m z))
  → isEquiv {B = PB (powLoop {X = typ (Ω X)} {x = refl} m)
      (powLoop {X = typ (Ω X)} {x = refl} n)}
      (λ z → (powLoop n z , powLoop m z , h z))
double-power-square = Matrix.gap-isEquiv
