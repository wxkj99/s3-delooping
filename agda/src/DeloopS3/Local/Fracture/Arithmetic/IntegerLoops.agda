{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Arithmetic.IntegerLoops where

-- Finite integer powers.  The carrier is NOT assumed to be a set.
-- Only concatenation laws and the supplied commutative homotopy are used.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
import Cubical.Data.Int as Z
open import DeloopS3.Local.Base using (powLoop)

module CommutativeLoops (A : Type) (a : A)
  (comm : (x y : a ≡ a) → x ∙ y ≡ y ∙ x) where

  Y : Type
  Y = a ≡ a

  swap : (x y z : Y) → x ∙ (y ∙ z) ≡ y ∙ (x ∙ z)
  swap x y z = assoc x y z ∙ cong (_∙ z) (comm x y) ∙ sym (assoc y x z)

  interchange : (w x y z : Y) → (w ∙ x) ∙ (y ∙ z) ≡ (w ∙ y) ∙ (x ∙ z)
  interchange w x y z = sym (assoc w x (y ∙ z))
    ∙ cong (w ∙_) (swap x y z) ∙ assoc w y (x ∙ z)

  cancel : (x y : Y) → x ∙ (sym x ∙ y) ≡ y
  cancel x y = assoc x (sym x) y ∙ cong (_∙ y) (rCancel x) ∙ sym (lUnit y)

  power-sym : (n : ℕ) (x : Y) → powLoop n (sym x) ≡ sym (powLoop n x)
  power-sym zero x = refl
  power-sym (suc n) x = cong (sym x ∙_) (power-sym n x)
    ∙ comm (sym x) (sym (powLoop n x)) ∙ sym (symDistr x (powLoop n x))

  power-distrib : (n : ℕ) (x y : Y)
    → powLoop n (x ∙ y) ≡ powLoop n x ∙ powLoop n y
  power-distrib zero x y = lUnit refl
  power-distrib (suc n) x y = cong ((x ∙ y) ∙_) (power-distrib n x y)
    ∙ interchange x y (powLoop n x) (powLoop n y)

  scalar : Z.ℤ → Y → Y
  scalar (Z.pos n) x = powLoop n x
  scalar (Z.negsuc n) x = powLoop (suc n) (sym x)

  scalar-suc : (k : Z.ℤ) (x : Y) → scalar (Z.sucℤ k) x ≡ x ∙ scalar k x
  scalar-suc (Z.pos n) x = refl
  scalar-suc (Z.negsuc zero) x = sym (cancel x refl)
  scalar-suc (Z.negsuc (suc n)) x = sym (cancel x (powLoop (suc n) (sym x)))

  scalar-pred : (k : Z.ℤ) (x : Y) → scalar (Z.predℤ k) x ≡ sym x ∙ scalar k x
  scalar-pred (Z.pos zero) x = refl
  scalar-pred (Z.pos (suc n)) x = sym (cancel (sym x) (powLoop n x))
  scalar-pred (Z.negsuc n) x = refl

  scalar-add : (k l : Z.ℤ) (x : Y)
    → scalar (k Z.+ l) x ≡ scalar k x ∙ scalar l x
  scalar-add k (Z.pos zero) x = rUnit (scalar k x)
  scalar-add k (Z.pos (suc n)) x = scalar-suc (k Z.+ Z.pos n) x
    ∙ cong (x ∙_) (scalar-add k (Z.pos n) x) ∙ swap x (scalar k x) (powLoop n x)
  scalar-add k (Z.negsuc zero) x = scalar-pred k x
    ∙ comm (sym x) (scalar k x) ∙ cong (scalar k x ∙_) (rUnit (sym x))
  scalar-add k (Z.negsuc (suc n)) x = scalar-pred (k Z.+ Z.negsuc n) x
    ∙ cong (sym x ∙_) (scalar-add k (Z.negsuc n) x)
    ∙ swap (sym x) (scalar k x) (scalar (Z.negsuc n) x)

  scalar-neg : (k : Z.ℤ) (x : Y) → scalar (Z.- k) x ≡ sym (scalar k x)
  scalar-neg (Z.pos zero) x = refl
  scalar-neg (Z.pos (suc n)) x = power-sym (suc n) x
  scalar-neg (Z.negsuc n) x = sym (cong sym (power-sym (suc n) x))

  scalar-mul : (k l : Z.ℤ) (x : Y)
    → scalar (k Z.· l) x ≡ scalar k (scalar l x)
  scalar-mul (Z.pos zero) l x = refl
  scalar-mul (Z.pos (suc n)) l x = scalar-add l (Z.pos n Z.· l) x
    ∙ cong (scalar l x ∙_) (scalar-mul (Z.pos n) l x)
  scalar-mul (Z.negsuc zero) l x = scalar-neg l x ∙ rUnit (sym (scalar l x))
  scalar-mul (Z.negsuc (suc n)) l x = scalar-add (Z.- l) (Z.negsuc n Z.· l) x
    ∙ cong₂ _∙_ (scalar-neg l x) (scalar-mul (Z.negsuc n) l x)

  scalar-distrib : (k : Z.ℤ) (x y : Y)
    → scalar k (x ∙ y) ≡ scalar k x ∙ scalar k y
  scalar-distrib (Z.pos n) x y = power-distrib n x y
  scalar-distrib (Z.negsuc n) x y =
    cong (powLoop (suc n)) (symDistr x y ∙ comm (sym y) (sym x))
    ∙ power-distrib (suc n) (sym x) (sym y)

  scalar-one : (x : Y) → scalar (Z.pos 1) x ≡ x
  scalar-one x = sym (rUnit x)

  linear : (c d : Z.ℤ) → Y → Y → Y
  linear c d x y = scalar c x ∙ scalar d y

  linear-expand : (c d e f g h : Z.ℤ) (x y : Y)
    → linear c d (linear e f x y) (linear g h x y)
      ≡ linear (c Z.· e Z.+ d Z.· g) (c Z.· f Z.+ d Z.· h) x y
  linear-expand c d e f g h x y =
    cong₂ _∙_ (scalar-distrib c (scalar e x) (scalar f y))
      (scalar-distrib d (scalar g x) (scalar h y))
    ∙ cong₂ _∙_
      (cong₂ _∙_ (sym (scalar-mul c e x)) (sym (scalar-mul c f y)))
      (cong₂ _∙_ (sym (scalar-mul d g x)) (sym (scalar-mul d h y)))
    ∙ interchange (scalar (c Z.· e) x) (scalar (c Z.· f) y)
      (scalar (d Z.· g) x) (scalar (d Z.· h) y)
    ∙ cong₂ _∙_ (sym (scalar-add (c Z.· e) (d Z.· g) x))
      (sym (scalar-add (c Z.· f) (d Z.· h) y))
