{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TorusIntegerAlgebra where

-- Carrier-level algebra, elaborated before substituting cellular homology.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup ; ℤHom)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_ ; homPresℤ· ; ℤ·≡·)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.DMCExactness.Groups using (contr→zero)

open IsGroupHom

Scalar : (G : Group₀) → ℤ → GroupHom G G → Type
Scalar G ℓ h = (x : fst G) → fst h x ≡ (ℓ ℤ[ G ]· x)

abstract
  equiv-injective : {G H : Group₀} (e : GroupEquiv G H)
    (x y : fst G) → equivFun (fst e) x ≡ equivFun (fst e) y → x ≡ y
  equiv-injective e x y p = sym (retEq (fst e) x)
    ∙ cong (invEq (fst e)) p ∙ retEq (fst e) y

  integer-scalar : (ℓ : ℤ) → Scalar ℤGroup ℓ (ℤHom ℓ)
  integer-scalar ℓ n = ℤ·≡· ℓ n

  scalar-through-equiv : {G H : Group₀} (e : GroupEquiv G H)
    (g : GroupHom G G) (h : GroupHom H H) (ℓ : ℤ)
    → ((x : fst G) → equivFun (fst e) (fst g x) ≡ fst h (equivFun (fst e) x))
    → Scalar H ℓ h → Scalar G ℓ g
  scalar-through-equiv e g h ℓ square scalar x = equiv-injective e _ _
    (square x ∙ scalar (equivFun (fst e) x)
      ∙ sym (homPresℤ· (GroupEquiv→GroupHom e) x ℓ))

  exact-mono : {V P A : Group₀} (u : GroupHom V P) (δ : GroupHom P A)
    → Exact₃ u δ → isContr (fst V) → isMono δ
  exact-mono {V} {P} u δ ex vz = isInjective→isMono δ λ x p →
    PT.rec (GroupStr.is-set (snd P) _ _)
      (λ { (v , q) → sym q ∙ cong (fst u) (contr→zero V vz v) ∙ pres1 (snd u) })
      (equivFun (ex x) p)

  scalar-from-boundary : {V P A : Group₀}
    (u : GroupHom V P) (δ : GroupHom P A)
    (p : GroupHom P P) (a : GroupHom A A) (ℓ : ℤ)
    → Exact₃ u δ → isContr (fst V)
    → compGroupHom p δ ≡ compGroupHom δ a
    → Scalar A ℓ a → Scalar P ℓ p
  scalar-from-boundary u δ p a ℓ ex vz natural scalar x = exact-mono u δ ex vz
    (cong (λ h → fst h x) natural ∙ scalar (fst δ x)
      ∙ sym (homPresℤ· δ x ℓ))

  scalar-coordinate : {G : Group₀} (h : GroupHom G G) (e : GroupHom G ℤGroup)
    (ℓ : ℤ) → Scalar G ℓ h
    → (x : fst G) → fst e (fst h x) ≡ ℓ Z.· fst e x
  scalar-coordinate h e ℓ scalar x = cong (fst e) (scalar x)
    ∙ homPresℤ· e x ℓ ∙ sym (ℤ·≡· ℓ (fst e x))

  product-action : (G H : Group₀) (ℓ : ℤ) (x : fst G) (y : fst H)
    → (ℓ ℤ[ DirProd G H ]· (x , y)) ≡ ((ℓ ℤ[ G ]· x) , (ℓ ℤ[ H ]· y))
  product-action G H (pos zero) x y = refl
  product-action G H (pos (suc n)) x y =
    cong (GroupStr._·_ (snd (DirProd G H)) (x , y)) (product-action G H (pos n) x y)
  product-action G H (negsuc zero) x y = refl
  product-action G H (negsuc (suc n)) x y =
    cong (GroupStr._·_ (snd (DirProd G H))
      (GroupStr.inv (snd G) x , GroupStr.inv (snd H) y))
      (product-action G H (negsuc n) x y)

-- A canonical coproduct equivalence; its beta must be the actual inclusions.
module CoproductScalar (G A : Group₀)
  (left right : GroupHom G A) (e : GroupEquiv (DirProd G G) A)
  (beta : (x y : fst G) → equivFun (fst e) (x , y)
    ≡ GroupStr._·_ (snd A) (fst left x) (fst right y)) where

  abstract
    scalar-on-sum : (g : GroupHom G G) (a : GroupHom A A) (ℓ : ℤ)
      → ((x : fst G) → fst a (fst left x) ≡ fst left (fst g x))
      → ((y : fst G) → fst a (fst right y) ≡ fst right (fst g y))
      → Scalar G ℓ g → Scalar A ℓ a
    scalar-on-sum g a ℓ sqL sqR scalar z =
      cong (fst a) (sym (secEq (fst e) z))
      ∙ cong (fst a) (beta x y)
      ∙ pres· (snd a) (fst left x) (fst right y)
      ∙ cong₂ (GroupStr._·_ (snd A)) (sqL x) (sqR y)
      ∙ sym (beta (fst g x) (fst g y))
      ∙ cong (equivFun (fst e)) (ΣPathP (scalar x , scalar y))
      ∙ cong (equivFun (fst e)) (sym (product-action G G ℓ x y))
      ∙ homPresℤ· (GroupEquiv→GroupHom e) (x , y) ℓ
      ∙ cong (ℓ ℤ[ A ]·_) (secEq (fst e) z)
      where
      x y : fst G
      x = fst (invEq (fst e) z)
      y = snd (invEq (fst e) z)
