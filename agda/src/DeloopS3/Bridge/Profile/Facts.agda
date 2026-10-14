{-# OPTIONS --safe --cubical --guardedness --no-import-sorts --lossy-unification #-}
module DeloopS3.Bridge.Profile.Facts where

-- Homology and cover-degree data for the actual outer span.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv; equivFun)
open import Cubical.Data.Sigma using (≡-×)
open import Cubical.Data.Nat using (ℕ; suc; _+_)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Int using (ℤ; pos)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group.Base using (Group; Group₀; GroupStr)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.Morphisms using
  (GroupHom; GroupEquiv; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.Group.DirProd using (DirProd)
open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup₀)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Algebra.Group.Subgroup using (kerGroup)
open import Cubical.Functions.Surjection using (isSurjection)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ-comm)
open import DeloopS3.Bridge.Recognition.Notation using
  (CW₀; H̃ᶜʷ; Hzero; finite≤→isCW)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map)
import DeloopS3.Bridge.OriginalSpan as OS
open OS public using (ShortCase; octa; icosa)

ACW CCW XCW : ShortCase → CW₀
ACW c = OS.A c , finite≤→isCW (OS.A-finite c)
CCW c = OS.C c , finite≤→isCW (OS.C-finite c)
XCW c = OS.X c , finite≤→isCW (OS.X-finite c)

RCW : CW₀
RCW = OS.R , finite≤→isCW OS.RP²-finite

XO XI : CW₀
XO = XCW octa
XI = XCW icosa

A₁ C₁ : ShortCase → Group₀
A₁ octa = DirProd (ℤGroup/ 2) (ℤGroup/ 2)
A₁ icosa = ℤGroup/ 4
C₁ octa = ℤGroup/ 2
C₁ icosa = UnitGroup₀

qH : (c : ShortCase) (k : ℕ)
  → GroupHom (H̃ᶜʷ (ACW c) k) (H̃ᶜʷ RCW k)
qH c k = cellular-map (ACW c) RCW k (OS.q c)

pH : (c : ShortCase) (k : ℕ)
  → GroupHom (H̃ᶜʷ (ACW c) k) (H̃ᶜʷ (CCW c) k)
pH c k = cellular-map (ACW c) (CCW c) k (OS.p c)

private
  abstract
    -- Seal the group calculation before instantiating cellular homology.
    signed-pair-isHom : {ℓ ℓ' ℓ'' : Level}
      (G : Group ℓ) (B : Group ℓ') (C : Group ℓ'')
      (q : GroupHom G B) (p : GroupHom G C)
      (comm : (x y : fst C)
        → GroupStr._·_ (snd C) x y ≡ GroupStr._·_ (snd C) y x)
      → IsGroupHom (snd G)
          (λ a → fst q a , GroupStr.inv (snd C) (fst p a))
          (snd (DirProd B C))
    signed-pair-isHom G B C q p comm = makeIsGroupHom λ x y →
      ≡-× (IsGroupHom.pres· (snd q) x y)
        (cong (GroupStr.inv (snd C)) (IsGroupHom.pres· (snd p) x y)
        ∙ GroupTheory.invDistr C (fst p x) (fst p y)
        ∙ comm (GroupStr.inv (snd C) (fst p y))
               (GroupStr.inv (snd C) (fst p x)))

  signed-pair : {ℓ ℓ' ℓ'' : Level}
    (G : Group ℓ) (B : Group ℓ') (C : Group ℓ'')
    (q : GroupHom G B) (p : GroupHom G C)
    (comm : (x y : fst C)
      → GroupStr._·_ (snd C) x y ≡ GroupStr._·_ (snd C) y x)
    → GroupHom G (DirProd B C)
  signed-pair G B C q p comm =
    (λ a → fst q a , GroupStr.inv (snd C) (fst p a)) ,
    signed-pair-isHom G B C q p comm


signedN : Bool → ℕ → ℤ
signedN false n = pos n
signedN true  n = Z.- (pos n)

-- Elaborate over an abstract homology functor.  The public specialization
-- below supplies the actual cellular groups, induced maps and commutativity.
private
  module Profiles
    (H : CW₀ → ℕ → Group₀)
    (cell : (A B : CW₀) (n : ℕ) (f : fst A → fst B)
      → GroupHom (H A n) (H B n))
    (comm : {n : ℕ} (X : CW₀) (x y : fst (H X (suc n)))
      → GroupStr._·_ (snd (H X (suc n))) x y
        ≡ GroupStr._·_ (snd (H X (suc n))) y x)
    where

    q : (c : ShortCase) (k : ℕ) → GroupHom (H (ACW c) k) (H RCW k)
    q c k = cell (ACW c) RCW k (OS.q c)

    p : (c : ShortCase) (k : ℕ) → GroupHom (H (ACW c) k) (H (CCW c) k)
    p c k = cell (ACW c) (CCW c) k (OS.p c)

    -- k indexes one below the positive homology degree.
    σ : (c : ShortCase) (k : ℕ)
      → GroupHom (H (ACW c) (suc k))
          (DirProd (H RCW (suc k)) (H (CCW c) (suc k)))
    σ c k = signed-pair
      (H (ACW c) (suc k)) (H RCW (suc k)) (H (CCW c) (suc k))
      (q c (suc k)) (p c (suc k)) (comm {n = k} (CCW c))

    σ-β : (c : ShortCase) (k : ℕ) (a : fst (H (ACW c) (suc k)))
      → fst (σ c k) a ≡ (fst (q c (suc k)) a ,
          GroupStr.inv (snd (H (CCW c) (suc k)))
            (fst (p c (suc k)) a))
    σ-β c k a = refl

open Profiles H̃ᶜʷ cellular-map (H̃ᶜʷ-comm {ℓ = ℓ-zero}) public
  using (σ; σ-β)

-- The record is elaborated over neutral groups, then specialized to the exact
-- groups and maps above; no additional hypotheses remain in the public type.
private
  module FactRecord
    (R : ℕ → Group₀)
    (A C : ShortCase → ℕ → Group₀)
    (p : (c : ShortCase) (k : ℕ) → GroupHom (A c k) (C c k))
    (s : (c : ShortCase) (k : ℕ)
      → GroupHom (A c (suc k)) (DirProd (R (suc k)) (C c (suc k))))
    where

    record ProfileFacts : Type₁ where
      field
        R-H₀ : isContr (fst (R 0))
        R-H₁ : GroupEquiv (R 1) (ℤGroup/ 2)
        R-H≥2 : (k : ℕ) → isContr (fst (R (2 + k)))

        A-H₀ : (c : ShortCase) → isContr (fst (A c 0))
        C-H₀ : (c : ShortCase) → isContr (fst (C c 0))
        A-H₁ : (c : ShortCase) → GroupEquiv (A c 1) (A₁ c)
        C-H₁ : (c : ShortCase) → GroupEquiv (C c 1) (C₁ c)
        A-H₂ : (c : ShortCase) → isContr (fst (A c 2))
        C-H₂ : (c : ShortCase) → isContr (fst (C c 2))
        A-H₃ : (c : ShortCase) → GroupEquiv (A c 3) ℤGroup
        C-H₃ : (c : ShortCase) → GroupEquiv (C c 3) ℤGroup

        O-H₁-equiv : isEquiv
          {A = fst (A octa 1)}
          {B = fst (DirProd (R 1) (C octa 1))}
          (fst (s octa 0))
        I-H₁-onto : isSurjection
          {A = fst (A icosa 1)}
          {B = fst (DirProd (R 1) (C icosa 1))}
          (fst (s icosa 0))
        I-H₁-kernel : GroupEquiv
          (kerGroup {G = A icosa 1}
            {H = DirProd (R 1) (C icosa 1)}
            (s icosa 0)) (ℤGroup/ 2)

        cover-sign : ShortCase → Bool
        cover-degree : (c : ShortCase) (z : fst (A c 3))
          → equivFun {A = fst (C c 3)} {B = ℤ} (fst (C-H₃ c)) (fst (p c 3) z)
            ≡ signedN (cover-sign c) (OS.N c)
                Z.· equivFun {A = fst (A c 3)} {B = ℤ} (fst (A-H₃ c)) z


open FactRecord (H̃ᶜʷ RCW)
  (λ c k → H̃ᶜʷ (ACW c) k) (λ c k → H̃ᶜʷ (CCW c) k)
  pH σ public using (ProfileFacts)
