{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.MooreMarked.Representatives where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat using (ℕ ; suc ; _+_)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties using (GroupEquiv→GroupHom)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Homotopy.Connected using (isConnected)
open import Cubical.HITs.Sn using (S₊∙)
open import Cubical.HITs.Susp using (north)
open import Cubical.HITs.Pushout using (inr)
open import Cubical.CW.Instances.Sn using (Sᶜʷ)
open import Cubical.CW.Homology.Groups.Sn using (genHₙSⁿ)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→comp)
open import Cubical.CW.HurewiczTheorem using (HurewiczMapUntrunc)
open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Bridge.Recognition.Models using (moore3CW ; bottomCW)
open import DeloopS3.Bridge.Recognition.Extension using (Moore ; BottomMoore)
open import DeloopS3.Bridge.Recognition.Hurewicz using (hurewicz-representative)
open import DeloopS3.Bridge.Recognition.Torsion using (multiple ; reflect-multiple-zero)
open import DeloopS3.Bridge.Recognition.RepresentativeFinish using (extend-moore3-from-homology-torsion)
open import DeloopS3.Bridge.MooreMarked.BottomExtension using (extend-bottom-from-homology-torsion)
open import DeloopS3.Bridge.MooreMarked.Cyclic
open import DeloopS3.Bridge.MooreMarked.Marked
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as TR

abstract
  -- Naturality is used with the retained *unpointed restriction path*.
  -- HurewiczMapUntrunc depends only on the underlying sphere map.
  hurewicz-restriction : (k : ℕ) (A X : CW₀) (a : fst A) (x : fst X)
    (ι : S₊∙ (2 + k) →∙ (fst A , a))
    (s : S₊∙ (2 + k) →∙ (fst X , x))
    (f : fst A → fst X) → f ∘ fst ι ≡ fst s
    → fst (H̃ᶜʷ→ {C = A} {D = X} (2 + k) f)
        (HurewiczMapUntrunc {n = suc k} A a ι)
      ≡ HurewiczMapUntrunc {n = suc k} X x s
  hurewicz-restriction k A X a x ι s f restriction =
    funExt⁻ (cong fst (sym (H̃ᶜʷ→comp
      {C = Sᶜʷ (2 + k)} {D = A} {E = X} (2 + k) f (fst ι))))
      (genHₙSⁿ (suc k))
    ∙ cong (λ g → fst (H̃ᶜʷ→ {C = Sᶜʷ (2 + k)} {D = X} (2 + k) g)
        (genHₙSⁿ (suc k))) restriction

  representative-from-marking : (k m : ℕ) (positive : 0 < m)
    (A : CW₀) (a : fst A) (ι : S₊∙ (2 + k) →∙ (fst A , a))
    (marked : GroupEquiv (H̃ᶜʷ A (2 + k)) (ℤGroup/ m))
    → equivFun (fst marked) (HurewiczMapUntrunc {n = suc k} A a ι) ≡ oneMod m positive
    → (X : CW₀) (conn : isConnected (3 + k) (fst X))
    → ((x : fst X) (s : S₊∙ (2 + k) →∙ (fst X , x))
        → multiple (H̃ᶜʷ X (2 + k)) m (HurewiczMapUntrunc {n = suc k} X x s)
          ≡ GroupStr.1g (snd (H̃ᶜʷ X (2 + k)))
        → PT.∥ Σ[ f ∈ (fst A → fst X) ] (f ∘ fst ι ≡ fst s) ∥₁)
    → GroupEquiv (H̃ᶜʷ X (2 + k)) (ℤGroup/ m)
    → PT.∥ Σ[ f ∈ (fst A → fst X) ] Hiso A X (2 + k) f ∥₁
  representative-from-marking k m positive A a ι marked mark X conn extend coordinates =
    TR.rec {A = fst X} {n = 3 + k}
      (isProp→isOfHLevelSuc (2 + k) PT.squash₁) at-point (fst conn)
    where
    h : fst (H̃ᶜʷ X (2 + k))
    h = invEq (fst coordinates) (oneMod m positive)

    h-torsion : multiple (H̃ᶜʷ X (2 + k)) m h
      ≡ GroupStr.1g (snd (H̃ᶜʷ X (2 + k)))
    h-torsion = reflect-multiple-zero (GroupEquiv→GroupHom coordinates)
      (snd (fst coordinates)) m h
      (cong (multiple (ℤGroup/ m) m) (secEq (fst coordinates) (oneMod m positive))
       ∙ multiple-oneMod m positive)

    at-point : (x : fst X)
      → PT.∥ Σ[ f ∈ (fst A → fst X) ] Hiso A X (2 + k) f ∥₁
    at-point x = PT.rec PT.squash₁
      (λ { (s , value) → PT.rec PT.squash₁
        (λ { (f , restriction) → PT.∣ f ,
          marked-map-isEquiv m positive (H̃ᶜʷ A (2 + k)) (H̃ᶜʷ X (2 + k))
            marked coordinates (HurewiczMapUntrunc {n = suc k} A a ι) h
            mark (secEq (fst coordinates) (oneMod m positive))
            (H̃ᶜʷ→ {C = A} {D = X} (2 + k) f)
            (hurewicz-restriction k A X a x ι s f restriction ∙ value) ∣₁ })
        (extend x s (cong (multiple (H̃ᶜʷ X (2 + k)) m) value ∙ h-torsion)) })
      (hurewicz-representative X k conn x h)

  moore3-representative : (m : ℕ) → 0 < m → (X : CW₀)
    → isConnected 4 (fst X)
    → GroupEquiv (H̃ᶜʷ X 3) (ℤGroup/ m)
    → PT.∥ Σ[ f ∈ (Moore m 2 → fst X) ] Hiso (moore3CW m) X 3 f ∥₁
  moore3-representative m positive X conn =
    representative-from-marking 1 m positive (moore3CW m) (inr north) (inr , refl)
      (moore3-H₃-marked m positive) (moore3-bottom-generator m positive) X conn
      (extend-moore3-from-homology-torsion m X conn)

  bottom-representative : (X : CW₀) → isConnected 3 (fst X)
    → GroupEquiv (H̃ᶜʷ X 2) (ℤGroup/ 2)
    → PT.∥ Σ[ a ∈ (BottomMoore → fst X) ] Hiso bottomCW X 2 a ∥₁
  bottom-representative X conn =
    representative-from-marking 0 2 positive₂ bottomCW (inr north) (inr , refl)
      bottom-H₂-marked bottom-bottom-generator X conn
      (extend-bottom-from-homology-torsion X conn)
