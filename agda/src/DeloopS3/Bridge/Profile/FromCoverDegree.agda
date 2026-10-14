{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.Profile.FromCoverDegree where

-- Construct the homology profile from a joint choice of H₃ coordinates
-- and their actual cover-degree law, using the lower-degree component facts.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv; equivFun)
open import Cubical.Foundations.Pointed using (Pointed; typ; _≃∙_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _+_)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Int using (ℤ)
import Cubical.Data.Int as Z
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Algebra.Group.Base using (Group₀; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom; GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties using
  (GroupHom≡; compGroupEquiv; GroupIso→GroupEquiv)
open import Cubical.Algebra.Group.DirProd using (DirProd)
open import Cubical.Algebra.Group.Subgroup using (kerGroup)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_; ℤGroup/1≅Unit)
open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup₀)
open import Cubical.Functions.Surjection using (isSurjection)
open import Cubical.CW.Homology.Base using (H̃ᶜʷAb)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.Homotopy.Connected using (isConnected)
open import Cubical.Homotopy.Loopspace using (Ω)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using (CW₀; isCW; H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map)
import DeloopS3.Bridge.OriginalSpan as OS
import DeloopS3.Bridge.Profile.Facts as Facts
open Facts using (ShortCase; octa; icosa; ProfileFacts)
import DeloopS3.Bridge.Profile.H1Data.Actual as Actual
open import DeloopS3.Bridge.Profile.H1Data.Components using
  (FourGroups; ComponentH1Groups)
import DeloopS3.Bridge.Profile.H1Complete as H1
import DeloopS3.Bridge.Profile.ComponentHomologyComplete as Components
import DeloopS3.Bridge.ComponentHomology.RP2 as RP2
open import DeloopS3.Bridge.Profile.Types using (connected-H₀)
import DeloopS3.Bridge.SpanPi1.Connected as Connected
open import DeloopS3.Bridge.Profile.Assembly using (Deloop-final-from-facts)

-- Elaborate the dependent coordinate/degree record on neutral groups.
private
  module DegreeRecord
    (A C : ShortCase → Group₀)
    (p : (c : ShortCase) → GroupHom (A c) (C c)) where

    record CoverDegreeInput : Type₀ where
      field
        eA : (c : ShortCase) → GroupEquiv (A c) ℤGroup
        eC : (c : ShortCase) → GroupEquiv (C c) ℤGroup
        sign : ShortCase → Bool
        degree : (c : ShortCase) (z : fst (A c))
          → equivFun (fst (eC c)) (fst (p c) z)
            ≡ Facts.signedN (sign c) (OS.N c)
                Z.· equivFun (fst (eA c)) z

open DegreeRecord (λ c → H̃ᶜʷ (Facts.ACW c) 3)
  (λ c → H̃ᶜʷ (Facts.CCW c) 3) (λ c → Facts.pH c 3)
  public using (CoverDegreeInput)

private
  abstract
    -- The target-I computation ends at Z/1, not at Facts.C₁ icosa.
    trivial-target : GroupEquiv (ℤGroup/ 1) UnitGroup₀
    trivial-target = GroupIso→GroupEquiv ℤGroup/1≅Unit

  -- All the remaining fields, elaborated before specializing homology.
  module LowerRecord
    (R : ℕ → Group₀) (A C : ShortCase → ℕ → Group₀)
    (s : (c : ShortCase) → GroupHom (A c 1) (DirProd (R 1) (C c 1)))
    where

    record LowerFacts : Type₀ where
      field
        R-H₀ : isContr (fst (R 0))
        R-H₁ : GroupEquiv (R 1) (ℤGroup/ 2)
        R-H≥2 : (k : ℕ) → isContr (fst (R (2 + k)))
        A-H₀ : (c : ShortCase) → isContr (fst (A c 0))
        C-H₀ : (c : ShortCase) → isContr (fst (C c 0))
        A-H₁ : (c : ShortCase) → GroupEquiv (A c 1) (Facts.A₁ c)
        C-H₁ : (c : ShortCase) → GroupEquiv (C c 1) (Facts.C₁ c)
        A-H₂ : (c : ShortCase) → isContr (fst (A c 2))
        C-H₂ : (c : ShortCase) → isContr (fst (C c 2))
        O-H₁-equiv : isEquiv (fst (s octa))
        I-H₁-onto : isSurjection (fst (s icosa))
        I-H₁-kernel : GroupEquiv (kerGroup (s icosa)) (ℤGroup/ 2)

    abstract
      assemble-lower
        : isContr (fst (R 0))
        → GroupEquiv (R 1) (ℤGroup/ 2)
        → ((k : ℕ) → isContr (fst (R (2 + k))))
        → ((c : ShortCase) → isContr (fst (A c 0)))
        → ((c : ShortCase) → isContr (fst (C c 0)))
        → ((c : ShortCase) → isContr (fst (A c 2)))
        → ((c : ShortCase) → isContr (fst (C c 2)))
        → isEquiv (fst (s octa))
        → isSurjection (fst (s icosa))
        → PT.∥ FourGroups (A octa 1) (A icosa 1) (C octa 1) (C icosa 1) ∥₁
        → PT.∥ GroupEquiv (kerGroup (s icosa)) (ℤGroup/ 2) ∥₁
        → PT.∥ LowerFacts ∥₁
      assemble-lower r0 r1 r2 a0 c0 a2 c2 oe io = PT.map2 build
        where
        build : FourGroups (A octa 1) (A icosa 1) (C octa 1) (C icosa 1)
          → GroupEquiv (kerGroup (s icosa)) (ℤGroup/ 2) → LowerFacts
        LowerFacts.R-H₀ (build g k) = r0
        LowerFacts.R-H₁ (build g k) = r1
        LowerFacts.R-H≥2 (build g k) = r2
        LowerFacts.A-H₀ (build g k) = a0
        LowerFacts.C-H₀ (build g k) = c0
        LowerFacts.A-H₁ (build g k) octa = FourGroups.source-O g
        LowerFacts.A-H₁ (build g k) icosa = FourGroups.source-I g
        LowerFacts.C-H₁ (build g k) octa = FourGroups.target-O g
        LowerFacts.C-H₁ (build g k) icosa =
          compGroupEquiv (FourGroups.target-I g) trivial-target
        LowerFacts.A-H₂ (build g k) = a2
        LowerFacts.C-H₂ (build g k) = c2
        LowerFacts.O-H₁-equiv (build g k) = oe
        LowerFacts.I-H₁-onto (build g k) = io
        LowerFacts.I-H₁-kernel (build g k) = k

  -- Only the CW proof changes here, never the underlying space or q/p.
  -- Seal the dependent transports before inserting the literal spaces.
  module ChangeR (A C : CW₀) (R : Type₀)
    (q : fst A → R) (p : fst A → fst C) where

    signed : (w : isCW R)
      → GroupHom (H̃ᶜʷ A 1) (DirProd (H̃ᶜʷ (R , w) 1) (H̃ᶜʷ C 1))
    signed w = Actual.signed-hom
      (H̃ᶜʷAb A 0) (H̃ᶜʷAb (R , w) 0) (H̃ᶜʷAb C 0)
      (cellular-map A (R , w) 1 q) (cellular-map A C 1 p)

    abstract
      change-equiv : (u v : isCW R)
        → isEquiv (fst (signed u)) → isEquiv (fst (signed v))
      change-equiv u v = subst (λ w → isEquiv (fst (signed w))) (PT.squash₁ u v)

      change-onto : (u v : isCW R)
        → isSurjection (fst (signed u)) → isSurjection (fst (signed v))
      change-onto u v = subst (λ w → isSurjection (fst (signed w))) (PT.squash₁ u v)

      change-kernel : (u v : isCW R)
        → PT.∥ GroupEquiv (kerGroup (signed u)) (ℤGroup/ 2) ∥₁
        → PT.∥ GroupEquiv (kerGroup (signed v)) (ℤGroup/ 2) ∥₁
      change-kernel u v = subst
        (λ w → PT.∥ GroupEquiv (kerGroup (signed w)) (ℤGroup/ 2) ∥₁)
        (PT.squash₁ u v)

  abstract
    change-R-H₁ : (R : Type₀) (u v : isCW R)
      → GroupEquiv (H̃ᶜʷ (R , u) 1) (ℤGroup/ 2)
      → GroupEquiv (H̃ᶜʷ (R , v) 1) (ℤGroup/ 2)
    change-R-H₁ R u v = subst
      (λ w → GroupEquiv (H̃ᶜʷ (R , w) 1) (ℤGroup/ 2)) (PT.squash₁ u v)

    change-R-zero : (R : Type₀) (u v : isCW R) (n : ℕ)
      → isContr (fst (H̃ᶜʷ (R , u) n)) → isContr (fst (H̃ᶜʷ (R , v) n))
    change-R-zero R u v n = subst
      (λ w → isContr (fst (H̃ᶜʷ (R , w) n))) (PT.squash₁ u v)

    -- Equality transport for the actual homomorphisms, not coordinates.
    along-equiv : (G H : Group₀) (f g : GroupHom G H)
      → f ≡ g → isEquiv (fst f) → isEquiv (fst g)
    along-equiv G H f g e = subst (λ h → isEquiv (fst h)) e

    along-onto : (G H : Group₀) (f g : GroupHom G H)
      → f ≡ g → isSurjection (fst f) → isSurjection (fst g)
    along-onto G H f g e = subst (λ h → isSurjection (fst h)) e

    along-kernel : (G H : Group₀) (f g : GroupHom G H)
      → f ≡ g → PT.∥ GroupEquiv (kerGroup f) (ℤGroup/ 2) ∥₁
      → PT.∥ GroupEquiv (kerGroup g) (ℤGroup/ 2) ∥₁
    along-kernel G H f g e = subst
      (λ h → PT.∥ GroupEquiv (kerGroup h) (ℤGroup/ 2) ∥₁) e

  module ActualR (c : ShortCase) = ChangeR
    (Facts.ACW c) (Facts.CCW c) OS.R (OS.q c) (OS.p c)

  abstract
    σ-agrees : (c : ShortCase)
      → Facts.σ c 0 ≡ ActualR.signed c (snd Facts.RCW)
    σ-agrees c = GroupHom≡ (funExt (Facts.σ-β c 0))

    actual-O-equiv : isEquiv (fst (Facts.σ octa 0))
    actual-O-equiv = along-equiv
      (H̃ᶜʷ (Facts.ACW octa) 1)
      (DirProd (H̃ᶜʷ Facts.RCW 1) (H̃ᶜʷ (Facts.CCW octa) 1))
      (ActualR.signed octa (snd Facts.RCW)) (Facts.σ octa 0)
      (sym (σ-agrees octa))
      (ActualR.change-equiv octa (snd Actual.RCW) (snd Facts.RCW) H1.outer-O-isEquiv)

    actual-I-onto : isSurjection (fst (Facts.σ icosa 0))
    actual-I-onto = along-onto
      (H̃ᶜʷ (Facts.ACW icosa) 1)
      (DirProd (H̃ᶜʷ Facts.RCW 1) (H̃ᶜʷ (Facts.CCW icosa) 1))
      (ActualR.signed icosa (snd Facts.RCW)) (Facts.σ icosa 0)
      (sym (σ-agrees icosa))
      (ActualR.change-onto icosa (snd Actual.RCW) (snd Facts.RCW) H1.outer-I-onto)

    actual-I-kernel : PT.∥ GroupEquiv (kerGroup (Facts.σ icosa 0)) (ℤGroup/ 2) ∥₁
    actual-I-kernel = along-kernel
      (H̃ᶜʷ (Facts.ACW icosa) 1)
      (DirProd (H̃ᶜʷ Facts.RCW 1) (H̃ᶜʷ (Facts.CCW icosa) 1))
      (ActualR.signed icosa (snd Facts.RCW)) (Facts.σ icosa 0)
      (sym (σ-agrees icosa))
      (ActualR.change-kernel icosa (snd Actual.RCW) (snd Facts.RCW) H1.outer-I-kernel)

    R-H₁ : GroupEquiv (H̃ᶜʷ Facts.RCW 1) (ℤGroup/ 2)
    R-H₁ = change-R-H₁ OS.R (snd Actual.RCW) (snd Facts.RCW) RP2.RP²-H₁

    R-H≥2 : (k : ℕ) → isContr (fst (H̃ᶜʷ Facts.RCW (2 + k)))
    R-H≥2 zero = change-R-zero OS.R (snd Actual.RCW) (snd Facts.RCW) 2 RP2.RP²-H₂
    R-H≥2 (suc k) = change-R-zero OS.R (snd Actual.RCW) (snd Facts.RCW)
      (3 + k) (RP2.RP²-H≥3 k)

  module Lower = LowerRecord (H̃ᶜʷ Facts.RCW)
    (λ c k → H̃ᶜʷ (Facts.ACW c) k) (λ c k → H̃ᶜʷ (Facts.CCW c) k)
    (λ c → Facts.σ c 0)

  abstract
    lower-facts : PT.∥ Lower.LowerFacts ∥₁
    lower-facts = Lower.assemble-lower
      (connected-H₀ Facts.RCW Connected.R-connected) R-H₁ R-H≥2
      (λ c → connected-H₀ (Facts.ACW c) (Connected.A-connected c))
      (λ c → connected-H₀ (Facts.CCW c) (Connected.C-connected c))
      Components.source-H₂-zero Components.target-H₂-zero
      actual-O-equiv actual-I-onto H1.component-groups actual-I-kernel

  -- These projections reuse the input's exact H3 choices; no independent
  -- component-H3 equivalence is selected or identified with them.
  assemble-profile : Lower.LowerFacts → CoverDegreeInput → ProfileFacts
  ProfileFacts.R-H₀ (assemble-profile l d) = Lower.LowerFacts.R-H₀ l
  ProfileFacts.R-H₁ (assemble-profile l d) = Lower.LowerFacts.R-H₁ l
  ProfileFacts.R-H≥2 (assemble-profile l d) = Lower.LowerFacts.R-H≥2 l
  ProfileFacts.A-H₀ (assemble-profile l d) = Lower.LowerFacts.A-H₀ l
  ProfileFacts.C-H₀ (assemble-profile l d) = Lower.LowerFacts.C-H₀ l
  ProfileFacts.A-H₁ (assemble-profile l d) = Lower.LowerFacts.A-H₁ l
  ProfileFacts.C-H₁ (assemble-profile l d) = Lower.LowerFacts.C-H₁ l
  ProfileFacts.A-H₂ (assemble-profile l d) = Lower.LowerFacts.A-H₂ l
  ProfileFacts.C-H₂ (assemble-profile l d) = Lower.LowerFacts.C-H₂ l
  ProfileFacts.A-H₃ (assemble-profile l d) = CoverDegreeInput.eA d
  ProfileFacts.C-H₃ (assemble-profile l d) = CoverDegreeInput.eC d
  ProfileFacts.O-H₁-equiv (assemble-profile l d) = Lower.LowerFacts.O-H₁-equiv l
  ProfileFacts.I-H₁-onto (assemble-profile l d) = Lower.LowerFacts.I-H₁-onto l
  ProfileFacts.I-H₁-kernel (assemble-profile l d) = Lower.LowerFacts.I-H₁-kernel l
  ProfileFacts.cover-sign (assemble-profile l d) = CoverDegreeInput.sign d
  ProfileFacts.cover-degree (assemble-profile l d) = CoverDegreeInput.degree d

abstract
  -- All finite choices, including the kernel equivalence, stay under PT.
  coverDegree→profileFacts : PT.∥ CoverDegreeInput ∥₁ → PT.∥ ProfileFacts ∥₁
  coverDegree→profileFacts = PT.map2 assemble-profile lower-facts

  Deloop-from-cover-degree : PT.∥ CoverDegreeInput ∥₁
    → Σ[ B ∈ Pointed ℓ-zero ]
        (isConnected 2 (typ B) × (Ω B ≃∙ (S₊ 3 , north)))
  Deloop-from-cover-degree d = Deloop-final-from-facts (coverDegree→profileFacts d)
