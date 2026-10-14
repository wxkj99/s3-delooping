{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.Outer where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
open import Cubical.Algebra.Group.Base using (Group₀)
open import Cubical.Algebra.Group.Morphisms using
  (GroupHom ; GroupEquiv ; isInjective)
open import Cubical.Algebra.Group.DirProd using (DirProd)
open import Cubical.Algebra.Group.Subgroup using (kerGroup)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Homotopy.Connected using (isConnectedSubtr)
import Cubical.HITs.PropositionalTruncation as PT

open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; Hzero)
open import DeloopS3.Bridge.Recognition.HomologyDimension using
  (finite≤-homology-above)
open import DeloopS3.Bridge.DMCExactness.Geometric using
  (GeometricPushoutLES ; SpanSequenceData)
open import DeloopS3.Bridge.DMCExactness.Groups using (equiv-kernel-zero)
open import DeloopS3.Bridge.Profile.Facts
open import DeloopS3.Bridge.Profile.Types using (OProfile ; IProfile ; connected-H₀)
open import DeloopS3.Bridge.Profile.OuterAdapters using
  (positive-source-coordinate ; positive-cover-degree ; spanLES-merely ; span-source-agrees)
import DeloopS3.Bridge.Profile.OuterMV as MV
import DeloopS3.Bridge.Profile.H1Data.Actual as H1
import DeloopS3.Bridge.OriginalSpan as OS
import DeloopS3.Bridge.SpanPi1.Target as Target

private
  -- Homomorphism transports are elaborated over neutral groups, not over
  -- expanded cellular-homology presentations.
  abstract
    source-injective : (G H : Group₀) (u v : GroupHom G H)
      → u ≡ v → isEquiv (fst v) → isInjective u
    source-injective G H u v p e =
      subst {A = GroupHom G H} {x = v} {y = u}
        (λ w → isInjective {G = G} {H = H} w) (sym p)
        (equiv-kernel-zero {G = G} {H = H} v e)

    source-kernel : (G H K : Group₀) (u v : GroupHom G H)
      → u ≡ v → GroupEquiv (kerGroup v) K → GroupEquiv (kerGroup u) K
    source-kernel G H K u v p e =
      subst {A = GroupHom G H} {x = v} {y = u}
        (λ w → GroupEquiv (kerGroup {G = G} {H = H} w) K)
        (sym p) e

  LES : ShortCase → Type₁
  LES c = GeometricPushoutLES (ACW c) RCW (CCW c) (OS.q c) (OS.p c) (XCW c)

  Top : ShortCase → Type
  Top c = Hzero (XCW c) 4 × GroupEquiv (H̃ᶜʷ (XCW c) 3) (ℤGroup/ OS.N c)

  Second : Type
  Second = Hzero XO 2 × GroupEquiv (H̃ᶜʷ XI 2) (ℤGroup/ 2)

  N-positive : (c : ShortCase) → 0 < OS.N c
  N-positive octa = 2 , refl
  N-positive icosa = 9 , refl

  abstract
    top-from-LES : (facts : ProfileFacts) (c : ShortCase) → LES c → Top c
    top-from-LES facts c les =
      MV.H₄-zero-from-MV (ACW c) RCW (CCW c) (XCW c) (OS.q c) (OS.p c) les
        (OS.N c) (N-positive c)
        (positive-source-coordinate facts c) (ProfileFacts.C-H₃ facts c)
        (positive-cover-degree facts c)
        (ProfileFacts.R-H≥2 facts 2)
        (finite≤-homology-above (CCW c) 3 4 (OS.C-finite c) (0 , refl)) ,
      MV.H₃-iso-ℤ/N-from-MV (ACW c) RCW (CCW c) (XCW c) (OS.q c) (OS.p c) les
        (OS.N c)
        (positive-source-coordinate facts c) (ProfileFacts.C-H₃ facts c)
        (positive-cover-degree facts c)
        (ProfileFacts.R-H≥2 facts 1) (ProfileFacts.A-H₂ facts c)

    second-from-LES : (facts : ProfileFacts) → LES octa → LES icosa → Second
    second-from-LES facts lesO lesI =
      MV.H₂-zero-from-MV (ACW octa) RCW (CCW octa) XO (OS.q octa) (OS.p octa) lesO
        (ProfileFacts.R-H≥2 facts 0) (ProfileFacts.C-H₂ facts octa)
        (source-injective (H̃ᶜʷ (ACW octa) 1)
          (DirProd (H̃ᶜʷ RCW 1) (H̃ᶜʷ (CCW octa) 1))
          (SpanSequenceData.source-map (snd lesO) 1) (σ octa 0)
          (span-source-agrees octa lesO 0) (ProfileFacts.O-H₁-equiv facts)) ,
      MV.H₂-iso-ℤ/2-from-MV (ACW icosa) RCW (CCW icosa) XI (OS.q icosa) (OS.p icosa) lesI
        (ProfileFacts.R-H≥2 facts 0) (ProfileFacts.C-H₂ facts icosa)
        (source-kernel (H̃ᶜʷ (ACW icosa) 1)
          (DirProd (H̃ᶜʷ RCW 1) (H̃ᶜʷ (CCW icosa) 1)) (ℤGroup/ 2)
          (SpanSequenceData.source-map (snd lesI) 1) (σ icosa 0)
          (span-source-agrees icosa lesI 0) (ProfileFacts.I-H₁-kernel facts))

abstract
  outer-top : (facts : ProfileFacts) (c : ShortCase)
    → PT.∥ Hzero (XCW c) 4
        × GroupEquiv (H̃ᶜʷ (XCW c) 3) (ℤGroup/ OS.N c) ∥₁
  outer-top facts c = PT.map {A = LES c} {B = Top c}
    (top-from-LES facts c) (spanLES-merely c)

  outer-H₂ : ProfileFacts
    → PT.∥ Hzero XO 2 × GroupEquiv (H̃ᶜʷ XI 2) (ℤGroup/ 2) ∥₁
  outer-H₂ facts = PT.rec {A = LES octa} {P = PT.∥ Second ∥₁}
    PT.squash₁
    (λ lesO → PT.map {A = LES icosa} {B = Second}
      (second-from-LES facts lesO) (spanLES-merely icosa))
    (spanLES-merely octa)

  -- H1Data uses the same literal type with a different CW witness.
  -- Only the propositional CW witness is changed here.
  outer-H₁-zero : ProfileFacts → (c : ShortCase) → Hzero (XCW c) 1
  outer-H₁-zero facts c = subst {A = CW₀} {x = H1.XCW c} {y = XCW c}
    (λ Y → Hzero Y 1)
    (ΣPathP (refl , PT.squash₁ (snd (H1.XCW c)) (snd (XCW c))))
    (H1.X-H₁-zero c)

  outer-H₀-zero : (c : ShortCase) → Hzero (XCW c) 0
  outer-H₀-zero c = connected-H₀ (XCW c)
    (isConnectedSubtr {A = OS.X c} 2 1 (Target.X-simple c))

  outer-H-above : (c : ShortCase) (k : ℕ) → 4 < k → Hzero (XCW c) k
  outer-H-above c k = finite≤-homology-above (XCW c) 4 k (OS.X-finite c)

private
  abstract
    octa-profile : Top octa → Hzero XO 2 → OProfile XO
    OProfile.finite (octa-profile top h2) = OS.X-finite octa
    OProfile.simple (octa-profile top h2) = Target.X-simple octa
    OProfile.H₂-zero (octa-profile top h2) = h2
    OProfile.H₃ (octa-profile top h2) = snd top
    OProfile.H₄-zero (octa-profile top h2) = fst top

    icosa-profile : Top icosa → GroupEquiv (H̃ᶜʷ XI 2) (ℤGroup/ 2) → IProfile XI
    IProfile.finite (icosa-profile top h2) = OS.X-finite icosa
    IProfile.simple (icosa-profile top h2) = Target.X-simple icosa
    IProfile.H₂ (icosa-profile top h2) = h2
    IProfile.H₃ (icosa-profile top h2) = snd top
    IProfile.H₄-zero (icosa-profile top h2) = fst top

abstract
  outer-profiles : ProfileFacts → PT.∥ OProfile XO × IProfile XI ∥₁
  outer-profiles facts =
    PT.rec {A = Top octa} {P = PT.∥ OProfile XO × IProfile XI ∥₁} PT.squash₁
      (λ topO →
        PT.rec {A = Top icosa} {P = PT.∥ OProfile XO × IProfile XI ∥₁} PT.squash₁
          (λ topI →
            PT.map {A = Second} {B = OProfile XO × IProfile XI}
              (λ h2 → octa-profile topO (fst h2) , icosa-profile topI (snd h2))
              (outer-H₂ facts))
          (outer-top facts icosa))
      (outer-top facts octa)
