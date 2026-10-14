{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.MooreRecognition where

-- Moore-space recognition from a finite homology profile.
-- The LES is eliminated into isEquiv f; the representative and space equivalence remain mere.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Homotopy.Connected using (isConnected)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using
  (CW₀ ; Finite≤ ; Hzero ; Hiso ; H̃ᶜʷ ; cofibCW ; finite≤→isFinCW)
open import DeloopS3.Bridge.Recognition.Extension using (Moore)
open import DeloopS3.Bridge.Recognition.Models using (moore3CW ; moore3-finite≤)
open import DeloopS3.Bridge.Recognition.HomologyDimension using
  (finite≤-homology-above)
open import DeloopS3.Bridge.Recognition using (moore3-map-isEquiv-from-cofib)
open import DeloopS3.Bridge.MooreMarked using (moore3-representative)
open import DeloopS3.Bridge.CofibreHomology using (CofibreLES ; moore3-H₄)
open import DeloopS3.Bridge.DMCExactness.Consequences using (cofib-H₄-H₅)
open import DeloopS3.Bridge.Profile.CofibreLES using
  (recognition-cofibreLES-merely)

abstract
  moore3-map-isEquiv : (m : ℕ) → 0 < m → (X : CW₀)
    → Finite≤ 4 (fst X) → isConnected 4 (fst X)
    → Hzero X 4 → Hzero X 5
    → (f : Moore m 2 → fst X) → Hiso (moore3CW m) X 3 f → isEquiv f
  moore3-map-isEquiv m positive X finX connX x4 x5 f isoH =
    PT.rec (isPropIsEquiv f) from-LES
      (recognition-cofibreLES-merely (moore3CW m) X f
        (moore3-finite≤ m) finX)
    where
    -- This is the recognizer's actual cofibre CW witness.  We do not
    -- claim that the cofibre itself has dimension at most four.
    Cf : CW₀
    Cf = cofibCW (moore3CW m) X
      (finite≤→isFinCW {d = 4} (moore3-finite≤ m)) f

    from-LES : CofibreLES (moore3CW m) X f Cf → isEquiv f
    from-LES les = moore3-map-isEquiv-from-cofib m X finX connX f isoH
      (fst vanishings) (snd vanishings)
      where
      vanishings : Hzero Cf 4 × Hzero Cf 5
      vanishings = cofib-H₄-H₅ (moore3CW m) X Cf f les isoH x4 x5
        (moore3-H₄ m positive)

  recognize-moore3 : (m : ℕ) → 0 < m → (X : CW₀)
    → Finite≤ 4 (fst X) → isConnected 4 (fst X)
    → GroupEquiv (H̃ᶜʷ X 3) (ℤGroup/ m) → Hzero X 4
    → PT.∥ fst X ≃ Moore m 2 ∥₁
  recognize-moore3 m positive X finX connX coordinates x4 =
    PT.map recognize (moore3-representative m positive X connX coordinates)
    where
    x5 : Hzero X 5
    x5 = finite≤-homology-above X 4 5 finX (0 , refl)

    recognize : (Σ[ f ∈ (Moore m 2 → fst X) ] Hiso (moore3CW m) X 3 f)
      → fst X ≃ Moore m 2
    recognize (f , isoH) = invEquiv
      (f , moore3-map-isEquiv m positive X finX connX x4 x5 f isoH)
