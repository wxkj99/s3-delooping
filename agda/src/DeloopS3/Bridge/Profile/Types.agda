{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Profile.Types where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (invEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Algebra.Group.Base using (Group₀)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.CW.Base using (CWskel ; hasCWskel)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ)
open import Cubical.CW.Connected using
  (isConnectedCW ; connectedCWskel→CWskel ; makeConnectedCW)
open import Cubical.Homotopy.Connected using (isConnected)
import Cubical.HITs.PropositionalTruncation as PT

open import DeloopS3.Bridge.Recognition.Notation using
  (CW₀ ; H̃ᶜʷ ; Hzero ; Finite≤)
open import DeloopS3.Bridge.ComponentHomology.ChainTools using
  (one-vertex-homology ; chosen-zero)

-- Check the records over abstract groups, without expanding cellular homology.
-- The public specialization below has exactly the recognition-profile fields.
private
  module Profiles (H : CW₀ → ℕ → Group₀) where
    record OProfile (X : CW₀) : Type₁ where
      field
        finite : Finite≤ 4 (fst X)
        simple : isConnected 3 (fst X)
        H₂-zero : isContr (fst (H X 2))
        H₃ : GroupEquiv (H X 3) (ℤGroup/ 3)
        H₄-zero : isContr (fst (H X 4))

    record IProfile (X : CW₀) : Type₁ where
      field
        finite : Finite≤ 4 (fst X)
        simple : isConnected 3 (fst X)
        H₂ : GroupEquiv (H X 2) (ℤGroup/ 2)
        H₃ : GroupEquiv (H X 3) (ℤGroup/ 10)
        H₄-zero : isContr (fst (H X 4))

open Profiles H̃ᶜʷ public

private
  abstract
    connected-skeleton-H₀ : (Y : CW₀)
      → isConnectedCW 0 (fst Y) → Hzero Y 0
    connected-skeleton-H₀ Y (sk , e) = chosen-zero Y t 0 zero
      where
      K : CWskel ℓ-zero
      K = connectedCWskel→CWskel {ℓ = ℓ-zero} {n = 0} sk

      t : hasCWskel (fst Y)
      t = K , invEquiv e

      one-vertex : K .snd .fst 0 ≡ 1
      one-vertex = sk .snd .snd .fst

      zero : isContr (fst (H̃ˢᵏᵉˡ K 0))
      zero = one-vertex-homology K one-vertex

    chosen-connected-H₀ : (Y : CW₀) → isConnected 2 (fst Y)
      → hasCWskel (fst Y) → Hzero Y 0
    chosen-connected-H₀ Y conn s =
      PT.rec {A = isConnectedCW 0 (fst Y)} {P = Hzero Y 0}
        (isPropIsContr {A = fst (H̃ᶜʷ Y 0)}) (connected-skeleton-H₀ Y)
        (makeConnectedCW {ℓ = ℓ-zero} 0 {C = fst Y} s conn)

abstract
  connected-H₀ : (Y : CW₀) → isConnected 2 (fst Y) → Hzero Y 0
  connected-H₀ Y conn =
    PT.rec {A = hasCWskel (fst Y)} {P = Hzero Y 0}
      (isPropIsContr {A = fst (H̃ᶜʷ Y 0)})
      (chosen-connected-H₀ Y conn) (snd Y)
