{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Recognition where

-- Finite-dimensional recognition from a homology isomorphism and
-- vanishings of the actual cofibre, using Hurewicz and Blakers–Massey.
-- Indices are library h-levels: isConnected 4 means 2-connected;
-- isConnectedFun 6 means that the fibres are 4-connected.
open import DeloopS3.Bridge.Recognition.Notation public
open import DeloopS3.Bridge.Recognition.Dimension public
open import DeloopS3.Bridge.Recognition.HomologyDimension public
open import DeloopS3.Bridge.Recognition.Extension public
open import DeloopS3.Bridge.Recognition.Degree public
open import DeloopS3.Bridge.Recognition.Torsion public
open import DeloopS3.Bridge.Recognition.Models public
open import DeloopS3.Bridge.Recognition.Finite public
open import DeloopS3.Bridge.Recognition.Hurewicz public
open import DeloopS3.Bridge.Recognition.Initial public
open import DeloopS3.Bridge.Recognition.Excision public
open import DeloopS3.Bridge.Recognition.Representative public
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.Pushout.Base using (cofib)
open import Cubical.Homotopy.Connected
open import DeloopS3.Local.EO using (E_O ; E_O≃cofibre ; EO-model-contraction)
import Cubical.HITs.PropositionalTruncation as PT

-- Two absolute Hurewicz steps, one Blakers–Massey application,
-- and finite-cell detection of isEquiv.
bounded-map-isEquiv : (A B : CW₀) (f : fst A → fst B)
  (finA : Finite≤ 4 (fst A)) (finB : Finite≤ 4 (fst B))
  → isConnected 4 (fst A) → isConnectedFun 4 f
  → Hzero (cofibCW A B (finite≤→isFinCW {d = 4} finA) f) 4
  → Hzero (cofibCW A B (finite≤→isFinCW {d = 4} finA) f) 5
  → isEquiv f
bounded-map-isEquiv A B f finA finB connA connf h4 h5 =
  finite4-detect-equiv f finA finB
    (cofib5conn→map4conn f connA connf
      (two-hurewicz-steps (cofibCW A B (finite≤→isFinCW {d = 4} finA) f)
        (isConnectedCofib 3 {f = f} connf) h4 h5))

-- Naturality turns the specified H₃ isomorphism into initial connectivity;
-- the two cofibre vanishings are explicit inputs.
finite4-homology-map-isEquiv : (A B : CW₀) (f : fst A → fst B)
  (finA : Finite≤ 4 (fst A)) (finB : Finite≤ 4 (fst B))
  → isConnected 4 (fst A) → isConnected 4 (fst B)
  → Hiso A B 3 f
  → Hzero (cofibCW A B (finite≤→isFinCW {d = 4} finA) f) 4
  → Hzero (cofibCW A B (finite≤→isFinCW {d = 4} finA) f) 5
  → isEquiv f
finite4-homology-map-isEquiv A B f finA finB connA connB isoH =
  bounded-map-isEquiv A B f finA finB connA
    (H₃-iso→connected4 A B f connA connB isoH)

moore3-map-isEquiv-from-cofib : (m : ℕ) (X : CW₀)
  (finX : Finite≤ 4 (fst X)) → isConnected 4 (fst X)
  → (f : Moore m 2 → fst X) → Hiso (moore3CW m) X 3 f
  → Hzero (cofibCW (moore3CW m) X (finite≤→isFinCW {d = 4} (moore3-finite≤ m)) f) 4
  → Hzero (cofibCW (moore3CW m) X (finite≤→isFinCW {d = 4} (moore3-finite≤ m)) f) 5
  → isEquiv f
moore3-map-isEquiv-from-cofib m X finX connX f =
  finite4-homology-map-isEquiv (moore3CW m) X f
    (moore3-finite≤ m) finX (moore3-connected m) connX

-- The Local.EO model: the map and homology facts about its dependent
-- cofibre stay in one truncation.
EO-from-merely-map-profile : (X : CW₀)
  → Finite≤ 4 (fst X) → isConnected 4 (fst X)
  → PT.∥ Σ[ f ∈ (Moore 3 2 → fst X) ]
      (Hiso (moore3CW 3) X 3 f
      × Hzero (cofibCW (moore3CW 3) X (finite≤→isFinCW {d = 4} (moore3-finite≤ 3)) f) 4
      × Hzero (cofibCW (moore3CW 3) X (finite≤→isFinCW {d = 4} (moore3-finite≤ 3)) f) 5) ∥₁
  → PT.∥ fst X ≃ E_O ∥₁
EO-from-merely-map-profile X finX connX = PT.map λ (f , isoH , h4 , h5) →
  compEquiv (invEquiv (f , moore3-map-isEquiv-from-cofib 3 X finX connX f isoH h4 h5))
    (invEquiv E_O≃cofibre)

