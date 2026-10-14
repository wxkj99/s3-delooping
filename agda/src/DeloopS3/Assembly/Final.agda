{-# OPTIONS --cubical --safe --guardedness #-}
module DeloopS3.Assembly.Final where

-- Assemble the delooping from localized contractions and connectivity of
-- the actual mixed τ-bottom cubes, with pointed naturality from UnitNaturality.
-- Bridge.Profile and Assembly.SimpleFromPi1 supply the two input records;
-- Assembly.Complete exports the unconditional theorem.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Homotopy.Connected using
  (isConnected ; isConnectedSubtr ; isConnectedRetractFromIso)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
open import Cubical.HITs.Susp.Base using (north)
open import DeloopS3.Local.Base using (L ; η ; local-L)
open import DeloopS3.Local.Powers using (local-path)
open import DeloopS3.Local.EI using (local-factor)
open import DeloopS3.Local.RouteB2 using (Conn ; SC ; L-map ; L-preserves-SC)
open import DeloopS3.Local.Assembly.PushoutContractible using (localize-pushout-contractible)
open import DeloopS3.Assembly.LocalizedLoops using
  (P-sc-from-E-sc)
open import DeloopS3.Assembly.RP2LocalNull public using (RP²≃cofib-double ; RP²-local₂-contr)
open import DeloopS3.Assembly.Final.Geometry public
open import DeloopS3.Assembly.LocalizationMaps using (L-equiv ; L-map-homotopy ; L-map-comp)
open import DeloopS3.Assembly.Final.Naturality using (unit-square-descent ; common-coordinate)
import DeloopS3.Assembly.Final.UnitNaturality as UnitNat
import DeloopS3.Assembly.FibreNaturality as FibreNat
import DeloopS3.Assembly.DefB as DefB

EO EI : Type
EO = E octa
EI = E icosa

record HomologyProfileInput : Type where
  field
    contrO : isContr (L 3 EO)
    contrI : isContr (L 10 EI)

-- No third contraction hypothesis: use exactly the ACTUAL span over R.
abstract
  contrStar : HomologyProfileInput → isContr (L 30 E*)
  contrStar h = localize-pushout-contractible 30 3 10 2
    EO EI R (iR octa) (iR icosa)
    (transfer octa) (transfer icosa)
    (λ Z → local-factor {m = 30} {d = 2} {b = 15} {Z = Z} refl)
    (HomologyProfileInput.contrO h) (HomologyProfileInput.contrI h)
    RP²-local₂-contr

contrG : HomologyProfileInput → (c : ShortCase) → isContr (L (m c) (E c))
contrG h octa = HomologyProfileInput.contrO h
contrG h icosa = HomologyProfileInput.contrI h

-- Localized fibre-loop equivalences with their unit naturality.
open UnitNat public using (loopG ; loopStar)

κ : (c : ShortCase) → L (m c) (Fib c) → L 30 Fib*
κ c z = L-map 30 {A = Fib c} {B = Fib*} (U c) (ι c (Fib c) z)

κ-unit : (c : ShortCase) (x : Fib c)
  → κ c (η {m c} {Fib c} x) ≡ η {30} {Fib*} (U c x)
κ-unit c x = cong (L-map 30 {A = Fib c} {B = Fib*} (U c)) (ι-β c (Fib c) x)

record FibreInput : Type where
  field
    total-SC : (c : ShortCase) → SC (E c)
    base-connected : (c : ShortCase) → Conn (P c)
    star-total-SC : SC E*
    star-base-connected : Conn P*

-- FibreInput contains only connectivity data; fibre equivalences, common-F
-- coordinates, cocone homotopies, and localized unit coherence are constructed.

abstract
  fibre-connected : (c : ShortCase) → Conn (Fib c)
  fibre-connected c = isConnectedRetractFromIso 2 (equivToIso (χ c))
    (isConnectedSubtr {A = S₊ 3} 2 2 (sphereConnected 3))

  star-fibre-connected : Conn Fib*
  star-fibre-connected = isConnectedRetractFromIso 2 (equivToIso χ*)
    (isConnectedSubtr {A = S₊ 3} 2 2 (sphereConnected 3))

module Assemble (homology : HomologyProfileInput) (fibres : FibreInput) where
  private
    module FI = FibreInput fibres

  abstract
    base-SC : (c : ShortCase) → SC (P c)
    base-SC c = P-sc-from-E-sc (E c) (P c) (p c) (e₀ c) (b c) refl
      (FI.total-SC c) (FI.base-connected c) (fibre-connected c)

    star-base-SC : SC P*
    star-base-SC = P-sc-from-E-sc E* P* p* e* b* refl
      FI.star-total-SC FI.star-base-connected star-fibre-connected

    common : (c : ShortCase) (z : F)
      → U c (equivFun (λG c) z) ≡ equivFun λ* z
    common octa z = funExt⁻ FibreNat.naturality-O z
    common icosa z = funExt⁻ FibreNat.naturality-I z

    coordinates : (c : ShortCase) (x : Fib c)
      → equivFun χ* (U c x) ≡ equivFun (χ c) x
    coordinates c = common-coordinate F (Fib c) Fib* (S₊ 3)
      (λG c) λ* σ (U c) (common c)

  eG : (c : ShortCase) → typ (Ω (Q c)) ≃ L (m c) (Fib c)
  eG c = loopG c (base-SC c) (contrG homology c)
  eStar : typ (Ω T) ≃ L 30 Fib*
  eStar = loopStar star-base-SC (contrStar homology)

  φ : (c : ShortCase) → typ (Ω (Q c)) ≃ L (m c) (S₊ 3)
  φ c = compEquiv (eG c) (L-equiv (m c) {A = Fib c} {B = S₊ 3} (χ c))
  φT : typ (Ω T) ≃ L 30 (S₊ 3)
  φT = compEquiv eStar (L-equiv 30 {A = Fib*} {B = S₊ 3} χ*)

  abstract
    -- Descend the explicit unit square; do not posit the final h1/h2.
    fibre-loop-square : (c : ShortCase) (a : typ (Ω (Q c)))
      → κ c (equivFun (eG c) a) ≡ equivFun eStar (fst (Ω→ (u c)) a)
    fibre-loop-square c = unit-square-descent (m c) (Fib c)
      (typ (Ω (Q c))) (typ (Ω T)) (L 30 Fib*)
      (eG c) eStar (fst (Ω→ (u c))) (κ c)
      (transfer c (typ (Ω T)) (local-path (local-L 30 P*) (pt T) (pt T)))
      (λ x → UnitNat.unit-loop-square c (base-SC c) star-base-SC
          (contrG homology c) (contrStar homology) x
        ∙ cong (invEq eStar) (sym (κ-unit c x)))

    sphere-square : (c : ShortCase) (z : L (m c) (Fib c))
      → ι c (S₊ 3) (L-map (m c) {A = Fib c} {B = S₊ 3} (equivFun (χ c)) z)
        ≡ L-map 30 {A = Fib*} {B = S₊ 3} (equivFun χ*) (κ c z)
    sphere-square c z =
      sym (funExt⁻ (ι-natural c {A = Fib c} {B = S₊ 3} (equivFun (χ c))) z)
      ∙ funExt⁻ (L-map-homotopy 30 {A = Fib c} {B = S₊ 3}
          (equivFun (χ c)) (equivFun χ* ∘ U c) (λ x → sym (coordinates c x)))
          (ι c (Fib c) z)
      ∙ funExt⁻ (L-map-comp 30 {A = Fib c} {B = Fib*} {C = S₊ 3}
          (U c) (equivFun χ*)) (ι c (Fib c) z)

    h : (c : ShortCase) (a : typ (Ω (Q c)))
      → ι c (S₊ 3) (equivFun (φ c) a) ≡ equivFun φT (fst (Ω→ (u c)) a)
    h c a = sphere-square c (equivFun (eG c) a)
      ∙ cong (L-map 30 {A = Fib*} {B = S₊ 3} (equivFun χ*)) (fibre-loop-square c a)

  module B = DefB

  naturalLoopData : B.NaturalLoopData (Q octa) (Q icosa) T (u octa) (u icosa)
  B.NaturalLoopData.Q1-connected naturalLoopData =
    isConnectedSubtr {A = typ (Q octa)} 2 1 (L-preserves-SC 3 (base-SC octa))
  B.NaturalLoopData.Q2-connected naturalLoopData =
    isConnectedSubtr {A = typ (Q icosa)} 2 1 (L-preserves-SC 10 (base-SC icosa))
  B.NaturalLoopData.T-simply-connected naturalLoopData = L-preserves-SC 30 star-base-SC
  B.NaturalLoopData.φ1 naturalLoopData = φ octa
  B.NaturalLoopData.φ2 naturalLoopData = φ icosa
  B.NaturalLoopData.φT naturalLoopData = φT
  B.NaturalLoopData.h1 naturalLoopData = h octa
  B.NaturalLoopData.h2 naturalLoopData = h icosa

  abstract
    result : Σ[ B ∈ Pointed ℓ-zero ] (isConnected 2 (typ B) × (Ω B ≃∙ (S₊ 3 , north)))
    result = B.Deloop-from-data (Q octa) (Q icosa) T (u octa) (u icosa) naturalLoopData

abstract
  Deloop-final : HomologyProfileInput → FibreInput
    → Σ[ B ∈ Pointed ℓ-zero ] (isConnected 2 (typ B) × (Ω B ≃∙ (S₊ 3 , north)))
  Deloop-final = Assemble.result
