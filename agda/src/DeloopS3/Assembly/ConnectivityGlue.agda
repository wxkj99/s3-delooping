{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Assembly.ConnectivityGlue where

-- Propagate simple connectivity of the two actual upper pushouts through
-- the assembly. SimpleFromPi1 supplies this input from the π₁ calculation.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Homotopy.Connected using (isConnected; isConnectedSubtr)
open import Cubical.Homotopy.Loopspace using (Ω)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (north)
open import DeloopS3.Local.RouteB2 using (Conn; SC; L-preserves-SC)
open import DeloopS3.Local.Base using (L)
open import DeloopS3.Assembly.Final public using (HomologyProfileInput; FibreInput)
open import DeloopS3.Assembly.Final.Geometry
import DeloopS3.Assembly.Final as Final
import DeloopS3.Bridge.SpanPi1.Connected as Span
open import DeloopS3.Assembly.LocalizedLoops using (P-sc-from-E-sc)
open import DeloopS3.Assembly.ConnectivityGlue.Pushout
open import DeloopS3.Assembly.ConnectivityGlue.Surjectivity public using (t-surjective)

record SimpleInput : Type where
  field
    E-simple : (c : ShortCase) → SC (E c)

-- First the common seam, then the outer total space; neither needs any
-- homology/contraction hypothesis or an inner-span fundamental-group model.
abstract
  R-connected : Conn R
  R-connected = Span.R-connected

  E*-simple : SimpleInput → SC E*
  E*-simple s = pushout-simple {A = R} {B = E octa} {C = E icosa}
    (iR octa) (iR icosa) r₀ R-connected
    (SimpleInput.E-simple s octa) (SimpleInput.E-simple s icosa)

  P-connected : SimpleInput → (c : ShortCase) → Conn (P c)
  P-connected s c = surjective-connected {X = E c} {Y = P c}
    (p c) (t-surjective c)
    (isConnectedSubtr {A = E c} 2 1 (SimpleInput.E-simple s c))

  P*-connected : SimpleInput → Conn P*
  P*-connected s = pushout-connected {A = N} {B = P octa} {C = P icosa}
    (jN octa) (jN icosa) n₀ (P-connected s octa) (P-connected s icosa)

fibreInput-from-simple : SimpleInput → FibreInput
FibreInput.total-SC (fibreInput-from-simple s) = SimpleInput.E-simple s
FibreInput.base-connected (fibreInput-from-simple s) = P-connected s
FibreInput.star-total-SC (fibreInput-from-simple s) = E*-simple s
FibreInput.star-base-connected (fibreInput-from-simple s) = P*-connected s

-- The selected fibres are already identified with S³ in Final.  Thus
-- the base and localized-base conclusions introduce no additional input.
abstract
  P-simple : SimpleInput → (c : ShortCase) → SC (P c)
  P-simple s c = P-sc-from-E-sc (E c) (P c) (p c) (e₀ c) (b c) refl
    (SimpleInput.E-simple s c) (P-connected s c) (Final.fibre-connected c)

  P*-simple : SimpleInput → SC P*
  P*-simple s = P-sc-from-E-sc E* P* p* e* b* refl
    (E*-simple s) (P*-connected s) Final.star-fibre-connected

  localized-P-simple : SimpleInput → (c : ShortCase) → SC (L (m c) (P c))
  localized-P-simple s c = L-preserves-SC (m c) (P-simple s c)

  localized-P*-simple : SimpleInput → SC (L 30 P*)
  localized-P*-simple s = L-preserves-SC 30 (P*-simple s)

  Deloop-final′ : HomologyProfileInput → SimpleInput
    → Σ[ B ∈ Pointed ℓ-zero ]
        (isConnected 2 (typ B) × (Ω B ≃∙ (S₊ 3 , north)))
  Deloop-final′ h s = Final.Deloop-final h (fibreInput-from-simple s)
