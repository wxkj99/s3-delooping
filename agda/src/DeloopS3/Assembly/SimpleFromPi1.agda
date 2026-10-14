{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Assembly.SimpleFromPi1 where

-- Compare the literal span used by the π₁ calculation with the actual
-- assembly span, then transport its unconditional simple connectivity.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (invIso)
open import Cubical.Foundations.Pointed
open import Cubical.Data.Int using (pos)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.Homotopy.Connected
  using (isConnected; isConnectedRetractFromIso)
open import Cubical.Homotopy.Loopspace using (Ω)
open import DeloopS3.Assembly.ActualSpans using (ShortCase; E)
import DeloopS3.Assembly.ActualSpans as Actual
open import DeloopS3.Assembly.ConnectivityGlue
  using (SimpleInput; HomologyProfileInput; Deloop-final′)
import DeloopS3.Bridge.OriginalSpan as OS
import DeloopS3.Bridge.SpanPi1.Target as Target
import DeloopS3.Cert.Input.Model as Input
import DeloopS3.Seifert.MarkedSeifert.FinalDone as Final

private
  abstract
    A-equiv : (c : ShortCase) → OS.A c ≃ Actual.A c
    A-equiv c = Final.M22e≃Mₑ (pos (OS.e c))

    C-equiv : (c : ShortCase) → OS.C c ≃ Actual.C c
    C-equiv c = Input.originalTotalEquiv c

    q-square : (c : ShortCase) (a : OS.A c)
      → OS.q c a ≡ Actual.q c (equivFun (A-equiv c) a)
    q-square c = OS.projectionPath c

    -- The C-vertex comparison points from the original total space to
    -- Done.M_G. Its section law cancels the inverse in OS.p.
    p-square : (c : ShortCase) (a : OS.A c)
      → equivFun (C-equiv c) (OS.p c a)
        ≡ Actual.p c (equivFun (A-equiv c) a)
    p-square c a = secEq (Input.originalTotalEquiv c) (OS.p-model c a)
      ∙ funExt⁻ (OS.p-model-done c) a

abstract
  X≃E : (c : ShortCase) → OS.X c ≃ E c
  X≃E c = pushoutEquiv
    {A₁ = OS.A c} {B₁ = OS.R} {C₁ = OS.C c}
    {A₂ = Actual.A c} {B₂ = Actual.R} {C₂ = Actual.C c}
    (OS.q c) (OS.p c) (Actual.q c) (Actual.p c)
    (A-equiv c) (idEquiv OS.R) (C-equiv c)
    (funExt (q-square c)) (funExt (p-square c))

E-simple-from-X : ((c : ShortCase) → isConnected 3 (OS.X c)) → SimpleInput
SimpleInput.E-simple (E-simple-from-X X-simple) c =
  isConnectedRetractFromIso 3 {A = E c} {B = OS.X c}
    (invIso (equivToIso (X≃E c))) (X-simple c)

-- Target.X-simple supplies simple connectivity without a marking hypothesis.
simpleInput : SimpleInput
simpleInput = E-simple-from-X Target.X-simple

abstract
  Deloop-final″ : HomologyProfileInput
    → Σ[ B ∈ Pointed ℓ-zero ]
        (isConnected 2 (typ B) × (Ω B ≃∙ (S₊ 3 , north)))
  Deloop-final″ h = Deloop-final′ h simpleInput
