{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.OriginalSpan where

-- The literal spans: q is the circle-bundle leg and p the finite-cover leg.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.SumFin using (SumFin≃Fin)
open import Cubical.HITs.Pushout.Base using (Pushout)
open import Cubical.HITs.EilenbergMacLane1.Base using (EM₁; embase)
import Cubical.HITs.EilenbergMacLane1.Properties as EM
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Cert.Interpret.Short public using (ShortCase; octa; icosa)
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Cert.Interpret.Done as Done
import DeloopS3.Cert.Interpret.Realization as Realization
import DeloopS3.Cert.Input.Model as Input
import DeloopS3.Cert.Input.Initial.Endpoint as Initial
import DeloopS3.Cert.Input.Sheets as Sheets
import DeloopS3.Seifert.MarkedSeifert.FinalDone as Final
open import DeloopS3.Sphere.RP2UnitFiber public using (RP²)
open import DeloopS3.Cover.Cosets using (CosetFamily)
open import DeloopS3.Move.CancelMinimalCore using (EquivOver)

e : ShortCase → ℕ
e = Short.exponentOf

N : ShortCase → ℕ
N octa = 3
N icosa = 10

A : ShortCase → Type₀
A c = Final.M22e (pos (e c))

C : ShortCase → Type₀
C c = Input.M-original c

R : Type₀
R = RP²

abstract
  -- Done retains the finite-position/Kind reindexing, the wedge/rose
  -- chart and BOTH squares, rather than just a presentation equivalence.
  rose22≃literal : (c : ShortCase) → Short.M22e (e c) ≃ A c
  rose22≃literal c = Done.standard-to-marked (e c)

  -- The cover source is the descended bundle, so precompose by
  -- FinalDone's literal-source comparison.
  sourceCoverEquiv : (c : ShortCase) → A c ≃ Input.A_G c
  sourceCoverEquiv c = compEquiv
    {A = A c} {B = Final.Bundle.Mₑ (pos (e c))} {C = Input.A_G c}
    (Final.M22e≃Mₑ (pos (e c))) (Done.short-total c)

  sourceCoverEquiv-formula : (c : ShortCase)
    → sourceCoverEquiv c ≡ compEquiv
        (Final.M22e≃Mₑ (pos (e c))) (Done.short-total c)
  sourceCoverEquiv-formula c = refl

  cover-initial-over : (c : ShortCase)
    → EquivOver (Initial.initialProjection c) (fst {B = Input.Q c})
  cover-initial-over = Initial.cover-initial-over

  originalSpanEquiv : (c : ShortCase)
    → Realization.SpanEquiv (Input.OriginalSpan c) (Input.BaseSpan c)
  originalSpanEquiv = Input.originalSpanEquiv

q : (c : ShortCase) → A c → R
q c = Final.p22 (pos (e c))

p-model : (c : ShortCase) → A c → Input.M_G c
p-model c = fst ∘ equivFun (sourceCoverEquiv c)

p : (c : ShortCase) → A c → C c
p c = invEq (Input.originalTotalEquiv c) ∘ p-model c

X : ShortCase → Type₀
X c = Pushout (q c) (p c)

X_O X_I : Type₀
X_O = X octa
X_I = X icosa

abstract
  projectionPath : (c : ShortCase) (a : A c)
    → q c a ≡ Final.Bundle.pₑ (pos (e c))
        (equivFun (Final.M22e≃Mₑ (pos (e c))) a)
  projectionPath c = Final.projectionPath (pos (e c))

  p-model-done : (c : ShortCase)
    → p-model c ≡ Done.p c ∘ equivFun (Final.M22e≃Mₑ (pos (e c)))
  p-model-done c = refl

  p-model-formula : (c : ShortCase)
    → p-model c ≡ fst ∘ equivFun (sourceCoverEquiv c)
  p-model-formula c = refl

  p-formula : (c : ShortCase)
    → p c ≡ invEq (Input.originalTotalEquiv c) ∘ p-model c
  p-formula c = refl

private
  abstract
    -- The generic target change is sealed before specializing the large
    -- literal Seifert equivalence. Its path is the actual inverse law.
    change-target : {S T U : Type₀} (t : T ≃ U) (f : S → U) (z : T)
      → fiber (invEq t ∘ f) z ≃ fiber f (equivFun t z)
    change-target t f z = Σ-cong-equiv-snd λ a → compEquiv
      (congEquiv {x = invEq t (f a)} {y = z} t)
      (compPathlEquiv (sym (secEq t (f a))))

    model-fibres : (c : ShortCase) (m : Input.M_G c)
      → fiber (p-model c) m ≃ Input.Q c m
    model-fibres c m = subst
      (λ f → fiber f m ≃ Input.Q c m) (sym (p-model-done c))
      (compEquiv
        {A = fiber (Done.p c ∘ equivFun (Final.M22e≃Mₑ (pos (e c)))) m}
        {B = fiber (Done.p c) m} {C = Input.Q c m}
        (Σ-cong-equiv-fst {B = λ a → Done.p c a ≡ m}
          (Final.M22e≃Mₑ (pos (e c))))
        (Done.p-fibres c m))

    sheets≃Fin : (c : ShortCase) → Input.Sh c ≃ Fin (N c)
    sheets≃Fin octa = SumFin≃Fin 3
    sheets≃Fin icosa = SumFin≃Fin 10

    -- Elimination is into a proposition, not into a chosen enumeration.
    cosets-finite : (c : ShortCase) (b : EM₁ (Short.Δ c))
      → PT.∥ CosetFamily (Short.j c) b .fst ≃ Fin (N c) ∥₁
    cosets-finite c = EM.elimProp (Short.Δ c) (λ _ → PT.squash₁)
      PT.∣ compEquiv (invEquiv (Sheets.SheetData.e (Sheets.sheet-data c)))
        (sheets≃Fin c) ∣₁

abstract
  p-fibres : (c : ShortCase) (z : C c)
    → fiber (p c) z ≃ Input.Q c (equivFun (Input.originalTotalEquiv c) z)
  p-fibres c z = compEquiv
    {A = fiber (p c) z}
    {B = fiber (p-model c) (equivFun (Input.originalTotalEquiv c) z)}
    {C = Input.Q c (equivFun (Input.originalTotalEquiv c) z)}
    (change-target (Input.originalTotalEquiv c) (p-model c) z)
    (model-fibres c (equivFun (Input.originalTotalEquiv c) z))

  p-finite : (c : ShortCase) (z : C c)
    → PT.∥ fiber (p c) z ≃ Fin (N c) ∥₁
  p-finite c z = PT.map (compEquiv (p-fibres c z))
    (cosets-finite c (Input.ρ-M c (equivFun (Input.originalTotalEquiv c) z)))

open import DeloopS3.Bridge.SpanCells public using (RP²-finite)
import DeloopS3.Bridge.SpanCells as Cells
open import DeloopS3.Bridge.FiniteDim using (Finite≤; pushout-finite≤)
import DeloopS3.Cert.Check as Check

abstract
  A-finite : (c : ShortCase) → Finite≤ 3 (A c)
  A-finite c = Cells.seifert-finite (pos 2) (pos 2) (pos (e c))

  C-finite : (c : ShortCase) → Finite≤ 3 (C c)
  C-finite c = Cells.seifert-finite (pos 2) (pos 3)
    (pos (Input.localOrder c Check.C))

  X-finite : (c : ShortCase) → Finite≤ 4 (X c)
  X-finite c = pushout-finite≤ (q c) (p c) 3 2 3
    (A-finite c) RP²-finite (C-finite c)
