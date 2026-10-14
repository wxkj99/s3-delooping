{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Compare the Seifert filling and descended bundle via the small quotient
-- span in Base.fA coordinates. The input DescentChart retains the entire
-- torus-boundary map; DescentChart.Finish supplies it for FinalDone.
module DeloopS3.Seifert.MarkedSeifert.Final where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Data.Bool using (false)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.NatMinusOne
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Homotopy.Group.Base using (π)
open import Cubical.HITs.RPn.Base using (cov⁻¹)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (commₖ)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²; mulC; _+C_)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv public using (M22e)
open import DeloopS3.Seifert.MarkedSeifert.WRelJR public
  using (WComparison-checked; module WComparisonInstance)
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (row)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus
  using (Kinv)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.TorusMap using (λ₂)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third using (Fill)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Basis
  using (mulC-one)
open import DeloopS3.Seifert.TwistedBundle.SignCircle using (SignC; ε)
open import DeloopS3.Seifert.TwistedBundle.Base using (A; w₁; Ksign; λA; fA)
open import DeloopS3.Seifert.TwistedBundle.Cell public using (module Bundle)
open import DeloopS3.Seifert.TwistedBundle.Flattening using (module Total)
open import DeloopS3.Seifert.TwistedBundle.SmallChart
  using (module Filling; ε-natural)
import DeloopS3.Seifert.TwistedBundle.Coherent as Coherent
import DeloopS3.Seifert.TwistedBundle.Pi2Zero as Pi2Zero
open import DeloopS3.Seifert.TwistedBundle.Pi2Zero public using (pi₂-Mₑ-zero)
open import DeloopS3.Sphere.RP2UnitFiber
  using (RP²; q; q-fiber; q-fibers-are-sets)

-- The literal basepoint in the original Seifert pushout.
pt : (e : ℤ) → M22e e
pt e = inl (inl 0C , 0C)

-- The marked W comparison identifies M22e with the third torus filling.
abstract
  M22e≃Fill : (e : ℤ) → M22e e ≃ Fill e
  M22e≃Fill = WComparisonInstance.thirdFilling

-- Keep transport/inverse cancellation generic: specializing a J proof
-- after unfolding the descended EM family causes needless normalization.
private
  abstract
    invert-evaluation : ∀ {ℓX ℓY ℓC}
      {X : Type ℓX} {Y : Type ℓY} {Z : Type ℓC}
      (a : X ≃ Z) (b : Y ≃ Z) (x : X) (y : Y)
      → a .fst x ≡ b .fst y → x ≡ invEq a (b .fst y)
    invert-evaluation a b x y h = sym (retEq a x) ∙ cong (invEq a) h

-- Naturality and inverse cancellation give the left square;
-- Action.clutching-seam gives the right square.
module SmallSpan (e : ℤ) where
  module F = Total e
  module S = Filling e

  SmallFill : Type₀
  SmallFill = Pushout λA S.rowShift

  abstract
    left-square : S.leftTotal .fst ∘ F.left ≡ λA ∘ S.overlapTotal .fst
    left-square = funExt λ { (T , ((x , p) , y) , t) →
      ΣPathP (refl , invert-evaluation
        (ε (w₁ x) (subst Coherent.Reg (sym p) y)) (ε T y)
        (subst SignC (sym p) t) t (ε-natural (w₁ x) p y t)) }

    right-square : S.rightTotal .fst ∘ F.right
      ≡ S.rowShift ∘ S.overlapTotal .fst
    right-square = funExt λ { (T , (a , y) , t) →
      Coherent.Action.clutching-seam e T a y t }

    quotientSpan≃Small : F.Filling ≃ SmallFill
    quotientSpan≃Small = pushoutEquiv F.left F.right λA S.rowShift
      S.overlapTotal S.leftTotal S.rightTotal left-square right-square

    flattenSmall : Bundle.Mₑ e ≃ SmallFill
    flattenSmall = compEquiv
      {A = Bundle.Mₑ e} {B = F.Filling} {C = SmallFill}
      F.flattenDescent quotientSpan≃Small

-- The specified fA is retained, not replaced by a
-- positively oriented circle chart without a comparison theorem.
torusToCover : T² → A × C
torusToCover (u , t) = invEq fA u , t

λsign : T² → Ksign
λsign = λA ∘ torusToCover

SignFill : ℤ → Type₀
SignFill e = Pushout λsign (row e (pos 1))

abstract
  torusCoverEquiv : T² ≃ (A × C)
  torusCoverEquiv = Σ-cong-equiv-fst {B = λ _ → C} (invEquiv fA)

  torusCoverEquiv-map : torusCoverEquiv .fst ≡ torusToCover
  torusCoverEquiv-map = refl

  sign-row : (e : ℤ)
    → row e (pos 1) ≡ Filling.rowShift e ∘ torusToCover
  sign-row e = funExt λ { (u , t) →
    cong (mulC e u +C_) (mulC-one t)
    ∙ commₖ {G = ℤAbGroup} 1 (mulC e u) t
    ∙ cong (λ v → t +C mulC e v) (sym (secEq fA u)) }

  signFill≃Small : (e : ℤ) → SignFill e ≃ SmallSpan.SmallFill e
  signFill≃Small e = pushoutEquiv λsign (row e (pos 1))
    λA (Filling.rowShift e) torusCoverEquiv (idEquiv Ksign) (idEquiv C)
    (cong (λA ∘_) (sym torusCoverEquiv-map))
    (sign-row e ∙ cong (Filling.rowShift e ∘_) (sym torusCoverEquiv-map))

  Mₑ≃SignFill : (e : ℤ) → Bundle.Mₑ e ≃ SignFill e
  Mₑ≃SignFill e = compEquiv
    {A = Bundle.Mₑ e} {B = SmallSpan.SmallFill e} {C = SignFill e}
    (SmallSpan.flattenSmall e) (invEquiv (signFill≃Small e))

-- Pi2Zero gives vanishing at every point of the sphere pullback. Choose a
-- sheet under propositional truncation and eliminate into isContr, without
-- assuming an equivalence preserves the specified bundle basepoint.
private
  abstract
    mere-sheet : (b : RP²) → PT.∥ fiber q b ∥₁
    mere-sheet b = PT.map
      (λ f → invEq (q-fiber b) (invEq f false)) (snd (cov⁻¹ 2 b))

module BundleAtEveryPoint (e : ℤ) where
  module P = Pi2Zero.ActualBundle e

  abstract
    pi₂-zero : ¬ e ≡ pos 0 → (m : Bundle.Mₑ e)
      → isContr (π 2 (Bundle.Mₑ e , m))
    pi₂-zero nz m = PT.rec isPropIsContr
      (λ sheet → P.Pullback.AtPoint.total-cover-π₂-zero
        q-fibers-are-sets m sheet (P.pullback-π₂-zero nz))
      (mere-sheet (Bundle.pₑ e m))

-- SignFill inherits the descended bundle's circle fibres and π₂ vanishing
-- for e ≠ 0; it is a different pushout presentation from Fill.
pSignFill : (e : ℤ) → SignFill e → RP²
pSignFill e = Bundle.pₑ e ∘ invEq (Mₑ≃SignFill e)

abstract
  sign-fibres : (e : ℤ) (b : RP²)
    → fiber (pSignFill e) b ≃ fiber (Bundle.pₑ e) b
  sign-fibres e b = Σ-cong-equiv-fst
    {B = λ m → Bundle.pₑ e m ≡ b} (invEquiv (Mₑ≃SignFill e))

  sign-circleFibres : (e : ℤ) (b : RP²)
    → PT.∥ fiber (pSignFill e) b ≃ C ∥₁
  sign-circleFibres e b = PT.map (compEquiv (sign-fibres e b))
    (Bundle.circleFibres e b)

  pi₂-SignFill-zero : (e : ℤ) → ¬ e ≡ pos 0 → (s : SignFill e)
    → isContr (π 2 (SignFill e , s))
  pi₂-SignFill-zero e nz s = Pi2Zero.π₂-equiv-zero
    {X = SignFill e} {Y = Bundle.Mₑ e} (invEquiv (Mₑ≃SignFill e)) s
    (BundleAtEveryPoint.pi₂-zero e nz (invEq (Mₑ≃SignFill e) s))

-- The boundary field is a path of maps on T², retaining the basepoint,
-- both loops and the square. DescentChart.Finish constructs this chart.
record DescentChart : Type₁ where
  field
    total : Kinv ≃ Ksign
    boundary : total .fst ∘ λ₂ ≡ λsign

-- Assemble from a marked descent chart, as instantiated in FinalDone.
-- Equivalence holds for every e; e ≠ 0 is needed only for π₂ vanishing.
module FromDescentChart (chart : DescentChart) where
  open DescentChart chart

  abstract
    fillComparison : (e : ℤ) → Fill e ≃ SignFill e
    fillComparison e = pushoutEquiv λ₂ (row e (pos 1))
      λsign (row e (pos 1)) (idEquiv T²) total (idEquiv C) boundary refl

    M22e≃Mₑ : (e : ℤ) → M22e e ≃ Bundle.Mₑ e
    M22e≃Mₑ e = compEquiv
      {A = M22e e} {B = Fill e} {C = Bundle.Mₑ e}
      (M22e≃Fill e)
      (compEquiv {A = Fill e} {B = SignFill e} {C = Bundle.Mₑ e}
        (fillComparison e) (invEquiv (Mₑ≃SignFill e)))

  p22 : (e : ℤ) → M22e e → RP²
  p22 e = Bundle.pₑ e ∘ M22e≃Mₑ e .fst

  projectionPath : (e : ℤ) (m : M22e e)
    → p22 e m ≡ Bundle.pₑ e (M22e≃Mₑ e .fst m)
  projectionPath e m = refl

  abstract
    fibreComparison : (e : ℤ) (b : RP²)
      → fiber (p22 e) b ≃ fiber (Bundle.pₑ e) b
    fibreComparison e b = Σ-cong-equiv-fst
      {B = λ m → Bundle.pₑ e m ≡ b} (M22e≃Mₑ e)

    circleFibres : (e : ℤ) (b : RP²) → PT.∥ fiber (p22 e) b ≃ C ∥₁
    circleFibres e b = PT.map (compEquiv (fibreComparison e b))
      (Bundle.circleFibres e b)

    capFibre : (e : ℤ) → fiber (p22 e) (inr tt) ≃ C
    capFibre e = compEquiv (fibreComparison e (inr tt)) (Bundle.baseFibre e)

    pi₂-M22e-zero : (e : ℤ) → ¬ e ≡ pos 0
      → isContr (π 2 (M22e e , pt e))
    pi₂-M22e-zero e nz = Pi2Zero.π₂-equiv-zero
      {X = M22e e} {Y = Bundle.Mₑ e} (M22e≃Mₑ e) (pt e)
      (BundleAtEveryPoint.pi₂-zero e nz (M22e≃Mₑ e .fst (pt e)))
