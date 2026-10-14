{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.SpanCells where

-- Finite witnesses from the actual diagrams. Product pushout charts
-- retain vertex maps and seams, without replacing a Seifert space by
-- a presentation 2-complex or discarding any torus prism.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Data.Sum using (_⊎_) renaming (inl to inj₁; inr to inj₂)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Susp.Base using (S¹IsoSuspBool; BoolIsoSusp⊥)
open import Cubical.HITs.Susp.Properties using (congSuspIso)
open import Cubical.HITs.RPn.Base using (RP; RP1≡S1)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.CW.Base using (finCW↑)
open import Cubical.CW.Instances.Empty using (finCWskel⊥; hasFinCWskel⊥)
open import DeloopS3.Bridge.FiniteDim public using
  (Finite≤; pushout-finite≤; cofib-finite≤)
open import DeloopS3.Bridge.FiniteDim using (sphere-finite≤; unit-finite≤)
open import DeloopS3.Move.CancelMinimal using (C; T²)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
import DeloopS3.Seifert.TwistedBundle.Base as RPChart
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)

abstract
  finite-equiv : {S T : Type₀} (d : ℕ) → S ≃ T
    → Finite≤ d T → Finite≤ d S
  finite-equiv d e = PT.map λ (sk , chart) → sk , compEquiv e chart

  circle-finite : Finite≤ 1 C
  circle-finite = finite-equiv 1 (invEquiv S¹≃C) (sphere-finite≤ 1)

  empty-finite : Finite≤ 0 ⊥
  empty-finite = PT.∣ finCW↑ 0 1 (1 , refl) finCWskel⊥ ,
    hasFinCWskel⊥ .snd .snd ∣₁

-- Disjoint unions are genuine pushouts over the empty type.
module Disjoint (S T : Type₀) where
  left : ⊥ → S
  left = Empty.rec
  right : ⊥ → T
  right = Empty.rec

  toSum : Pushout left right → S ⊎ T
  toSum (inl s) = inj₁ s
  toSum (inr t) = inj₂ t
  toSum (push () i)

  fromSum : S ⊎ T → Pushout left right
  fromSum (inj₁ s) = inl s
  fromSum (inj₂ t) = inr t

  sumIso : Iso (S ⊎ T) (Pushout left right)
  Iso.fun sumIso = fromSum
  Iso.inv sumIso = toSum
  Iso.sec sumIso (inl s) = refl
  Iso.sec sumIso (inr t) = refl
  Iso.sec sumIso (push () i)
  Iso.ret sumIso (inj₁ s) = refl
  Iso.ret sumIso (inj₂ t) = refl

  sumEquiv : (S ⊎ T) ≃ Pushout left right
  sumEquiv = isoToEquiv sumIso

abstract
  sum1-finite : {S T : Type₀} → Finite≤ 1 S → Finite≤ 1 T
    → Finite≤ 1 (S ⊎ T)
  sum1-finite {S} {T} s t = finite-equiv 1 (Disjoint.sumEquiv S T)
    (pushout-finite≤ (Disjoint.left S T) (Disjoint.right S T)
      0 1 1 empty-finite s t)

  sum2-finite : {S T : Type₀} → Finite≤ 2 S → Finite≤ 2 T
    → Finite≤ 2 (S ⊎ T)
  sum2-finite {S} {T} s t = finite-equiv 2 (Disjoint.sumEquiv S T)
    (pushout-finite≤ (Disjoint.left S T) (Disjoint.right S T)
      0 2 2 empty-finite s t)

-- A strict product-distribution chart, including the entire push seam.
-- It avoids a general product-skeleton dimension theorem.
module ProductPushout {S T U : Type₀} (f : S → T) (g : S → U)
  (D : Type₀) where
  left : S × D → T × D
  left (s , d) = f s , d
  right : S × D → U × D
  right (s , d) = g s , d

  toProduct : Pushout left right → Pushout f g × D
  toProduct (inl (t , d)) = inl t , d
  toProduct (inr (u , d)) = inr u , d
  toProduct (push (s , d) i) = push s i , d

  fromProduct : Pushout f g × D → Pushout left right
  fromProduct (inl t , d) = inl (t , d)
  fromProduct (inr u , d) = inr (u , d)
  fromProduct (push s i , d) = push (s , d) i

  productIso : Iso (Pushout left right) (Pushout f g × D)
  Iso.fun productIso = toProduct
  Iso.inv productIso = fromProduct
  Iso.sec productIso (inl t , d) = refl
  Iso.sec productIso (inr u , d) = refl
  Iso.sec productIso (push s i , d) = refl
  Iso.ret productIso (inl (t , d)) = refl
  Iso.ret productIso (inr (u , d)) = refl
  Iso.ret productIso (push (s , d) i) = refl

  productEquiv : Pushout left right ≃ (Pushout f g × D)
  productEquiv = isoToEquiv productIso

  left-β : (t : T) (d : D)
    → equivFun productEquiv (inl (t , d)) ≡ (inl t , d)
  left-β t d = refl
  right-β : (u : U) (d : D)
    → equivFun productEquiv (inr (u , d)) ≡ (inr u , d)
  right-β u d = refl
  push-β : (s : S) (d : D)
    → cong (equivFun productEquiv) (push (s , d))
      ≡ (λ i → push s i , d)
  push-β s d = refl

circle-cap : Bool → Unit
circle-cap _ = tt

abstract
  circle-pushout-equiv : C ≃ Pushout circle-cap circle-cap
  circle-pushout-equiv = compEquiv (invEquiv S¹≃C)
    (compEquiv (isoToEquiv S¹IsoSuspBool) (invEquiv PushoutSusp≃Susp))

module TorusCells = ProductPushout circle-cap circle-cap C
module CoreCells = ProductPushout Literal.wedgeLeg Literal.wedgeLeg C

private
  twoCopiesIso : Iso (Bool × C) (C ⊎ C)
  Iso.fun twoCopiesIso (false , z) = inj₁ z
  Iso.fun twoCopiesIso (true , z) = inj₂ z
  Iso.inv twoCopiesIso (inj₁ z) = false , z
  Iso.inv twoCopiesIso (inj₂ z) = true , z
  Iso.sec twoCopiesIso (inj₁ z) = refl
  Iso.sec twoCopiesIso (inj₂ z) = refl
  Iso.ret twoCopiesIso (false , z) = refl
  Iso.ret twoCopiesIso (true , z) = refl

abstract
  unit-circle-finite : Finite≤ 1 (Unit × C)
  unit-circle-finite = finite-equiv 1 (ΣUnit (λ _ → C)) circle-finite

  two-circles-finite : Finite≤ 1 (Bool × C)
  two-circles-finite = finite-equiv 1 (isoToEquiv twoCopiesIso)
    (sum1-finite circle-finite circle-finite)

  torus-pushout-equiv : T² ≃ Pushout TorusCells.left TorusCells.right
  torus-pushout-equiv = compEquiv
    (≃-× circle-pushout-equiv (idEquiv C))
    (invEquiv TorusCells.productEquiv)

  torus-finite : Finite≤ 2 T²
  torus-finite = finite-equiv 2 torus-pushout-equiv
    (pushout-finite≤ TorusCells.left TorusCells.right 1 1 1
      two-circles-finite unit-circle-finite unit-circle-finite)

  graph-finite : Finite≤ 1 Literal.P
  graph-finite = pushout-finite≤ Literal.wedgeLeg Literal.wedgeLeg
    0 1 1 unit-finite≤ circle-finite circle-finite

  core-pushout-equiv : Literal.Core ≃ Pushout CoreCells.left CoreCells.right
  core-pushout-equiv = invEquiv CoreCells.productEquiv

  core-finite : Finite≤ 2 Literal.Core
  core-finite = finite-equiv 2 core-pushout-equiv
    (pushout-finite≤ CoreCells.left CoreCells.right 1 2 2
      unit-circle-finite torus-finite torus-finite)

  three-tori-finite : Finite≤ 2 ((T² ⊎ T²) ⊎ T²)
  three-tori-finite = sum2-finite (sum2-finite torus-finite torus-finite) torus-finite

  three-circles-finite : Finite≤ 1 ((C ⊎ C) ⊎ C)
  three-circles-finite = sum1-finite (sum1-finite circle-finite circle-finite) circle-finite

  seifert-finite : (p q r : ℤ) → Finite≤ 3 (Literal.M p q r)
  seifert-finite p q r = pushout-finite≤
    (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r)
    2 2 1 three-tori-finite core-finite three-circles-finite

  -- RP 1 and the total of its double cover are two possibly different
  -- circle charts.  Retain pr₁ and cap; RP² is the inductive RP 2.
  RP¹-circle-equiv : RP 1 ≃ C
  RP¹-circle-equiv = compEquiv (pathToEquiv RP1≡S1)
    (compEquiv (invEquiv (isoToEquiv
      (compIso S¹IsoSuspBool (congSuspIso BoolIsoSusp⊥)))) S¹≃C)

  RP¹-finite : Finite≤ 1 (RP 1)
  RP¹-finite = finite-equiv 1 RP¹-circle-equiv circle-finite

  RP-overlap-finite : Finite≤ 1 RPChart.A
  RP-overlap-finite = finite-equiv 1 RPChart.fA circle-finite

  RP²-finite : Finite≤ 2 RP²
  RP²-finite = pushout-finite≤ RPChart.pr₁ RPChart.cap
    1 1 0 RP-overlap-finite RP¹-finite unit-finite≤
