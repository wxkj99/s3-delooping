{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Absorb the boundary sign without changing Base.fA. The loop markings
-- from L9 and the odd-square law from L11 give the full torus-boundary path.
module DeloopS3.Seifert.MarkedSeifert.DescentChart.Finish where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; false; true)
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Seifert.TwistedBundle.Base using (A; R; Ksign)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus
  using (Kinv; kbase; j; r)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary
  using (based; based-comp)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third
  using (cong-based)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.FilledLoops
  using (based-sym)
open import DeloopS3.Seifert.MarkedSeifert.DescentChart
  using (raw; raw-base; F₀; V; J₀; τ; a★; sgnLoop; boundarySign;
         sign-u; sign-v; reverseK; reverseK-base; reverseK-j; reverseK-r;
         based-chain; MarkedTotal; module FromMarkedTotal)
open import DeloopS3.Seifert.MarkedSeifert.DescentChart.L9
  using (raw-r; raw-j-projects)
open import DeloopS3.Seifert.MarkedSeifert.DescentChart.L11 using (odd-square)
open import DeloopS3.Seifert.MarkedSeifert.Final using (DescentChart)

-- Generic path algebra first: the composite pointing is cong g p · q,
-- not refl.  This retains every inverse-pointing path of reverseK.
opaque
  based-compose-image : ∀ {ℓX ℓY ℓZ}
    {X : Type ℓX} {Y : Type ℓY} {Z : Type ℓZ}
    (f : X → Y) (g : Y → Z) {x : X} {y : Y} {z : Z}
    (p : f x ≡ y) (q : g y ≡ z) (l : x ≡ x)
    → based (cong g p ∙ q) (cong (g ∘ f) l)
      ≡ based q (cong g (based p (cong f l)))
  based-compose-image f g p q l =
    based-chain (cong g p) q (cong (g ∘ f) l)
    ∙ cong (based q) (sym (cong-based g p (cong f l)))

  based-reversing-square : ∀ {ℓ} {X : Type ℓ}
    (f : X → X) {x : X} (p : f x ≡ x) (l : x ≡ x)
    → based p (cong f l) ≡ sym l
    → based p (cong f (l ∙ l)) ≡ sym (l ∙ l)
  based-reversing-square f p l eq = cong (based p) (cong-∙ f l l)
    ∙ based-comp p (cong f l) (cong f l)
    ∙ cong₂ _∙_ eq eq ∙ sym (symDistr l l)

  based-compose-marking : ∀ {ℓX ℓY ℓZ}
    {X : Type ℓX} {Y : Type ℓY} {Z : Type ℓZ}
    (f : X → Y) (g : Y → Z) (x : X) (y : Y) (z : Z)
    (p : f x ≡ y) (q : g y ≡ z)
    (l : x ≡ x) (m : y ≡ y) (n : z ≡ z)
    → based p (cong f l) ≡ m → based q (cong g m) ≡ n
    → based (cong g p ∙ q) (cong (g ∘ f) l) ≡ n
  based-compose-marking f g x y z p q l m n first second =
    based-compose-image f g p q l
    ∙ cong (based q ∘ cong g) first ∙ second

  based-compose-reversed : ∀ {ℓX ℓY}
    {X : Type ℓX} {Y : Type ℓY}
    (f : X → X) (g : X → Y) (x : X) (y : Y)
    (p : f x ≡ x) (q : g x ≡ y) (l : x ≡ x) (m : y ≡ y)
    → based p (cong f l) ≡ sym l → based q (cong g l) ≡ m
    → based (cong g p ∙ q) (cong (g ∘ f) l) ≡ sym m
  based-compose-reversed f g x y p q l m first second =
    based-compose-marking f g x x y p q l (sym l) (sym m) first
      (based-sym q (cong g l) ∙ cong sym second)

  -- Combine functoriality with an odd-square law while the map and the
  -- projection are variables.  Specializing a concrete concatenation of
  -- these equalities needlessly normalizes the descended EM family.
  square-from-projection : ∀ {ℓX ℓY ℓB}
    {X : Type ℓX} {Y : Type ℓY} {B : Type ℓB}
    (f : X → Y) (x : X) (y : Y) (b : f x ≡ y) (l : x ≡ x)
    (π : Y → B) (t : π y ≡ π y) (k : y ≡ y)
    → ((v : y ≡ y) → cong π v ≡ t → v ∙ v ≡ k ∙ k)
    → cong π (based b (cong f l)) ≡ t
    → based b (cong f (l ∙ l)) ≡ k ∙ k
  square-from-projection f x y b l π t k odd mark =
    cong (based b) (cong-∙ f l l)
    ∙ based-comp b (cong f l) (cong f l)
    ∙ odd (based b (cong f l)) mark

opaque
  reverseK-j² : based reverseK-base (cong (reverseK .fst) (j ∙ j))
    ≡ sym (j ∙ j)
  reverseK-j² = based-reversing-square {X = Kinv}
    (reverseK .fst) {x = kbase} reverseK-base j reverseK-j

-- Assemble while the equivalence is a variable.  Keeping this abstraction
-- through the record constructor avoids normalizing Sigma-valued path
-- compositions at raw's concrete forward map. L9 supplies the markings
-- for the concrete instance below.
module Assemble
  (e : Kinv ≃ Ksign)
  (pointing : e .fst kbase ≡ F₀ a★)
  (fibre-mark : based {X = Ksign} {a = e .fst kbase} {b = F₀ a★}
    pointing (cong (e .fst) r) ≡ V a★ hC)
  (base-mark : cong (λ (z : Ksign) → fst z)
    (based {X = Ksign} {a = e .fst kbase} {b = F₀ a★}
      pointing (cong (e .fst) j)) ≡ τ a★) where

  opaque
    raw-j² : based {X = Ksign} {a = e .fst kbase} {b = F₀ a★}
      pointing (cong (e .fst) (j ∙ j)) ≡ J₀ a★ ∙ J₀ a★
    raw-j² = square-from-projection {X = Kinv} {Y = Ksign} {B = R}
      (e .fst) kbase (F₀ a★) pointing j
      (λ (z : Ksign) → fst z) (τ a★) (J₀ a★) (odd-square a★) base-mark

  -- The maps and both composite pointings remain transparent.
  chooseTotal : Bool → Kinv ≃ Ksign
  chooseTotal false = e
  chooseTotal true = compEquiv {A = Kinv} {B = Kinv} {C = Ksign} reverseK e

  chooseBase : (s : Bool) → chooseTotal s .fst kbase ≡ F₀ a★
  chooseBase false = pointing
  chooseBase true = cong (e .fst) reverseK-base ∙ pointing

  opaque
    choose-r : (s : Bool)
      → based {X = Ksign} {a = chooseTotal s .fst kbase} {b = F₀ a★}
          (chooseBase s) (cong (chooseTotal s .fst) r) ≡ V a★ hC
    choose-r false = fibre-mark
    choose-r true = based-compose-marking {X = Kinv} {Y = Kinv} {Z = Ksign}
      (reverseK .fst) (e .fst) kbase kbase (F₀ a★)
      reverseK-base pointing r r (V a★ hC) reverseK-r fibre-mark

    choose-j² : (s : Bool)
      → based {X = Ksign} {a = chooseTotal s .fst kbase} {b = F₀ a★}
          (chooseBase s) (cong (chooseTotal s .fst) (j ∙ j))
        ≡ sgnLoop s (J₀ a★ ∙ J₀ a★)
    choose-j² false = raw-j²
    choose-j² true = based-compose-reversed {X = Kinv} {Y = Ksign}
      (reverseK .fst) (e .fst) kbase (F₀ a★)
      reverseK-base pointing (j ∙ j) (J₀ a★ ∙ J₀ a★) reverseK-j² raw-j²

  markedTotal : MarkedTotal
  markedTotal .MarkedTotal.total = chooseTotal boundarySign
  markedTotal .MarkedTotal.basepoint = chooseBase boundarySign
  markedTotal .MarkedTotal.mark-u =
    _∙_ {ℓ-zero} {F₀ a★ ≡ F₀ a★} (choose-j² boundarySign) (sym sign-u)
  markedTotal .MarkedTotal.mark-v =
    _∙_ {ℓ-zero} {F₀ a★ ≡ F₀ a★} (choose-r boundarySign) (sym sign-v)

  -- The existing Compare.homotopy application retains the generating
  -- squares and fills the remaining torus compatibility in Ksign.
  chart : DescentChart
  chart .DescentChart.total = chooseTotal boundarySign
  chart .DescentChart.boundary = FromMarkedTotal.boundary markedTotal

private
  module Actual = Assemble (raw a★) (raw-base a★) (raw-r a★) (raw-j-projects a★)

open Actual public using (raw-j²; chooseTotal; chooseBase; choose-r; choose-j²; markedTotal)

descentChart : DescentChart
descentChart = Actual.chart
