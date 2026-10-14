{-# OPTIONS --safe --cubical #-}

-- Nielsen change of coordinates via two R1 cancellations.
module DeloopS3.Seifert.MarkedSeifert.WEquiv.Nielsen where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Move.CancelLoopCell
open import DeloopS3.Move.CancelGeneral using (module ReplaceLeft)

-- Specify the solved loop explicitly while reusing the R1 proof.
-- The cofiber seam below retains the entire proof of the loop equation.
module ExplicitR1 {ℓ : Level} (Q : Type ℓ) (q : Q)
  (L R s : q ≡ q) (solved : (L ∙ s) ∙ R ≡ refl) where
  module P = PrimitiveCancellation Q q L R plus
  graph : AddLoop Q q → Q
  graph (incQ z) = z
  graph (x i) = s i
  cell : cong graph P.w ≡ refl
  cell = P.map-word graph ∙ solved
  retractMap : P.V → Q
  retractMap (inl z) = graph z
  retractMap (inr tt) = q
  retractMap (push base i) = q
  retractMap (push (loop k) i) = cell i k
  abstract
    cancellation : P.V ≃ Q
    cancellation = retractMap , precomposesToId→Equiv
      retractMap P.j refl P.primitive-cancel
    inclusion : Q ≃ P.V
    inclusion = P.jEquiv
    inclusion-map : inclusion .fst ≡ P.j
    inclusion-map = refl
    cancellation-map : cancellation .fst ≡ retractMap
    cancellation-map = refl
    canonical-agrees : P.r ≡ retractMap
    canonical-agrees = invEq
      (congEquiv {x = P.r} {y = retractMap} (P.restrictionEquiv Q)) P.rj

Gxy : Type₀
Gxy = AddLoop S¹ base
qxy : Gxy
qxy = incQ base
xLoop yLoop : qxy ≡ qxy
xLoop = cong (incQ {Q = S¹} {q = base}) loop
yLoop = x

Gjr : Type₀
Gjr = AddLoop S¹ base
qjr : Gjr
qjr = incQ base
jLoop rLoop : qjr ≡ qjr
jLoop = cong (incQ {Q = S¹} {q = base}) loop
rLoop = x

module First = ExplicitR1 Gxy qxy yLoop (sym xLoop)
  (sym yLoop ∙ xLoop) (solve-plus yLoop (sym xLoop))

private
  secondSolution : (sym refl ∙ sym (rLoop ∙ sym jLoop)) ≡ jLoop ∙ sym rLoop
  secondSolution = sym (lUnit (sym (rLoop ∙ sym jLoop)))
    ∙ symDistr rLoop (sym jLoop)
  secondSolved : (refl ∙ (jLoop ∙ sym rLoop)) ∙ (rLoop ∙ sym jLoop) ≡ refl
  secondSolved = cong (λ z → (refl ∙ z) ∙ (rLoop ∙ sym jLoop)) (sym secondSolution)
    ∙ solve-plus refl (rLoop ∙ sym jLoop)

module Second = ExplicitR1 Gjr qjr refl (rLoop ∙ sym jLoop)
  (jLoop ∙ sym rLoop) secondSolved

-- Free three-loop regrouping. This is the constructor-level realization
-- of the permutation of independent Σ coordinates in AddLoopUP.
A B : Type₀
A = AddLoop Gxy qxy
B = AddLoop Gjr qjr

permute : A → B
permute (incQ (incQ s)) = incQ (incQ s)
permute (incQ (x i)) = x i
permute (x i) = incQ (x i)

unpermute : B → A
unpermute (incQ (incQ s)) = incQ (incQ s)
unpermute (incQ (x i)) = x i
unpermute (x i) = incQ (x i)

private
  permute-sec : (z : B) → permute (unpermute z) ≡ z
  permute-sec (incQ (incQ s)) = refl
  permute-sec (incQ (x i)) = refl
  permute-sec (x i) = refl
  permute-ret : (z : A) → unpermute (permute z) ≡ z
  permute-ret (incQ (incQ s)) = refl
  permute-ret (incQ (x i)) = refl
  permute-ret (x i) = refl

abstract
  regroup : A ≃ B
  regroup = isoToEquiv (iso permute unpermute permute-sec permute-ret)
  regroup-map : regroup .fst ≡ permute
  regroup-map = refl

private
  inc : Gjr → B
  inc = incQ
  yB : Path B (inc qjr) (inc qjr)
  yB = x
  rB jB : Path B (inc qjr) (inc qjr)
  rB = cong inc rLoop
  jB = cong inc jLoop

  reassociate : cong permute First.P.w ≡ Second.P.w
  reassociate = cong-∙ permute (cong incQ yLoop ∙ x) (cong incQ (sym xLoop))
    ∙ cong (_∙ sym jB) (cong-∙ permute (cong incQ yLoop) x)
    ∙ sym (assoc yB rB (sym jB))
    ∙ cong (_∙ (rB ∙ sym jB)) (lUnit yB)
    ∙ cong ((refl ∙ yB) ∙_) (sym (cong-∙ inc rLoop (sym jLoop)))

  relatorTriangle : (z : S¹)
    → regroup .fst (circleMap First.P.w z) ≡ circleMap Second.P.w z
  relatorTriangle z = funExt⁻ regroup-map (circleMap First.P.w z) ∙ step z
    where
    step : (z : S¹) → permute (circleMap First.P.w z) ≡ circleMap Second.P.w z
    step base = refl
    step (loop i) k = reassociate k i

abstract
  relator-change : (z : S¹)
    → regroup .fst (circleMap First.P.w z) ≡ circleMap Second.P.w z
  relator-change = relatorTriangle

  -- Same N, with its primitive relation reassociated as a path of maps.
  regroupN : First.P.V ≃ Second.P.V
  regroupN = pushoutEquiv (circleMap First.P.w) (λ _ → tt)
    (circleMap Second.P.w) (λ _ → tt)
    (idEquiv S¹) regroup (idEquiv Unit) (funExt relatorTriangle) refl

  regroupN-graph : (z : A) → regroupN .fst (inl z) ≡ inl (permute z)
  regroupN-graph z = cong (inl {f = circleMap Second.P.w} {g = λ _ → tt})
    (funExt⁻ regroup-map z)

  -- First R1 inverted, graph regrouping, second R1 forward.
  nielsen : Gxy ≃ Gjr
  nielsen = compEquiv First.inclusion (compEquiv regroupN Second.cancellation)

forward : Gxy → Gjr
forward (incQ s) = incQ s
forward (x i) = (jLoop ∙ sym rLoop) i

backward : Gjr → Gxy
backward (incQ s) = incQ s
backward (x i) = (sym yLoop ∙ xLoop) i

abstract
  nielsen-map : nielsen .fst ≡ forward
  nielsen-map = funExt λ z →
    cong (λ n → Second.cancellation .fst (regroupN .fst n))
      (funExt⁻ First.inclusion-map z)
    ∙ cong (Second.cancellation .fst) (regroupN-graph (incQ z))
    ∙ funExt⁻ Second.cancellation-map (inl (permute (incQ z)))
    ∙ step z
    where
    step : (z : Gxy) → Second.retractMap (inl (permute (incQ z))) ≡ forward z
    step (incQ s) = refl
    step (x i) = refl

-- Generator formulas are paths in the actual untruncated graph.
forward-x : cong forward xLoop ≡ jLoop
forward-x = refl
forward-y : cong forward yLoop ≡ jLoop ∙ sym rLoop
forward-y = refl
backward-j : cong backward jLoop ≡ xLoop
backward-j = refl
backward-r : cong backward rLoop ≡ sym yLoop ∙ xLoop
backward-r = refl

private
  cancel-j : {ℓ : Level} {X : Type ℓ} {a : X} (p q : a ≡ a)
    → p ∙ (sym p ∙ q) ≡ q
  cancel-j p q = assoc p (sym p) q
    ∙ cong (_∙ q) (rCancel p) ∙ sym (lUnit q)
  cancel-r : {ℓ : Level} {X : Type ℓ} {a : X} (p q : a ≡ a)
    → (p ∙ sym q) ∙ q ≡ p
  cancel-r p q = sym (assoc p (sym q) q)
    ∙ cong (p ∙_) (lCancel q) ∙ sym (rUnit p)

  forward-backward : (z : Gjr) → forward (backward z) ≡ z
  forward-backward (incQ s) = refl
  forward-backward (x i) k =
    (cong-∙ forward (sym yLoop) xLoop
      ∙ cong (_∙ jLoop) (symDistr jLoop (sym rLoop))
      ∙ cancel-r rLoop jLoop) k i

  backward-forward : (z : Gxy) → backward (forward z) ≡ z
  backward-forward (incQ s) = refl
  backward-forward (x i) k =
    (cong-∙ backward jLoop (sym rLoop)
      ∙ cong (xLoop ∙_) (symDistr (sym yLoop) xLoop)
      ∙ cancel-j xLoop yLoop) k i

abstract
  inverse-formula : invEq nielsen ≡ backward
  inverse-formula = funExt λ z →
    cong (invEq nielsen)
      (sym (funExt⁻ nielsen-map (backward z) ∙ forward-backward z))
    ∙ retEq nielsen (backward z)
