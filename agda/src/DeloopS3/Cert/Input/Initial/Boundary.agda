{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Boundary where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Nat using (ℕ; zero; suc; _<ᵇ_; _≡ᵇ_; _·_)
open import Cubical.Data.Bool using (true; false≢true; _and_)
import Cubical.Data.Empty as Empty
import Cubical.Data.SumFin as SF
open import DeloopS3.Cert.Input.Graph.Base
open import DeloopS3.Cert.Input.Graph.Maps using (collapse)
open import DeloopS3.Cert.Input.Initial.Walk
open import DeloopS3.Cert.Input.LocalCharts.Charts using (startSheet; startSheet-value)
open import DeloopS3.Cert.Interpret.Syntax using
  (and-left; and-right; all-sound; at-member; natEq-sound; wordEq-sound; RawChecks)
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P

repeatWord : ℕ → List BaseLetter → List BaseLetter
repeatWord zero w = []
repeatWord (suc n) w = w P.++ repeatWord n w

abstract
  wire-append : (v w : List BaseLetter)
    → wireWord (v P.++ w) ≡ wireWord v P.++ wireWord w
  wire-append [] w = refl
  wire-append (t ∷ ts) w = cong (wireLetter t ∷_) (wire-append ts w)

  wire-repeat : (n : ℕ) (w : List BaseLetter)
    → wireWord (repeatWord n w)
      ≡ P.concatMap (λ v → v) (P.replicate n (wireWord w))
  wire-repeat zero w = refl
  wire-repeat (suc n) w = wire-append w (repeatWord n w)
    ∙ cong (wireWord w P.++_) (wire-repeat n w)

  boundary-checked : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → Ch.checkBoundary (certOf c) (bdAllAt c b) ≡ true
  boundary-checked octa b = all-sound (Ch.checkBoundary (certOf octa))
    (RawChecks.boundaries-ok (rawChecks octa)) (at-member (Ch.boundaries (certOf octa)) b)
  boundary-checked icosa b = all-sound (Ch.checkBoundary (certOf icosa))
    (RawChecks.boundaries-ok (rawChecks icosa)) (at-member (Ch.boundaries (certOf icosa)) b)

  nonempty-default : (xs : List ℕ) (d e : ℕ)
    → (0 <ᵇ P.length xs) ≡ true → P.nth d xs 0 ≡ P.nth e xs 0
  nonempty-default [] d e p = Empty.rec (false≢true p)
  nonempty-default (x ∷ xs) d e p = refl

-- Extract the literal checker result, rather than normalizing the
-- concrete boundary words, including their negative letters.
module Reflected (ct : Ch.Certificate) (bd : Ch.Boundary)
  (ok : Ch.checkBoundary ct bd ≡ true) where
  start : ℕ
  start = P.nth (Ch.index ct) (Ch.orbit bd) 0
  input : P.Word
  input = P.concatMap (λ w → w) (P.replicate (Ch.orbitLength bd) (Ch.kindWord (Ch.kind bd)))
  result : P.Pair ℕ P.Word
  result = Ch.liftWord ct start input

  abstract
    nonempty : (0 <ᵇ P.length (Ch.orbit bd)) ≡ true
    nonempty = and-left ok
    endpoint : P.fst result ≡ start
    endpoint = natEq-sound _ _ (and-left tail)
      where
      tail : ((P.fst result ≡ᵇ start) and
        (P.wordEq (P.snd result) (Ch.boundaryWord bd) and
        (P.wordValid (suc (Ch.index ct)) (Ch.boundaryWord bd) and
        (P.tableEq (Ch.conjugate (Ch.rep ct start) (P.power (Ch.degree ct) (Ch.kindGenerator ct (Ch.kind bd)) (Ch.orbitLength bd))) (Ch.mark bd) and
         P.tableEq (Ch.mark bd) (P.evaluate (Ch.degree ct) (Ch.boundaryWord bd) (Ch.images ct)))))) ≡ true
      tail = and-right {a = P.zEq (Ch.hPower bd) (P.pos 0)}
        (and-right {a = P.zEq (Ch.weight bd) (Ch.kindWeight ct (Ch.kind bd))}
        (and-right {a = (Ch.orbitLength bd · Ch.order bd ≡ᵇ P.nth 0 (Ch.orders ct) (Ch.kindIndex (Ch.kind bd)))}
        (and-right {a = (P.length (Ch.orbit bd) ≡ᵇ Ch.orbitLength bd)}
        (and-right {a = P.tableEq (P.map (λ i → P.fst (Ch.liftWord ct i (Ch.kindWord (Ch.kind bd)))) (Ch.orbit bd)) (Ch.rotate (Ch.orbit bd))}
        (and-right {a = P.all (λ i → i <ᵇ Ch.index ct) (Ch.orbit bd)}
        (and-right {a = 0 <ᵇ P.length (Ch.orbit bd)} ok))))))

    word : P.snd result ≡ Ch.boundaryWord bd
    word = wordEq-sound _ _ (and-left
      (and-right {a = P.fst result ≡ᵇ start}
      (and-right {a = P.zEq (Ch.hPower bd) (P.pos 0)}
      (and-right {a = P.zEq (Ch.weight bd) (Ch.kindWeight ct (Ch.kind bd))}
      (and-right {a = (Ch.orbitLength bd · Ch.order bd ≡ᵇ P.nth 0 (Ch.orders ct) (Ch.kindIndex (Ch.kind bd)))}
      (and-right {a = (P.length (Ch.orbit bd) ≡ᵇ Ch.orbitLength bd)}
      (and-right {a = P.tableEq (P.map (λ i → P.fst (Ch.liftWord ct i (Ch.kindWord (Ch.kind bd)))) (Ch.orbit bd)) (Ch.rotate (Ch.orbit bd))}
      (and-right {a = P.all (λ i → i <ᵇ Ch.index ct) (Ch.orbit bd)}
      (and-right {a = 0 <ᵇ P.length (Ch.orbit bd)} ok)))))))))

boundaryWalkWord : (c : ShortCase) → R.FaceIx (S₀ c) → List BaseLetter
boundaryWalkWord c b = repeatWord (Ch.orbitLength (bdAllAt c b)) (baseWord (Ch.kind (bdAllAt c b)))

module CheckedBoundary (c : ShortCase) (b : R.FaceIx (S₀ c)) where
  private
    bd : Ch.Boundary
    bd = bdAllAt c b
    module Check = Reflected (certOf c) bd (boundary-checked c b)
  abstract
    start-checked : SF.toℕ (startSheet c b) ≡ Check.start
    start-checked = startSheet-value c b
      ∙ nonempty-default (Ch.orbit bd) 0 (Ch.index (certOf c)) Check.nonempty

    input-checked : wireWord (boundaryWalkWord c b) ≡ Check.input
    input-checked = wire-repeat (Ch.orbitLength bd) (baseWord (Ch.kind bd))
      ∙ cong (λ w → P.concatMap (λ v → v) (P.replicate (Ch.orbitLength bd) w)) (baseWord-wire (Ch.kind bd))

    result-checked : Ch.liftWord (certOf c) (SF.toℕ (startSheet c b)) (wireWord (boundaryWalkWord c b)) ≡ Check.result
    result-checked = cong₂ (Ch.liftWord (certOf c)) start-checked input-checked

    closed : walk c (startSheet c b) (boundaryWalkWord c b) ≡ startSheet c b
    closed = SF.toℕ-injective (walk-endpoint c (startSheet c b) (boundaryWalkWord c b)
      ∙ cong P.fst result-checked ∙ Check.endpoint ∙ sym start-checked)

    word-checked : P.snd (Ch.liftWord (certOf c) (SF.toℕ (startSheet c b)) (wireWord (boundaryWalkWord c b))) ≡ Ch.boundaryWord bd
    word-checked = cong P.snd result-checked ∙ Check.word

boundaryLoop : (c : ShortCase) (b : R.FaceIx (S₀ c))
  → Path (LiftedGraph c) (vertex (startSheet c b)) (vertex (startSheet c b))
boundaryLoop c b = walkPath c (startSheet c b) (boundaryWalkWord c b)
  ∙ cong vertex (CheckedBoundary.closed c b)

abstract
  collapse-boundaryLoop : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → cong (collapse c) (boundaryLoop c b)
      ≡ R.roseWord (gs c) (Ch.boundaryWord (bdAllAt c b))
  collapse-boundaryLoop c b = cong-∙ (collapse c)
      (walkPath c (startSheet c b) (boundaryWalkWord c b)) (cong vertex (CheckedBoundary.closed c b))
    ∙ sym (rUnit (cong (collapse c) (walkPath c (startSheet c b) (boundaryWalkWord c b))))
    ∙ lUnit (cong (collapse c) (walkPath c (startSheet c b) (boundaryWalkWord c b)))
    ∙ sym (liftAcc-sound c (startSheet c b) (boundaryWalkWord c b) [])
    ∙ cong (R.roseWord (gs c)) (CheckedBoundary.word-checked c b)
