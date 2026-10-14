{-# OPTIONS --safe --cubical #-}

-- Edge comparison on all mapping types, not π₁.
module DeloopS3.Seifert.MarkedSeifert.WEquiv.Edge where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPathrEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (pos)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop-comp)
open import DeloopS3.Move.CancelMinimal using (C; mulC)
open import DeloopS3.Move.CancelLoopCell using (module CircleUP; module PushoutUP)
open import DeloopS3.Cover.Orientation.CircleModel using (circleToC; S¹≃C)
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (W)

double : S¹ → S¹
double base = base
double (loop i) = (loop ∙ loop) i

WHit : Type₀
WHit = Pushout double double

private
  doubleTriangle : (s : S¹) → circleToC (double s) ≡ mulC (pos 2) (circleToC s)
  doubleTriangle base = refl
  doubleTriangle (loop i) k = (cong-∙ circleToC loop loop
    ∙ sym (emloop-comp ℤGroup (pos 1) (pos 1))) k i

abstract
  circleModel : WHit ≃ W
  circleModel = pushoutEquiv double double (mulC (pos 2)) (mulC (pos 2))
    S¹≃C S¹≃C S¹≃C (funExt doubleTriangle) (funExt doubleTriangle)

-- Horizontal loops, repeated vertical edge. Nothing is truncated.
LoopSquare : {ℓ : Level} {X : Type ℓ} {a b : X}
  → a ≡ a → b ≡ b → a ≡ b → Type ℓ
LoopSquare p q γ = PathP (λ i → p i ≡ q i) γ γ

abstract
  squareAtRefl : {ℓ : Level} {X : Type ℓ} {a : X}
    (p q : a ≡ a) → LoopSquare p q refl ≃ (p ≡ q)
  squareAtRefl p q = isoToEquiv (iso (λ s j i → s i j)
    (λ s i j → s j i) (λ _ → refl) (λ _ → refl))

  equalityToRelator : {ℓ : Level} {X : Type ℓ} {a : X}
    (p q : a ≡ a) → (p ≡ q) ≃ (p ∙ sym q ≡ refl)
  equalityToRelator p q = compEquiv (congEquiv (compPathrEquiv (sym q)))
    (compPathrEquiv (rCancel q))

module Mapping {ℓ : Level} (X : Type ℓ) where
  Loops : Type ℓ
  Loops = Σ[ a ∈ X ] (a ≡ a)

  WithEdge : Type ℓ
  WithEdge = Σ[ ax ∈ Loops ] Σ[ by ∈ Loops ]
    Σ[ γ ∈ (ax .fst ≡ by .fst) ]
      LoopSquare (ax .snd ∙ ax .snd) (by .snd ∙ by .snd) γ

  RelationData : Type ℓ
  RelationData = Σ[ a ∈ X ] Σ[ x ∈ (a ≡ a) ] Σ[ y ∈ (a ≡ a) ]
    (x ∙ x ≡ y ∙ y)

  private
    seamEquiv : (f g : S¹ → X)
      → ((s : S¹) → f (double s) ≡ g (double s))
      ≃ (Σ[ γ ∈ (f base ≡ g base) ]
        LoopSquare (cong f loop ∙ cong f loop) (cong g loop ∙ cong g loop) γ)
    seamEquiv f g = compEquiv
      (CircleUP.circleUP (λ s → f (double s) ≡ g (double s)))
      (Σ-cong-equiv-snd λ γ → pathToEquiv λ k →
        LoopSquare (cong-∙ f loop loop k) (cong-∙ g loop loop k) γ)

    coconeToEdge : PushoutUP.Cocone double double X ≃ WithEdge
    coconeToEdge = Σ-cong-equiv (CircleUP.circleUP (λ _ → X)) λ f →
      Σ-cong-equiv (CircleUP.circleUP (λ _ → X)) λ g → seamEquiv f g

    EdgeFirst : Type ℓ
    EdgeFirst = Σ[ a ∈ X ] Σ[ x ∈ (a ≡ a) ]
      Σ[ bγ ∈ (Σ[ b ∈ X ] (a ≡ b)) ] Σ[ y ∈ (bγ .fst ≡ bγ .fst) ]
        LoopSquare (x ∙ x) (y ∙ y) (bγ .snd)

    reorder : WithEdge ≃ EdgeFirst
    reorder = isoToEquiv (iso
      (λ { ((a , x) , (b , y) , γ , s) → a , x , (b , γ) , y , s })
      (λ { (a , x , (b , γ) , y , s) → (a , x) , (b , y) , γ , s })
      (λ _ → refl) (λ _ → refl))

    eliminateSingleton : EdgeFirst ≃ RelationData
    eliminateSingleton = Σ-cong-equiv-snd λ a → Σ-cong-equiv-snd λ x →
      compEquiv (Σ-contractFst (isContrSingl a))
        (Σ-cong-equiv-snd λ y → isoToEquiv
          (iso (λ s j i → s i j) (λ s i j → s j i)
            (λ _ → refl) (λ _ → refl)))

    rawMapping : (WHit → X) ≃ RelationData
    rawMapping = compEquiv (PushoutUP.pushoutUP double double X)
      (compEquiv coconeToEdge (compEquiv reorder eliminateSingleton))

  -- Transparent computational maps for later HIT-recursion comparisons.
  -- Their inverse laws (and the public equivalence) stay abstract.
  hitEncode : (WHit → X) → RelationData
  hitEncode = rawMapping .fst
  hitDecode : RelationData → WHit → X
  hitDecode = invEq rawMapping

  abstract
    hitEncodeDecode : (d : RelationData) → hitEncode (hitDecode d) ≡ d
    hitEncodeDecode = secEq rawMapping
    hitDecodeEncode : (f : WHit → X) → hitDecode (hitEncode f) ≡ f
    hitDecodeEncode = retEq rawMapping

  abstract
    hitWithEdge : (WHit → X) ≃ WithEdge
    hitWithEdge = compEquiv (PushoutUP.pushoutUP double double X) coconeToEdge

    removeConnectingEdge : WithEdge ≃ RelationData
    removeConnectingEdge = compEquiv reorder eliminateSingleton

    hitMapping : (WHit → X) ≃ RelationData
    hitMapping = compEquiv hitWithEdge removeConnectingEdge

    WMapping : (W → X) ≃ RelationData
    WMapping = compEquiv (preCompEquiv {C = X} circleModel) hitMapping

-- The loop based at the first vertex uses the connecting path.  This is
-- the transport occurring in the singleton elimination above.
abstract
  transportBasedLoop : {ℓ : Level} {X : Type ℓ} {a b : X}
    (γ : a ≡ b) (y : b ≡ b)
    → transport (λ i → γ (~ i) ≡ γ (~ i)) y ≡ (γ ∙ y) ∙ sym γ
  transportBasedLoop {a = a} γ = J
    (λ b γ → (y : b ≡ b) → transport (λ i → γ (~ i) ≡ γ (~ i)) y
      ≡ (γ ∙ y) ∙ sym γ)
    (λ y → transportRefl y ∙ lUnit y ∙ rUnit (refl ∙ y)) γ
