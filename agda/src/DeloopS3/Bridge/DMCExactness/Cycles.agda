{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Cycles where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CellularPushout.Algebra
open import DeloopS3.Bridge.DMCExactness.Quotient
open import DeloopS3.Bridge.DMCExactness.Maps

open ChainComplex
open IsGroupHom
private variable ℓ : Level

module CycleAdjustments {E : AbGroup ℓ} (A B C : Augmented E)
  (f : AugmentedMap A B) (g : AugmentedMap A C) where
  open ConeMaps A B C f g

  abstract
    b-equation : (n : ℕ) (z : HD.Cycle (suc n))
      → BG._+_ n (fst (bdry bC n) (fst (fst z)))
          (fst (F n) (snd (snd (fst z)))) ≡ BG.0g n
    b-equation zero z = cong fst (snd z)
    b-equation (suc n) z = cong fst (snd z)

    c-equation : (n : ℕ) (z : HD.Cycle (suc n))
      → CG._+_ n (fst (bdry cC n) (fst (snd (fst z))))
          (CG.-_ n (fst (G n) (snd (snd (fst z))))) ≡ CG.0g n
    c-equation zero z = cong snd (snd z)
    c-equation (suc n) z = cong (fst ∘ snd) (snd z)

  -- First cycle adjustment: a zero source coordinate splits the cycle
  -- into two vertex cycles. No witness has been chosen from a truncation.
  splitB : (n : ℕ) (z : HD.Cycle (suc n))
    → snd (snd (fst z)) ≡ AG.0g n → HB.Cycle (suc n)
  splitB n z p = fst (fst z) ,
    sym (plusHomZero (F n) _)
      ∙ cong (λ a → BG._+_ n (fst (bdry bC n) (fst (fst z))) (fst (F n) a)) (sym p)
      ∙ b-equation n z

  splitC : (n : ℕ) (z : HD.Cycle (suc n))
    → snd (snd (fst z)) ≡ AG.0g n → HC.Cycle (suc n)
  splitC n z p = fst (snd (fst z)) ,
    sym (minusHomZero (G n) _)
      ∙ cong (λ a → CG._+_ n (fst (bdry cC n) (fst (snd (fst z)))) (CG.-_ n (fst (G n) a))) (sym p)
      ∙ c-equation n z

  abstract
    split-image : (n : ℕ) (z : HD.Cycle (suc n))
      (p : snd (snd (fst z)) ≡ AG.0g n)
      → fst (sumH (suc n)) (HB.class (suc n) (splitB n z p) , HC.class (suc n) (splitC n z p))
       ≡ HD.class (suc n) z
    split-image n z p = sumH-β (suc n) (splitB n z p) (splitC n z p) ∙ HD.class-path (suc n)
      (embedCycle-coordinates (suc n) (splitB n z p) (splitC n z p)
        ∙ ΣPathP (refl , ΣPathP (refl , sym p)))

  sourceChain : (n : ℕ) → fst (chain aC n) → fst (chain D (suc (suc n)))
  sourceChain n a = BG.0g (suc n) , CG.0g (suc n) , a

  adjusted : (n : ℕ) (z : HD.Cycle (suc n)) (v : fst (chain aC (suc n)))
    → HD.Cycle (suc n)
  adjusted n z v = GroupStr._·_ (snd (HD.Z (suc n))) z
    (HD.boundary (suc n) (sourceChain (suc n) v))

  abstract
    adjusted-projection : (n : ℕ) (z : HD.Cycle (suc n)) (v : fst (chain aC (suc n)))
      → fst (bdry aC n) v ≡ snd (snd (fst z))
      → snd (snd (fst (adjusted n z v))) ≡ AG.0g n
    adjusted-projection n z v p =
      cong (AG._+_ n (snd (snd (fst z)))) (cong (AG.-_ n) p) ∙ AG.+InvR n _

    adjusted-class : (n : ℕ) (z : HD.Cycle (suc n)) (v : fst (chain aC (suc n)))
      → HD.class (suc n) (adjusted n z v) ≡ HD.class (suc n) z
    adjusted-class n z v = cong (HD.H._·_ (suc n) (HD.class (suc n) z))
      (HD.boundary-zero (suc n) (sourceChain (suc n) v)) ∙ HD.H.·IdR (suc n) _

    total-kernel-cycle : (n : ℕ) (z : HD.Cycle (suc n))
      → fst (δ n) (HD.class (suc n) z) ≡ HA.H.1g n
      → PT.∥ Σ[ h ∈ fst (target (suc n)) ]
          fst (sumH (suc n)) h ≡ HD.class (suc n) z ∥₁
    total-kernel-cycle n z p = PT.map (λ { (v , q) →
      (HB.class (suc n) (splitB n (adjusted n z v) (adjusted-projection n z v q)) ,
       HC.class (suc n) (splitC n (adjusted n z v) (adjusted-projection n z v q))) ,
      split-image n (adjusted n z v) (adjusted-projection n z v q) ∙ adjusted-class n z v })
      (HA.zero→boundary n (fst (projection n) z) p)

    total-composite-cycle : (n : ℕ) (b : HB.Cycle (suc n)) (c : HC.Cycle (suc n))
      → fst (δ n) (fst (sumH (suc n)) (HB.class (suc n) b , HC.class (suc n) c))
       ≡ HA.H.1g n
    total-composite-cycle n b c = cong (fst (δ n)) (sumH-β (suc n) b c)
      ∙ HA.class-path n (cong (snd ∘ snd) (embedCycle-coordinates (suc n) b c))

  -- Second adjustment: representatives of the two zero target classes
  -- give a cycle (-v,-w,a), with d v=f a and d w=-g a.
  abstract
    lift-equation : {X Y : AbGroup ℓ} (d : AbGroupHom X Y)
      (v : fst X) (y : fst Y) → fst d v ≡ y
      → AbGroupStr._+_ (snd Y) (fst d (AbGroupStr.-_ (snd X) v)) y
       ≡ AbGroupStr.0g (snd Y)
    lift-equation {Y = Y} d v y p =
      cong (λ z → AbGroupStr._+_ (snd Y) z y)
        (presinv (snd d) v ∙ cong (AbGroupStr.-_ (snd Y)) p)
      ∙ AbGroupStr.+InvL (snd Y) y

  liftCycle : (n : ℕ) (a : HA.Cycle n)
    (v : fst (chain bC (suc n))) (w : fst (chain cC (suc n)))
    → fst (bdry bC n) v ≡ fst (F n) (fst a)
    → fst (bdry cC n) w ≡ CG.-_ n (fst (G n) (fst a))
    → HD.Cycle (suc n)
  liftCycle zero a v w p q = (BG.-_ 1 v , CG.-_ 1 w , fst a) ,
    ΣPathP (lift-equation (bdry bC 0) v _ p , lift-equation (bdry cC 0) w _ q)
  liftCycle (suc n) a v w p q = (BG.-_ (suc (suc n)) v , CG.-_ (suc (suc n)) w , fst a) ,
    ΣPathP (lift-equation (bdry bC (suc n)) v _ p ,
      ΣPathP (lift-equation (bdry cC (suc n)) w _ q , Laws.neg-of-zero (chain aC n) (snd a)))

  abstract
    lift-projects : (n : ℕ) (a : HA.Cycle n)
      (v : fst (chain bC (suc n))) (w : fst (chain cC (suc n)))
      (p : fst (bdry bC n) v ≡ fst (F n) (fst a))
      (q : fst (bdry cC n) w ≡ CG.-_ n (fst (G n) (fst a)))
      → fst (δ n) (HD.class (suc n) (liftCycle n a v w p q)) ≡ HA.class n a
    lift-projects zero a v w p q = HA.class-path 0 refl
    lift-projects (suc n) a v w p q = HA.class-path (suc n) refl

    source-kernel-cycle : (n : ℕ) (a : HA.Cycle n)
      → fst (spanH n) (HA.class n a) ≡ AbGroupStr.0g (snd (target n))
      → PT.∥ Σ[ z ∈ fst (HD.H (suc n)) ] fst (δ n) z ≡ HA.class n a ∥₁
    source-kernel-cycle n a p = PT.rec PT.isPropPropTrunc (λ { (v , q) →
      PT.map (λ { (w , r) → HD.class (suc n) (liftCycle n a v w q r) , lift-projects n a v w q r })
        (HC.zero→boundary n (minusGCycle n a) (cong snd (sym (spanH-β n a) ∙ p))) })
      (HB.zero→boundary n (fCycle n a) (cong fst (sym (spanH-β n a) ∙ p)))

    source-composite-cycle : (n : ℕ) (z : HD.Cycle (suc n))
      → fst (spanH n) (fst (δ n) (HD.class (suc n) z))
       ≡ AbGroupStr.0g (snd (target n))
    source-composite-cycle n z = spanH-β n (fst (projection n) z) ∙ ΣPathP
      (HB.boundary→zero n (fCycle n (fst (projection n) z)) (BG.-_ (suc n) (fst (fst z)))
        (presinv (snd (bdry bC n)) _ ∙ sym (Laws.sum-right-zero (chain bC n) (b-equation n z))) ,
       HC.boundary→zero n (minusGCycle n (fst (projection n) z)) (CG.-_ (suc n) (fst (snd (fst z))))
        (presinv (snd (bdry cC n)) _ ∙ sym (Laws.sum-right-zero (chain cC n) (c-equation n z))))

  -- Third adjustment: the source coordinate accompanying a cone
  -- boundary of vertex cycles is itself a source cycle. At degree zero
  -- this uses the augmentation square, not a nonexistent third coordinate.
  targetSource : (n : ℕ) (b : HB.Cycle n) (c : HC.Cycle n)
    (t : fst (chain D (suc (suc n))))
    → fst (bdry D (suc n)) t ≡ embed n (fst b) (fst c)
    → HA.Cycle n
  targetSource zero b c (v , w , a) p = a ,
    sym (augmentation-source v a) ∙ cong (fst (ε B)) (cong fst p) ∙ snd b
  targetSource (suc n) b c (v , w , a) p = a ,
    Laws.neg-zero (chain aC n) (cong (snd ∘ snd) p)

  abstract
    target-b-equation : (n : ℕ) (b : HB.Cycle n) (c : HC.Cycle n)
      (t : fst (chain D (suc (suc n))))
      → fst (bdry D (suc n)) t ≡ embed n (fst b) (fst c)
      → BG._+_ n (fst (bdry bC n) (fst t)) (fst (F n) (snd (snd t))) ≡ fst b
    target-b-equation zero b c t p = cong fst p
    target-b-equation (suc n) b c t p = cong fst p

    target-c-equation : (n : ℕ) (b : HB.Cycle n) (c : HC.Cycle n)
      (t : fst (chain D (suc (suc n))))
      → fst (bdry D (suc n)) t ≡ embed n (fst b) (fst c)
      → CG._+_ n (fst (bdry cC n) (fst (snd t)))
          (CG.-_ n (fst (G n) (snd (snd t)))) ≡ fst c
    target-c-equation zero b c t p = cong snd p
    target-c-equation (suc n) b c t p = cong (fst ∘ snd) p

    targetSource-coordinate : (n : ℕ) (b : HB.Cycle n) (c : HC.Cycle n)
      (t : fst (chain D (suc (suc n))))
      (p : fst (bdry D (suc n)) t ≡ embed n (fst b) (fst c))
      → fst (targetSource n b c t p) ≡ snd (snd t)
    targetSource-coordinate zero b c t p = refl
    targetSource-coordinate (suc n) b c t p = refl

    target-witness-path : (n : ℕ) (b : HB.Cycle n) (c : HC.Cycle n)
      (t : fst (chain D (suc (suc n))))
      (p : fst (bdry D (suc n)) t ≡ embed n (fst b) (fst c))
      → fst (spanH n) (HA.class n (targetSource n b c t p))
       ≡ (HB.class n b , HC.class n c)
    target-witness-path n b c t p = spanH-β n a ∙ ΣPathP
      (HB.boundary-add-path n (fCycle n a) b (fst t)
        (cong (BG._+_ n (fst (bdry bC n) (fst t)))
           (cong (fst (F n)) (targetSource-coordinate n b c t p))
         ∙ target-b-equation n b c t p) ,
       HC.boundary-add-path n (minusGCycle n a) c (fst (snd t))
        (cong (CG._+_ n (fst (bdry cC n) (fst (snd t))))
           (cong (CG.-_ n ∘ fst (G n)) (targetSource-coordinate n b c t p))
         ∙ target-c-equation n b c t p))
      where
      a : HA.Cycle n
      a = targetSource n b c t p

    target-kernel-cycle : (n : ℕ) (b : HB.Cycle n) (c : HC.Cycle n)
      → fst (sumH n) (HB.class n b , HC.class n c) ≡ HD.H.1g n
      → PT.∥ Σ[ a ∈ fst (HA.H n) ] fst (spanH n) a ≡ (HB.class n b , HC.class n c) ∥₁
    target-kernel-cycle n b c p = PT.map (λ { (t , q) →
      HA.class n (targetSource n b c t (q ∙ embedCycle-coordinates n b c)) ,
      target-witness-path n b c t (q ∙ embedCycle-coordinates n b c) })
      (HD.zero→boundary n (embedCycle n b c) (sym (sumH-β n b c) ∙ p))

    source-boundary : (n : ℕ) (a : HA.Cycle n)
      → fst (bdry D (suc n)) (sourceChain n (fst a))
       ≡ embed n (fst (F n) (fst a)) (CG.-_ n (fst (G n) (fst a)))
    source-boundary zero a = ΣPathP
      (cong (λ z → BG._+_ 0 z (fst (F 0) (fst a))) (pres1 (snd (bdry bC 0))) ∙ BG.+IdL 0 _ ,
       cong (λ z → CG._+_ 0 z (CG.-_ 0 (fst (G 0) (fst a)))) (pres1 (snd (bdry cC 0))) ∙ CG.+IdL 0 _)
    source-boundary (suc n) a = ΣPathP
      (cong (λ z → BG._+_ (suc n) z (fst (F (suc n)) (fst a))) (pres1 (snd (bdry bC (suc n)))) ∙ BG.+IdL (suc n) _ ,
       ΣPathP
        (cong (λ z → CG._+_ (suc n) z (CG.-_ (suc n) (fst (G (suc n)) (fst a))))
           (pres1 (snd (bdry cC (suc n)))) ∙ CG.+IdL (suc n) _ ,
         Laws.neg-of-zero (chain aC n) (snd a)))

    target-composite-cycle : (n : ℕ) (a : HA.Cycle n)
      → fst (sumH n) (fst (spanH n) (HA.class n a)) ≡ HD.H.1g n
    target-composite-cycle n a = cong (fst (sumH n)) (spanH-β n a)
      ∙ sumH-β n (fCycle n a) (minusGCycle n a)
      ∙ HD.boundary→zero n (embedCycle n (fCycle n a) (minusGCycle n a))
        (sourceChain n (fst a))
        (source-boundary n a ∙ sym (embedCycle-coordinates n (fCycle n a) (minusGCycle n a)))
