{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Packaging.Homology where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)
open import Cubical.Data.Fin.Base using (flast ; injectSuc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.ChainComplex
open import Cubical.CW.Approximation
open import Cubical.CW.Homology.Base
open import Cubical.HITs.SequentialColimit using (→FinSeqColimHomotopy)
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CellularPushout.Cellular
open import DeloopS3.Bridge.CellularPushout.Algebra
open import DeloopS3.Bridge.DMCExactness.Maps using (augmentMap)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀)

open ChainComplexMap

realisedCW : CWskel ℓ-zero → CW₀
realisedCW X = realise X , PT.∣ X , idEquiv (realise X) ∣₁

-- The two presentations have the same fields, including augmentation.
cellular-chain : {X Y : CWskel ℓ-zero} → cellMap X Y
  → ChainComplexMap (CW-AugChainComplex X) (CW-AugChainComplex Y)
chainmap (cellular-chain h) zero = idGroupHom
chainmap (cellular-chain h) (suc n) = cellular-coefficients h n
bdrycomm (cellular-chain h) zero = cellular-augmentation h
  ∙ sym (compGroupHomId (augmentation.ϵ _))
bdrycomm (cellular-chain h) (suc n) = cellular-boundary h n

presentation-map : (X : CWskel ℓ-zero)
  → ChainComplexMap (augment (CW-augmented X)) (CW-AugChainComplex X)
chainmap (presentation-map X) zero = idGroupHom
chainmap (presentation-map X) (suc n) = idGroupHom
bdrycomm (presentation-map X) zero = GroupHom≡ refl
bdrycomm (presentation-map X) (suc n) = GroupHom≡ refl

presentation-equiv : (X : CWskel ℓ-zero)
  → augment (CW-augmented X) ≃Chain CW-AugChainComplex X
fst (presentation-equiv X) = presentation-map X
snd (presentation-equiv X) zero = snd (idEquiv _)
snd (presentation-equiv X) (suc n) = snd (idEquiv _)

abstract
  presentation-natural : {X Y : CWskel ℓ-zero} (h : cellMap X Y)
    → compChainMap (augmentMap (cellular-augmented-map h)) (presentation-map Y)
     ≡ compChainMap (presentation-map X) (cellular-chain h)
  presentation-natural h = ChainComplexMap≡ λ
    { zero → GroupHom≡ refl ; (suc n) → GroupHom≡ refl }

cellular-realisation-approx : {X Y : CWskel ℓ-zero} (h : cellMap X Y) (n : ℕ)
  → finCellApprox X Y (realiseCellMap h) (suc n)
fst (cellular-realisation-approx h n) = restrictCell h (suc n)
snd (cellular-realisation-approx h n) = →FinSeqColimHomotopy _ _ (λ _ → refl)

abstract
  cellular-homology-window : {X Y : CWskel ℓ-zero} (h : cellMap X Y) (n : ℕ)
    → finCellMap→HomologyMap n (restrictCell h (suc (suc (suc n))))
     ≡ chainComplexMap→HomologyMap (cellular-chain h) n
  cellular-homology-window {Y = Y} h n = GroupHom≡
    (funExt (SQ.elimProp (λ _ → GroupStr.is-set (snd (H̃ˢᵏᵉˡ Y n)) _ _)
      (λ a → cong SQ.[_] (Σ≡Prop
        (λ _ → AbGroupStr.is-set (snd (ChainComplex.chain (CW-AugChainComplex Y) n)) _ _)
        (funExt⁻ (cong fst (cellular-coefficients-window h (suc (suc n)) n _)) (fst a))))))

  cellular-homology-β : {X Y : CWskel ℓ-zero} (h : cellMap X Y) (n : ℕ)
    → H̃ˢᵏᵉˡ→ {C = X} {D = Y} n (realiseCellMap h)
     ≡ chainComplexMap→HomologyMap (cellular-chain h) n
  cellular-homology-β {X} {Y} h n =
    H̃ˢᵏᵉˡ→β X Y n (cellular-realisation-approx h (suc (suc n)))
    ∙ cellular-homology-window h n

  approximation-homology-β : {X Y : CWskel ℓ-zero}
    (h : cellMap X Y) (u : realise X → realise Y) (n : ℕ)
    (a : finCellApprox X Y u (suc (suc (suc n))))
    → fst a ≡ restrictCell h (suc (suc (suc n)))
    → H̃ˢᵏᵉˡ→ {C = X} {D = Y} n u
     ≡ chainComplexMap→HomologyMap (cellular-chain h) n
  approximation-homology-β {X} {Y} h u n a p =
    H̃ˢᵏᵉˡ→β X Y n a ∙ cong (finCellMap→HomologyMap n) p
    ∙ cellular-homology-window h n

-- Functoriality with explicitly fixed chain endpoints avoids normalizing
-- cellular approximation while elaborating a naturality square.
abstract
  homology-square : {W X Y Z : ChainComplex ℓ-zero}
    (u : ChainComplexMap W X) (v : ChainComplexMap X Z)
    (s : ChainComplexMap W Y) (t : ChainComplexMap Y Z)
    → compChainMap u v ≡ compChainMap s t
    → (n : ℕ) (x : fst (homology n W))
    → fst (chainComplexMap→HomologyMap v n)
        (fst (chainComplexMap→HomologyMap u n) x)
     ≡ fst (chainComplexMap→HomologyMap t n)
        (fst (chainComplexMap→HomologyMap s n) x)
  homology-square u v s t p n = funExt⁻ (cong fst
    (sym (chainComplexMap→HomologyMapComp u v n)
      ∙ cong (λ h → chainComplexMap→HomologyMap h n) p
      ∙ chainComplexMap→HomologyMapComp s t n))
