{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.HomologyDimension where

-- Homology vanishing above the finite-dimensional bound, using a finite
-- subcomplex rather than a connected cell normal form.
open import DeloopS3.Bridge.Recognition.Notation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order using (_<_ ; _≤_)
open import Cubical.Data.Nat.Order.Inductive using
  (_≟ᵗ_ ; lt ; eq ; gt ; <ᵗ-asym)
open import Cubical.Data.Fin using (Fin ; ¬Fin0)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.CW.Base using
  (CWskel ; finCWskel ; finCWskel→CWskel ; realise)
open import Cubical.CW.Properties using (realiseFin)
open import Cubical.CW.Subcomplex using (subComplex ; realiseSubComplex)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ ; CW-AugChainComplex)
open import Cubical.Algebra.AbGroup.Base using (AbGroupStr)
open import Cubical.Algebra.Group.Base using (GroupStr)
open import Cubical.Algebra.ChainComplex.Base using (ChainComplex)
open import Cubical.Algebra.ChainComplex.Homology using (homology)
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT

private
  zero-chain-homology : (C : ChainComplex ℓ-zero) (k : ℕ)
    → isContr (fst (ChainComplex.chain C (suc k)))
    → isContr (fst (homology k C))
  zero-chain-homology C k zeroChain = GroupStr.1g (snd (homology k C)) ,
    SQ.elimProp (λ _ → GroupStr.is-set (snd (homology k C)) _ _)
      (λ z → cong SQ.[_] (Σ≡Prop
        (λ _ → AbGroupStr.is-set (snd (ChainComplex.chain C k)) _ _)
        (isContr→isProp zeroChain _ (fst z))))

  zero-cells-homology : (C : CWskel ℓ-zero) (k : ℕ)
    → C .snd .fst k ≡ 0 → isContr (fst (H̃ˢᵏᵉˡ C k))
  zero-cells-homology C k noCells = zero-chain-homology (CW-AugChainComplex C) k
    (subst (λ r → isContr (Fin r → ℤ)) (sym noCells)
      ((λ _ → pos 0) , λ f → funExt λ x → Empty.rec (¬Fin0 x)))

  subcomplex-no-cells : (C : CWskel ℓ-zero) (d k : ℕ)
    → d ≤ k → subComplex C d .snd .fst k ≡ 0
  subcomplex-no-cells C d k dk with k ≟ᵗ d
  ... | lt kd = Empty.rec (<ᵗ-asym kd dk)
  ... | eq _ = refl
  ... | gt _ = refl

finite≤-homology-above : (X : CW₀) (d k : ℕ)
  → Finite≤ d (fst X) → d < k → Hzero X k
finite≤-homology-above X d k fin dk = PT.rec isPropIsContr compute fin
  where
  compute : (Σ[ C ∈ finCWskel ℓ-zero (suc d) ]
    (fst X ≃ realise (finCWskel→CWskel (suc d) C))) → Hzero X k
  compute (C , e) =
    subst (λ cw → Hzero (fst X , cw) k)
      (PT.squash₁ PT.∣ subComplex K (suc d) , e' ∣₁ (snd X))
      (zero-cells-homology (subComplex K (suc d)) k
        (subcomplex-no-cells K (suc d) k dk))
    where
    K = finCWskel→CWskel (suc d) C
    e' : fst X ≃ realise (subComplex K (suc d))
    e' = compEquiv e (compEquiv (invEquiv (isoToEquiv (realiseFin (suc d) C)))
      (isoToEquiv (realiseSubComplex (suc d) K)))
