{-# OPTIONS --safe --cubical #-}

-- The complete mapping-data form of the Nielsen equivalence, including the 2-cell.
module DeloopS3.Seifert.MarkedSeifert.WEquiv.NielsenMapping where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Data.Sigma
open import DeloopS3.Move.CancelLoopCell using (powerEquiv; Sign; minus)
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (W)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Edge using (module Mapping)

module MappingJR {ℓ : Level} (X : Type ℓ) where
  JRData : Type ℓ
  JRData = Σ[ a ∈ X ] Σ[ j ∈ (a ≡ a) ] Σ[ r ∈ (a ≡ a) ]
    (j ∙ j ≡ (j ∙ sym r) ∙ (j ∙ sym r))

  -- The graph formulas proved by the two actual R1s in Nielsen.agda.
  -- Reindex the ENTIRE relation type, not just its inhabitation.
  abstract
    changeGenerators : Mapping.RelationData X ≃ JRData
    changeGenerators = Σ-cong-equiv-snd λ a → Σ-cong-equiv-snd λ j →
      invEquiv (Σ-cong-equiv-fst
        {B = λ y → j ∙ j ≡ y ∙ y}
        (compEquiv (powerEquiv a minus) (compPathlEquiv j)))

    WMappingJR : (W → X) ≃ JRData
    WMappingJR = compEquiv (Mapping.WMapping X) changeGenerators
