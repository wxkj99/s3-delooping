{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.EMEncode where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.HITs.EilenbergMacLane1.Base
import Cubical.HITs.SetTruncation as ST
import DeloopS3.Cover.Cosets as Cosets
open import DeloopS3.Bridge.SpanPi1.Seam using (Π)

module Encode {ℓ} (H : Group ℓ) where
  encode : fst (Π (EM₁ H) embase) → fst H
  encode = ST.rec (GroupStr.is-set (snd H)) (Cosets.loopCode H)

  abstract
    encode-comp : (s t : Path (EM₁ H) embase embase)
      → Cosets.loopCode H (s ∙ t)
        ≡ GroupStr._·_ (snd H) (Cosets.loopCode H s) (Cosets.loopCode H t)
    encode-comp s t = cong (Cosets.loopCode H)
      (cong₂ _∙_ (sym (Cosets.loop-codeLoop H s)) (sym (Cosets.loop-codeLoop H t))
        ∙ sym (emloop-comp H (Cosets.loopCode H s) (Cosets.loopCode H t)))
      ∙ Cosets.loopCode-loop H _

    encodeHom : GroupHom (Π (EM₁ H) embase) H
    encodeHom = encode , makeIsGroupHom
      (ST.elim2 (λ _ _ → isProp→isSet (GroupStr.is-set (snd H) _ _)) encode-comp)

    encodeHom-loop : (l : Path (EM₁ H) embase embase)
      → fst encodeHom ST.∣ l ∣₂ ≡ Cosets.loopCode H l
    encodeHom-loop l = refl

    encodeHom-emloop : (d : fst H) → fst encodeHom ST.∣ emloop d ∣₂ ≡ d
    encodeHom-emloop = Cosets.loopCode-loop H

open Encode public
