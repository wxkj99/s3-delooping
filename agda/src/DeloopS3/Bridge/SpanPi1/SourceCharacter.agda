{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.SourceCharacter where

-- The inversion pair is built on the actual filled circle bundle, then
-- transported as one structure to the literal cover. No action of
-- sourceCoverEquiv on a named target loop is computed or assumed.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (pos)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
import Cubical.HITs.PropositionalTruncation as PT
import DeloopS3.Cert.Input.Model as Model
import DeloopS3.Bridge.OriginalSpan as OS
import DeloopS3.Seifert.MarkedSeifert.FinalDone as Final
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
open import DeloopS3.Bridge.SpanPi1.Seam using (Π)
open import DeloopS3.Bridge.SpanPi1.Coordinates using (K; a₀; qCover; qCoverπ)
open import DeloopS3.Bridge.SpanPi1.Character using (KleinCharacter; C₂)
open import DeloopS3.Bridge.SpanPi1.SourceCharacter.Transport
  using (Everywhere; pullback; module AllFilled)

abstract
  cover-to-bundle : (c : ShortCase)
    → Model.A_G c ≃ Final.Bundle.Mₑ (pos (OS.e c))
  cover-to-bundle c = compEquiv
    {A = Model.A_G c} {B = OS.A c} {C = Final.Bundle.Mₑ (pos (OS.e c))}
    (invEquiv (OS.sourceCoverEquiv c)) (Final.M22e≃Mₑ (pos (OS.e c)))

  cover-projection : (c : ShortCase)
    → Final.Bundle.pₑ (pos (OS.e c)) ∘ fst (cover-to-bundle c) ≡ qCover c
  cover-projection c = funExt λ a →
    sym (OS.projectionPath c (invEq (OS.sourceCoverEquiv c) a))

  cover-character-at-every-point : (c : ShortCase)
    → Everywhere (Model.A_G c) (qCover c)
  cover-character-at-every-point c = subst (Everywhere (Model.A_G c)) (cover-projection c)
    (pullback (cover-to-bundle c) (Final.Bundle.pₑ (pos (OS.e c)))
      (AllFilled.bundle-character (pos (OS.e c))))

  source-character : (c : ShortCase)
    (rp : GroupEquiv (Π OS.R (qCover c (a₀ c))) C₂)
    → PT.∥ KleinCharacter (K c) (qCoverπ c rp) ∥₁
  source-character c = cover-character-at-every-point c (a₀ c)
