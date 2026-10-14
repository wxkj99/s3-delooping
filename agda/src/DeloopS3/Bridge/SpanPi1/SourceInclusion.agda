{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.SourceInclusion where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (isoToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (addIso; commₖ)
open import Cubical.Homotopy.Connected
  using (isConnectedFun; isConnectedRetractFromIso; inlConnected)
open import Cubical.Homotopy.Group.Base using (πHom)
open import Cubical.Homotopy.Group.Properties using (connectedFun→πSurj)
open import Cubical.HITs.Pushout.Base using (inl; inr)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²; mulC; _+C_)
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (row)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Basis using (mulC-one)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus using (Kinv; kbase)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.TorusMap using (λ₂)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third using (Fill)
import DeloopS3.Seifert.MarkedSeifert.TorusFilling.FilledLoops as Filled
open import DeloopS3.Bridge.SpanPi1.Connected using (circle-connected)
open import DeloopS3.Bridge.SpanPi1.Seam using (Π)

module Row (e : ℤ) where
  abstract
    slice-equivalence : (u : C) → isEquiv (λ t → row e (pos 1) (u , t))
    slice-equivalence u = subst isEquiv
      (funExt (λ t → sym (cong (mulC e u +C_) (mulC-one t)
        ∙ commₖ {G = ℤAbGroup} 1 (mulC e u) t)))
      (isoToEquiv (addIso {G = ℤAbGroup} 1 (mulC e u)) .snd)

    fibre-circle : (b : C) → fiber (row e (pos 1)) b ≃ C
    fibre-circle b = compEquiv Σ-assoc-≃
      (Σ-contractSnd (λ u → equiv-proof (slice-equivalence u) b))

    connected : isConnectedFun 2 (row e (pos 1))
    connected b = isConnectedRetractFromIso 2 (equivToIso (fibre-circle b)) circle-connected

fill-inclusion : (e : ℤ) → Kinv → Fill e
fill-inclusion e = inl

abstract
  fill-inclusion-connected : (e : ℤ) → isConnectedFun 2 (fill-inclusion e)
  fill-inclusion-connected e = inlConnected 2 λ₂ (row e (pos 1)) (Row.connected e)

  fill-inclusion-π-surjective : (e : ℤ) (a : Kinv)
    → (u : fst (Π (Fill e) (fill-inclusion e a)))
    → PT.∥ fiber (fst (πHom 0 (fill-inclusion e , refl))) u ∥₁
  fill-inclusion-π-surjective e a = connectedFun→πSurj 0
    (fill-inclusion e , refl) (fill-inclusion-connected e)

  filled-inclusion-π-surjective : (e : ℤ)
    → (u : fst (Π (Fill e) (inr 0C)))
    → PT.∥ fiber (fst (πHom 0 (fill-inclusion e , Filled.Filling.seam e))) u ∥₁
  filled-inclusion-π-surjective e = connectedFun→πSurj 0
    (fill-inclusion e , Filled.Filling.seam e) (fill-inclusion-connected e)
