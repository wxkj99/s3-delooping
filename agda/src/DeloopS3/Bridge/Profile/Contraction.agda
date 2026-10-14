{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.Contraction where

-- Homology profiles imply localized contraction. O is recognized as a Moore space;
-- for I, the cofibre of a chosen bottom representative is recognized, retaining the attachment.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_ ; invEquiv ; compEquiv)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.HITs.Pushout.Base using (cofib)
open import Cubical.Homotopy.Connected using (isConnected)
import Cubical.HITs.PropositionalTruncation as PT

open import DeloopS3.Bridge.Recognition.Notation using
  (CW₀ ; Finite≤ ; Hzero ; Hiso ; H̃ᶜʷ)
open import DeloopS3.Bridge.Recognition.Models using (bottomCW)
open import DeloopS3.Bridge.Recognition.Hurewicz using (hurewicz-raise)
open import DeloopS3.Bridge.MooreMarked using (bottom-representative)
open import DeloopS3.Bridge.Profile.Types using (OProfile ; IProfile)
open import DeloopS3.Bridge.Profile.MooreRecognition using (recognize-moore3)
open import DeloopS3.Bridge.Profile.BottomCofibre using
  (bottom-cofibCW ; bottom-cofib-profile)
open import DeloopS3.Local.Base using (L)
open import DeloopS3.Local.EO using
  (E_O ; E_O≃cofibre ; EO-model-contraction)
open import DeloopS3.Local.EI using
  (Moore ; BottomMoore ; TopMoore ; EI-from-merely-bottom-cofibre)

abstract
  O-profile-equivalence : (X : CW₀) → OProfile X
    → PT.∥ fst X ≃ E_O ∥₁
  O-profile-equivalence X p =
    PT.map {A = fst X ≃ Moore 3 2} {B = fst X ≃ E_O}
      (λ e → compEquiv e model)
      (recognize-moore3 3 (2 , refl) X (OProfile.finite p)
        connected (OProfile.H₃ p) (OProfile.H₄-zero p))
    where
    connected : isConnected 4 (fst X)
    connected = hurewicz-raise X 0 (OProfile.simple p) (OProfile.H₂-zero p)

    model : Moore 3 2 ≃ E_O
    model = invEquiv E_O≃cofibre

  O-profile-contraction : (X : CW₀) → OProfile X → isContr (L 3 (fst X))
  O-profile-contraction X p =
    EO-model-contraction {E = fst X} (O-profile-equivalence X p)

  I-profile-bottom-cofibre : (X : CW₀) → IProfile X
    → PT.∥ Σ[ a ∈ (BottomMoore → fst X) ] (cofib a ≃ TopMoore) ∥₁
  I-profile-bottom-cofibre X p =
    PT.rec
      {A = Σ[ a ∈ (BottomMoore → fst X) ] Hiso bottomCW X 2 a}
      {P = PT.∥ Σ[ a ∈ (BottomMoore → fst X) ] (cofib a ≃ TopMoore) ∥₁}
      PT.squash₁ from-bottom
      (bottom-representative X (IProfile.simple p) (IProfile.H₂ p))
    where
    from-bottom : (Σ[ a ∈ (BottomMoore → fst X) ] Hiso bottomCW X 2 a)
      → PT.∥ Σ[ a ∈ (BottomMoore → fst X) ] (cofib a ≃ TopMoore) ∥₁
    from-bottom (a , isoH) =
      PT.rec
        {A = Finite≤ 4 (cofib a)
          × isConnected 4 (cofib a)
          × GroupEquiv (H̃ᶜʷ F 3) (ℤGroup/ 10)
          × Hzero F 4}
        {P = PT.∥ Σ[ b ∈ (BottomMoore → fst X) ] (cofib b ≃ TopMoore) ∥₁}
        PT.squash₁ from-profile (bottom-cofib-profile X p a isoH)
      where
      -- This CW witness has the literal underlying type cofib a.
      F : CW₀
      F = bottom-cofibCW X (IProfile.finite p) a

      from-profile : Finite≤ 4 (cofib a)
        × isConnected 4 (cofib a)
        × GroupEquiv (H̃ᶜʷ F 3) (ℤGroup/ 10)
        × Hzero F 4
        → PT.∥ Σ[ b ∈ (BottomMoore → fst X) ] (cofib b ≃ TopMoore) ∥₁
      from-profile (finF , connF , coordinates , zeroF) =
        PT.map
          {A = cofib a ≃ TopMoore}
          {B = Σ[ b ∈ (BottomMoore → fst X) ] (cofib b ≃ TopMoore)}
          (λ e → a , e)
          (recognize-moore3 10 (9 , refl) F finF connF coordinates zeroF)

  I-profile-contraction : (X : CW₀) → IProfile X → isContr (L 10 (fst X))
  I-profile-contraction X p =
    EI-from-merely-bottom-cofibre {E = fst X} (I-profile-bottom-cofibre X p)
