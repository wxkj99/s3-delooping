{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.Profile.Assembly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (_≃_)
open import Cubical.Foundations.Pointed using (Pointed; typ; _≃∙_)
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.Homotopy.Connected using (isConnected)
open import Cubical.Homotopy.Loopspace using (Ω)
import Cubical.HITs.PropositionalTruncation as PT

open import DeloopS3.Local.Base using (L)
open import DeloopS3.Bridge.Profile.Facts using
  (ProfileFacts; XO; XI; octa; icosa)
open import DeloopS3.Bridge.Profile.Types using (OProfile; IProfile)
open import DeloopS3.Bridge.Profile.Outer using (outer-profiles)
open import DeloopS3.Bridge.Profile.Contraction using
  (O-profile-contraction; I-profile-contraction)
open import DeloopS3.Assembly.Final using (EO; EI; HomologyProfileInput)
open import DeloopS3.Assembly.LocalizationMaps using (L-equiv)
open import DeloopS3.Assembly.SimpleFromPi1 using (X≃E; Deloop-final″)

private
  abstract
    L-contr-equiv : (m : ℕ) (X Y : Type)
      → isContr (L m X) → X ≃ Y → isContr (L m Y)
    L-contr-equiv m X Y h e =
      subst {A = Type} {x = L m X} {y = L m Y}
        (λ Z → isContr Z) (ua (L-equiv m {A = X} {B = Y} e)) h

  abstract
    facts-contrO : ProfileFacts → isContr (L 3 (fst XO))
    facts-contrO f =
      PT.rec {A = OProfile XO × IProfile XI}
        {P = isContr (L 3 (fst XO))}
        (isPropIsContr {A = L 3 (fst XO)})
        (λ p → O-profile-contraction XO (fst p)) (outer-profiles f)

    facts-contrI : ProfileFacts → isContr (L 10 (fst XI))
    facts-contrI f =
      PT.rec {A = OProfile XO × IProfile XI}
        {P = isContr (L 10 (fst XI))}
        (isPropIsContr {A = L 10 (fst XI)})
        (λ p → I-profile-contraction XI (snd p)) (outer-profiles f)

-- Both truncation eliminations land in contraction propositions,
-- never in the final delooping Σ-type.
abstract
  profileFacts→HomologyProfileInput
    : PT.∥ ProfileFacts ∥₁ → HomologyProfileInput
  HomologyProfileInput.contrO (profileFacts→HomologyProfileInput facts) =
    L-contr-equiv 3 (fst XO) EO
      (PT.rec {A = ProfileFacts} {P = isContr (L 3 (fst XO))}
        (isPropIsContr {A = L 3 (fst XO)}) facts-contrO facts)
      (X≃E octa)
  HomologyProfileInput.contrI (profileFacts→HomologyProfileInput facts) =
    L-contr-equiv 10 (fst XI) EI
      (PT.rec {A = ProfileFacts} {P = isContr (L 10 (fst XI))}
        (isPropIsContr {A = L 10 (fst XI)}) facts-contrI facts)
      (X≃E icosa)

  Deloop-final-from-facts : PT.∥ ProfileFacts ∥₁
    → Σ[ B ∈ Pointed ℓ-zero ]
        (isConnected 2 (typ B) × (Ω B ≃∙ (S₊ 3 , north)))
  Deloop-final-from-facts facts =
    Deloop-final″ (profileFacts→HomologyProfileInput facts)
