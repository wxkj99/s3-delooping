{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Kernel where

-- Contractibility criteria from null localization units and local cofibre maps.
open import DeloopS3.Local.Base public
open import DeloopS3.Local.Powers public
open import DeloopS3.Local.Cofibre public
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.Pushout.Base using (cofib ; inl)
open import DeloopS3.Local.Unique using (module Unique)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquivCong)
import Cubical.HITs.PropositionalTruncation as PT

-- A1. The forward function is literally restriction along the unit.
preη-isEquiv : ∀ {m E Z} → Local m Z
  → isEquiv (λ (f : L m E → Z) → f ∘ η)
preη-isEquiv = Unique.isEquiv-preη

unit-null→contr : ∀ {m E} → MerelyNull (η {m} {E})
  → isContr (L m E)
unit-null→contr {m} {E} = PT.rec isPropIsContr contract
  where
  Y = L m E
  restriction : (Y → Y) ≃ (E → Y)
  restriction = (λ f → f ∘ η) , preη-isEquiv (local-L m E)

  contract : Σ[ y ∈ Y ] (η ≡ (λ _ → y)) → isContr Y
  contract (y , h) = y , λ z → sym (funExt⁻ lifted z)
    where
    lifted : idfun Y ≡ (λ _ → y)
    lifted = invEq (_ , isEquivCong restriction) h

-- A3. Test the local equivalence against the localized cofibre itself.
-- Its unit is null by the mapping-space fibre calculation; A1 contracts it.
local-cofib-contr : ∀ {m A B} (f : A → B)
  → LocalEquiv m f → isContr (L m (cofib f))
local-cofib-contr {m} f localEquiv = unit-null→contr
  PT.∣ η (inl tt) , cofib-map-null f
    (localEquiv (L m (cofib f)) (local-L m (cofib f))) η ∣₁
