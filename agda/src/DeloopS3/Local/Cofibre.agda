{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Cofibre where

-- Maps out of a cofibre are a family of fibres of
-- precomposition. Contracting those fibres makes every map constant.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquivCong)
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.Pushout.Base using (cofib ; inl ; inr ; push)

cofib-maps-Iso : {A B Z : Type} (f : A → B)
  → Iso (cofib f → Z)
    (Σ[ z ∈ Z ] fiber (λ (g : B → Z) → g ∘ f) (λ _ → z))
Iso.fun (cofib-maps-Iso f) h = h (inl tt) , h ∘ inr ,
  (λ i a → h (push a (~ i)))
Iso.inv (cofib-maps-Iso f) (z , g , p) (inl tt) = z
Iso.inv (cofib-maps-Iso f) (z , g , p) (inr b) = g b
Iso.inv (cofib-maps-Iso f) (z , g , p) (push a i) = p (~ i) a
Iso.sec (cofib-maps-Iso f) (z , g , p) = refl
Iso.ret (cofib-maps-Iso f) h = funExt λ
  { (inl tt) → refl ; (inr b) → refl ; (push a i) → refl }

cofib-map-null : {A B Z : Type} (f : A → B)
  → isEquiv (λ (g : B → Z) → g ∘ f)
  → (h : cofib f → Z) → h ≡ (λ _ → h (inl tt))
cofib-map-null {Z = Z} f preEquiv h =
  invEq (_ , isEquivCong mapsEquiv) (ΣPathP (refl , fibrePath))
  where
  mapsEquiv = isoToEquiv (cofib-maps-Iso {Z = Z} f)
  z = h (inl tt)

  fibrePath : snd (fst mapsEquiv h) ≡ snd (fst mapsEquiv (λ _ → z))
  fibrePath = isContr→isProp (equiv-proof preEquiv (λ _ → z))
    (snd (fst mapsEquiv h)) (snd (fst mapsEquiv (λ _ → z)))

cofib-const-isEquiv : {A B Z : Type} (f : A → B)
  → isEquiv (λ (g : B → Z) → g ∘ f)
  → isEquiv (λ (z : Z) (_ : cofib f) → z)
cofib-const-isEquiv f preEquiv = isoToIsEquiv
  (iso (λ z _ → z) (λ h → h (inl tt))
    (λ h → sym (cofib-map-null f preEquiv h)) (λ _ → refl))
