{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.FiniteCoproductCoordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma
import Cubical.Data.SumFin as SF
import Cubical.Data.Empty as Empty
import Cubical.Data.Sum as Sum
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.AbGroup
open import Cubical.CW.Base using (hasCWskel)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→Equiv ; H̃ᶜʷ→comp)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; H̃ᶜʷ→ ; Finite≤)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map-agrees)
open import DeloopS3.Bridge.Profile.BaseSeifert.Coproduct
import DeloopS3.Bridge.DegreeSpan.Pieces as Pieces
open import DeloopS3.Bridge.DegreeSpan.FiniteCoproductGroups

open IsGroupHom

-- The actual CW endpoints are parameters. In particular, this does not
-- identify two chosen CW witnesses by definitional equality.
module Split (X Y S : CW₀) (chart : fst S ≃ (fst X Sum.⊎ fst Y))
  (finX : Finite≤ 2 (fst X)) (finY : Finite≤ 2 (fst Y))
  (d : ℕ) (bound : d < 4) where
  module C = Coproduct X Y S chart 2 2 finX finY
  split : GroupEquiv (H̃ᶜʷ S (suc d)) (DirProd (H̃ᶜʷ X (suc d)) (H̃ᶜʷ Y (suc d)))
  split = invGroupEquiv (C.sum-equiv d bound)

  abstract
    left-β : (x : fst (H̃ᶜʷ X (suc d)))
      → equivFun (fst split) (fst (H̃ᶜʷ→ {C = X} {D = S} (suc d) C.left) x)
        ≡ (x , GroupStr.1g (snd (H̃ᶜʷ Y (suc d))))
    left-β x = cong (equivFun (fst split)) (sym p)
      ∙ retEq (fst (C.sum-equiv d bound)) (x , GroupStr.1g (snd (H̃ᶜʷ Y (suc d))))
      where
      p : equivFun (fst (C.sum-equiv d bound)) (x , GroupStr.1g (snd (H̃ᶜʷ Y (suc d))))
        ≡ fst (H̃ᶜʷ→ {C = X} {D = S} (suc d) C.left) x
      p = C.sum-equiv-eval d bound x (GroupStr.1g (snd (H̃ᶜʷ Y (suc d))))
        ∙ cong₂ (GroupStr._·_ (snd (H̃ᶜʷ S (suc d))))
            (cong (λ h → fst h x) (cellular-map-agrees X S (suc d) C.left))
            (cong (λ h → fst h (GroupStr.1g (snd (H̃ᶜʷ Y (suc d)))))
              (cellular-map-agrees Y S (suc d) C.right)
              ∙ pres1 (snd (H̃ᶜʷ→ {C = Y} {D = S} (suc d) C.right)))
        ∙ GroupStr.·IdR (snd (H̃ᶜʷ S (suc d))) _

    right-β : (y : fst (H̃ᶜʷ Y (suc d)))
      → equivFun (fst split) (fst (H̃ᶜʷ→ {C = Y} {D = S} (suc d) C.right) y)
        ≡ (GroupStr.1g (snd (H̃ᶜʷ X (suc d))) , y)
    right-β y = cong (equivFun (fst split)) (sym p)
      ∙ retEq (fst (C.sum-equiv d bound)) (GroupStr.1g (snd (H̃ᶜʷ X (suc d))) , y)
      where
      p : equivFun (fst (C.sum-equiv d bound)) (GroupStr.1g (snd (H̃ᶜʷ X (suc d))) , y)
        ≡ fst (H̃ᶜʷ→ {C = Y} {D = S} (suc d) C.right) y
      p = C.sum-equiv-eval d bound (GroupStr.1g (snd (H̃ᶜʷ X (suc d)))) y
        ∙ cong₂ (GroupStr._·_ (snd (H̃ᶜʷ S (suc d))))
            (cong (λ h → fst h (GroupStr.1g (snd (H̃ᶜʷ X (suc d)))))
              (cellular-map-agrees X S (suc d) C.left)
              ∙ pres1 (snd (H̃ᶜʷ→ {C = X} {D = S} (suc d) C.left)))
            (cong (λ h → fst h y) (cellular-map-agrees Y S (suc d) C.right))
        ∙ GroupStr.·IdL (snd (H̃ᶜʷ S (suc d))) _

module Coordinates (X : CW₀) (model : hasCWskel (fst X))
  (finX : Finite≤ 2 (fst X)) (d : ℕ) (bound : d < 4)
  (G : AbGroup ℓ-zero) (coordinate : GroupEquiv (H̃ᶜʷ X (suc d)) (AbGroup→Group G)) where
  module V = Vectors G

  copies : ℕ → CW₀
  copies n = (SF.Fin n × fst X) , PT.∣ Pieces.copies-model n model ∣₁

  sum-chart : (n : ℕ) (S : CW₀) (chart : fst S ≃ (SF.Fin (suc n) × fst X))
    → fst S ≃ (fst X Sum.⊎ fst (copies n))
  sum-chart n S chart = isoToEquiv
    (compIso (equivToIso chart) (Pieces.split-product-iso n (fst X)))

  module Step (n : ℕ) (S : CW₀) (chart : fst S ≃ (SF.Fin (suc n) × fst X)) =
    Split X (copies n) S (sum-chart n S chart) finX (Pieces.copies2-finite n finX) d bound

  coord : (n : ℕ) (S : CW₀) → fst S ≃ (SF.Fin n × fst X)
    → GroupEquiv (H̃ᶜʷ S (suc d)) (V.V n)
  coord zero S chart = compGroupEquiv
    (H̃ᶜʷ→Equiv {C = S} {D = emptyCW} (suc d)
      (compEquiv chart (isoToEquiv (Pieces.empty-product-iso (fst X)))))
    (V.empty-equiv (H̃ᶜʷ emptyCW (suc d)) (empty-H-zero (suc d)))
  coord (suc n) S chart = compGroupEquiv (Step.split n S chart)
    (compGroupEquiv (product-equiv coordinate (coord n (copies n) (idEquiv _))) (V.split n))

  inclusion : {n : ℕ} (S : CW₀) (chart : fst S ≃ (SF.Fin n × fst X))
    → SF.Fin n → fst X → fst S
  inclusion S chart i x = invEq chart (i , x)

  abstract
    inclusion-β : (n : ℕ) (S : CW₀) (chart : fst S ≃ (SF.Fin n × fst X))
      (i : SF.Fin n) (z : fst (H̃ᶜʷ X (suc d)))
      → equivFun (fst (coord n S chart))
          (fst (H̃ᶜʷ→ {C = X} {D = S} (suc d) (inclusion S chart i)) z)
        ≡ V.point i (equivFun (fst coordinate) z)
    inclusion-β zero S chart () z
    inclusion-β (suc n) S chart SF.fzero z =
      cong (λ p → V.join (equivFun (fst coordinate) (fst p) ,
        equivFun (fst (coord n (copies n) (idEquiv _))) (snd p)))
        (Step.left-β n S chart z)
      ∙ cong (λ y → V.join (equivFun (fst coordinate) z , y))
          (pres1 (snd (coord n (copies n) (idEquiv _))))
      ∙ funExt λ { SF.fzero → refl ; (SF.fsuc j) → refl }
    inclusion-β (suc n) S chart (SF.fsuc i) z =
      cong (equivFun (fst (coord (suc n) S chart)))
        (cong (λ h → fst h z) (H̃ᶜʷ→comp {C = X} {D = copies n} {E = S} (suc d)
          (Step.C.right n S chart) (inclusion (copies n) (idEquiv _) i)))
      ∙ cong (λ p → V.join (equivFun (fst coordinate) (fst p) ,
          equivFun (fst (coord n (copies n) (idEquiv _))) (snd p)))
          (Step.right-β n S chart
            (fst (H̃ᶜʷ→ {C = X} {D = copies n} (suc d) (inclusion (copies n) (idEquiv _) i)) z))
      ∙ cong₂ (λ a v → V.join (a , v)) (pres1 (snd coordinate))
          (inclusion-β n (copies n) (idEquiv _) i z)
      ∙ funExt λ { SF.fzero → refl ; (SF.fsuc j) → refl }

    inclusion-inverse-β : (n : ℕ) (S : CW₀) (chart : fst S ≃ (SF.Fin n × fst X))
      (i : SF.Fin n) (a : fst G)
      → invEq (fst (coord n S chart)) (V.point i a)
        ≡ fst (H̃ᶜʷ→ {C = X} {D = S} (suc d) (inclusion S chart i))
            (invEq (fst coordinate) a)
    inclusion-inverse-β n S chart i a =
      cong (invEq (fst (coord n S chart)))
        (sym (inclusion-β n S chart i (invEq (fst coordinate) a)
          ∙ cong (V.point i) (secEq (fst coordinate) a)))
      ∙ retEq (fst (coord n S chart))
          (fst (H̃ᶜʷ→ {C = X} {D = S} (suc d) (inclusion S chart i))
            (invEq (fst coordinate) a))

    hom-ext : (n : ℕ) (S : CW₀) (chart : fst S ≃ (SF.Fin n × fst X))
      {H : Group₀} (f g : GroupHom (H̃ᶜʷ S (suc d)) H)
      → ((i : SF.Fin n) (z : fst (H̃ᶜʷ X (suc d)))
        → fst f (fst (H̃ᶜʷ→ {C = X} {D = S} (suc d) (inclusion S chart i)) z)
          ≡ fst g (fst (H̃ᶜʷ→ {C = X} {D = S} (suc d) (inclusion S chart i)) z))
      → (z : fst (H̃ᶜʷ S (suc d))) → fst f z ≡ fst g z
    hom-ext n S chart f g p z =
      cong (fst f) (sym (retEq (fst (coord n S chart)) z))
      ∙ V.hom-ext n
          (compGroupHom (GroupEquiv→GroupHom (invGroupEquiv (coord n S chart))) f)
          (compGroupHom (GroupEquiv→GroupHom (invGroupEquiv (coord n S chart))) g)
          (λ i a → cong (fst f) (inclusion-inverse-β n S chart i a)
            ∙ p i (invEq (fst coordinate) a)
            ∙ cong (fst g) (sym (inclusion-inverse-β n S chart i a)))
          (equivFun (fst (coord n S chart)) z)
      ∙ cong (fst g) (retEq (fst (coord n S chart)) z)
