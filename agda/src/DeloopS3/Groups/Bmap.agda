{-# OPTIONS --safe --cubical #-}
module DeloopS3.Groups.Bmap where

-- Pointed classifying-space maps induced by group homomorphisms.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Pointed.Base
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.HITs.EilenbergMacLane1.Base
import Cubical.HITs.EilenbergMacLane1.Properties as EM

private
  variable
    ℓ ℓ' ℓ'' : Level
    G : Group ℓ
    H : Group ℓ'
    K : Group ℓ''

Bmap : GroupHom G H → EM₁ G → EM₁ H
Bmap {G = G} {H = H} f = EM.rec' G (emsquash) (embase)
  (λ g → emloop (f .fst g))
  (λ g h → cong (emloop) (IsGroupHom.pres· (f .snd) g h)
           ∙ emloop-comp H (f .fst g) (f .fst h))

Bmap-base : (f : GroupHom G H) → Bmap f (embase) ≡ embase
Bmap-base f = refl

Bmap-loop : (f : GroupHom G H) (g : G .fst)
  → cong (Bmap f) (emloop g) ≡ emloop (f .fst g)
Bmap-loop f g = refl

B∙ : Group ℓ → Pointed ℓ
B∙ G = EM₁ G , embase

Bmap∙ : GroupHom G H → B∙ G →∙ B∙ H
Bmap∙ f = Bmap f , refl

Bmap-comp : (f : GroupHom G H) (g : GroupHom H K) (x : EM₁ G)
  → Bmap (compGroupHom f g) x ≡ Bmap g (Bmap f x)
Bmap-comp {G = G} {K = K} f g =
  EM.elimSet G (λ x → emsquash _ _) refl (λ a i j → emloop (g .fst (f .fst a)) i)

-- Equality of pointed maps, with a constant basepoint track (not just
-- equality of their underlying functions).
Bmap-comp∙ : (f : GroupHom G H) (g : GroupHom H K)
  → Bmap∙ (compGroupHom f g) ≡ ((λ x → Bmap g (Bmap f x)) , refl)
Bmap-comp∙ f g i = (λ x → Bmap-comp f g x i) , refl

Bmap-id : (x : EM₁ G) → Bmap idGroupHom x ≡ x
Bmap-id {G = G} = EM.elimSet G (λ x → emsquash _ _) refl
  (λ a i j → emloop a i)

Bmap-id∙ : Bmap∙ (idGroupHom {G = G}) ≡ idfun∙ (B∙ G)
Bmap-id∙ i = (λ x → Bmap-id x i) , refl

open import Cubical.Foundations.Pointed.Properties using (_∘∙_)
open import Cubical.Foundations.GroupoidLaws using (rUnit)

Bmap-pointed-composition : (f : GroupHom G H) (g : GroupHom H K)
  → Bmap∙ (compGroupHom f g) ≡ Bmap∙ g ∘∙ Bmap∙ f
Bmap-pointed-composition f g = Bmap-comp∙ f g
  ∙ (λ i → (λ x → Bmap g (Bmap f x)) , rUnit refl i)
