{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Cokernel where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT

Coker : {A B : AbGroup ℓ-zero} → AbGroupHom A B → Group₀
Coker {B = B} f = AbGroup→Group (B /Im f)

module _ {A B C D : AbGroup ℓ-zero}
  (f : AbGroupHom A B) (g : AbGroupHom C D)
  (h : AbGroupHom B D) (k : AbGroupHom A C)
  (square : (a : fst A) → fst g (fst k a) ≡ fst h (fst f a)) where
  private
    module D = AbGroupStr (snd D)

  coker-map : GroupHom (Coker f) (Coker g)
  coker-map = Hom/ h λ a b → PT.map λ { (u , p) → fst k u ,
    square u ∙ cong (fst h) p ∙ IsGroupHom.pres· (snd h) a (AbGroupStr.-_ (snd B) b)
      ∙ cong (D._+_ (fst h a)) (IsGroupHom.presinv (snd h) b) }

-- A split row reduction with an explicit chain correction.  The source
-- ranks may differ; this cancels genuine unit relations, not generators
-- without their relations.
module _ {A B C D : AbGroup ℓ-zero}
  (f : AbGroupHom A B) (g : AbGroupHom C D)
  (p : AbGroupHom B D) (i : AbGroupHom D B)
  (s : AbGroupHom A C) (l : AbGroupHom C A)
  (psquare : (a : fst A) → fst g (fst s a) ≡ fst p (fst f a))
  (isquare : (a : fst C) → fst f (fst l a) ≡ fst i (fst g a))
  (pi : (d : fst D) → fst p (fst i d) ≡ d)
  (t : fst B → fst A)
  (correction : (b : fst B) → fst f (t b)
    ≡ AbGroupStr._+_ (snd B) b (AbGroupStr.-_ (snd B) (fst i (fst p b)))) where

  coker-reduction : GroupIso (Coker f) (Coker g)
  Iso.fun (fst coker-reduction) = fst (coker-map f g p s psquare)
  Iso.inv (fst coker-reduction) = fst (coker-map g f i l isquare)
  Iso.sec (fst coker-reduction) = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ d → cong SQ.[_] (pi d))
  Iso.ret (fst coker-reduction) = SQ.elimProp (λ _ → SQ.squash/ _ _)
    (λ b → sym (SQ.eq/ b (fst i (fst p b)) PT.∣ t b , correction b ∣₁))
  snd coker-reduction = snd (coker-map f g p s psquare)

product-hom : {A B C D : AbGroup ℓ-zero}
  → AbGroupHom A B → AbGroupHom C D → AbGroupHom (dirProdAb A C) (dirProdAb B D)
fst (product-hom f g) (a , c) = fst f a , fst g c
snd (product-hom f g) = makeIsGroupHom λ a b →
  ΣPathP (IsGroupHom.pres· (snd f) (fst a) (fst b) ,
          IsGroupHom.pres· (snd g) (snd a) (snd b))

module _ {A B C D : AbGroup ℓ-zero} (f : AbGroupHom A B) (g : AbGroupHom C D) where
  private
    module A = AbGroupStr (snd A)
    module B = AbGroupStr (snd B)
    module C = AbGroupStr (snd C)
    module D = AbGroupStr (snd D)
    F : fst (Coker (product-hom f g)) → fst (Coker f) × fst (Coker g)
    F = SQ.rec (isSet× SQ.squash/ SQ.squash/)
      (λ b → SQ.[ fst b ] , SQ.[ snd b ])
      (λ a b r → ΣPathP
        (SQ.eq/ (fst a) (fst b) (PT.map (λ { ((u , v) , e) → u , cong fst e }) r) ,
         SQ.eq/ (snd a) (snd b) (PT.map (λ { ((u , v) , e) → v , cong snd e }) r)))

    join : fst (Coker f) → fst (Coker g) → fst (Coker (product-hom f g))
    join = SQ.rec2 SQ.squash/ (λ b d → SQ.[ b , d ])
      (λ a b d → PT.rec (SQ.squash/ _ _) λ { (u , e) →
        SQ.eq/ (a , d) (b , d) PT.∣ (u , C.0g) ,
          ΣPathP (e , IsGroupHom.pres1 (snd g) ∙ sym (D.+InvR d)) ∣₁ })
      (λ b a d → PT.rec (SQ.squash/ _ _) λ { (u , e) →
        SQ.eq/ (b , a) (b , d) PT.∣ (A.0g , u) ,
          ΣPathP (IsGroupHom.pres1 (snd f) ∙ sym (B.+InvR b) , e) ∣₁ })

  coker-product : GroupIso (Coker (product-hom f g)) (DirProd (Coker f) (Coker g))
  Iso.fun (fst coker-product) = F
  Iso.inv (fst coker-product) b = join (fst b) (snd b)
  Iso.sec (fst coker-product) (b , d) =
    SQ.elimProp2 {P = λ b d → F (join b d) ≡ (b , d)}
      (λ b d → isSet× SQ.squash/ SQ.squash/ (F (join b d)) (b , d)) (λ _ _ → refl) b d
  Iso.ret (fst coker-product) = SQ.elimProp (λ _ → SQ.squash/ _ _) (λ _ → refl)
  snd coker-product = makeIsGroupHom
    (SQ.elimProp2 (λ _ _ → isSet× SQ.squash/ SQ.squash/ _ _) (λ _ _ → refl))
