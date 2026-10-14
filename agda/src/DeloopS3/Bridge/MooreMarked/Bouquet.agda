{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.MooreMarked.Bouquet where

-- Concrete cofibre calculation with the marked bouquet cokernel and
-- Hurewicz equivalence. Both retain the bottom map without unfolding
-- the unmarked homology equivalence.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; ¬-<-zero)
open import Cubical.Data.Int using (ℤ ; pos ; ·IdL)
open import Cubical.Data.Fin using (Fin ; fzero ; isContrFin1)
open import Cubical.Data.Unit using (Unit ; tt)
import Cubical.Data.Empty as Empty
import Cubical.HITs.SetQuotients as SQ
open import Cubical.HITs.Pushout using (cofib ; inl ; inr ; push ; pushoutEquiv)
open import Cubical.HITs.Sn using (S₊ ; S₊∙ ; ptSn)
open import Cubical.HITs.Sn.Degree using (degree)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap ; FinSphereBouquetMap∙)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal ; bouquetDegree)
open import Cubical.Homotopy.Connected using (isConnected)
open import Cubical.Homotopy.Group.PiAbCofibFinSphereBouquetMap using
  (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree
  ; π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreePresGens
  ; πᵃᵇFinSphereBouquetMapGenerator)
open import Cubical.CW.Instances.SphereBouquetMap using (SphereBouquet/ᶜʷ)
open import Cubical.CW.Instances.Sn using (Sᶜʷ)
open import Cubical.CW.Homology.Groups.Sn using (genHₙSⁿ)
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap using (ℤ[]/ImSphereMap)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→Equiv ; H̃ᶜʷ→comp)
open import Cubical.CW.HurewiczTheorem using
  (HurewiczHomAb ; HurewiczMapCofibEquiv ; HurewiczMapUntrunc)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Algebra.Group.ZAction using (ℤHom→ℤ/im≅ℤ/im1)
open import Cubical.Algebra.Group.QuotientGroup using (Hom/ImIso)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_] ; ℤFinGenerator)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; isCW ; H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.MooreMarked.Cyclic using (oneMod)

one-in : (n : ℕ) → S₊ n → SphereBouquet n (Fin 1)
one-in n x = inr (fzero , x)

one-petal : (n : ℕ) → SphereBouquet n (Fin 1) → S₊ n
one-petal n = pickPetal fzero

private
  one-ret : (n : ℕ) (x : SphereBouquet n (Fin 1))
    → one-in n (one-petal n x) ≡ x
  one-ret n (inl tt) = sym (push fzero)
  one-ret n (inr ((zero , tt) , x)) = refl
  one-ret n (push (zero , tt) i) j = push fzero (i ∨ ~ j)

one-equiv : (n : ℕ) → SphereBouquet n (Fin 1) ≃ S₊ n
one-equiv n = isoToEquiv (iso (one-petal n) (one-in n) (λ _ → refl) (one-ret n))

one-map : {n : ℕ} → (S₊ (suc n) → S₊ (suc n)) → FinSphereBouquetMap 1 1 n
one-map {n} f = one-in (suc n) ∘ f ∘ one-petal (suc n)

one-cofibre : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
  → cofib (one-map f) ≃ cofib f
one-cofibre {n} f = pushoutEquiv (λ _ → tt) (one-map f) (λ _ → tt) f
  (one-equiv (suc n)) (idEquiv Unit) (one-equiv (suc n)) refl refl

private
  eval-iso : GroupIso (AbGroup→Group ℤ[Fin 1 ]) ℤGroup
  Iso.fun (fst eval-iso) r = r fzero
  Iso.inv (fst eval-iso) z = λ _ → z
  Iso.sec (fst eval-iso) z = refl
  Iso.ret (fst eval-iso) r = funExt λ x → cong r (snd isContrFin1 x)
  snd eval-iso = makeIsGroupHom λ _ _ → refl

  conjugate-degree : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
    → GroupHom ℤGroup ℤGroup
  conjugate-degree f = compGroupHom (GroupIso→GroupHom (invGroupIso eval-iso))
    (compGroupHom (bouquetDegree (one-map f)) (GroupIso→GroupHom eval-iso))

  degree-one : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
    → fst (conjugate-degree f) (pos 1) ≡ degree (suc n) f
  degree-one f = ·IdL _

opaque
  one-cokernel : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
    (m : ℕ) (positive : 0 < m) → degree (suc n) f ≡ pos m
    → GroupEquiv (ℤ[]/ImSphereMap (one-map f)) (ℤGroup/ m)
  one-cokernel f zero positive deg = Empty.rec (¬-<-zero positive)
  one-cokernel f (suc m) positive deg = compGroupEquiv
    (GroupIso→GroupEquiv
      (Hom/ImIso (bouquetDegree (one-map f)) (conjugate-degree f)
        eval-iso eval-iso
        (λ r → cong (λ s → fst (bouquetDegree (one-map f)) s fzero)
          (Iso.ret (fst eval-iso) r))))
    (BijectionIsoToGroupEquiv
      (ℤHom→ℤ/im≅ℤ/im1 (conjugate-degree f) m (degree-one f ∙ deg)))

opaque
  unfolding one-cokernel
  one-cokernel-generator : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
    (m : ℕ) (positive : 0 < m) (deg : degree (suc n) f ≡ pos m)
    → equivFun (fst (one-cokernel f m positive deg)) SQ.[ ℤFinGenerator fzero ]
      ≡ oneMod m positive
  one-cokernel-generator f zero positive deg = Empty.rec (¬-<-zero positive)
  one-cokernel-generator f (suc m) positive deg = refl

module Concrete {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
  (point : f (ptSn (suc n)) ≡ ptSn (suc n))
  (cw : isCW (cofib f))
  (connected : isConnected 2 (cofib (one-map f))) where

  X : CW₀
  X = cofib f , cw

  α : FinSphereBouquetMap∙ 1 1 n
  α = one-map f , (cong (one-in (suc n)) point ∙ sym (push fzero))
  B : CW₀
  B = SphereBouquet/ᶜʷ (one-map f)

  opaque
    quotient-to-homology : GroupEquiv (ℤ[]/ImSphereMap (one-map f)) (H̃ᶜʷ B (suc n))
    quotient-to-homology = compGroupEquiv
      (invGroupEquiv (GroupIso→GroupEquiv
        (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α)))
      ((fst (HurewiczHomAb B (inl tt) connected n)
        , HurewiczMapCofibEquiv α connected)
        , snd (HurewiczHomAb B (inl tt) connected n))

  opaque
    unfolding quotient-to-homology
    quotient-to-homology-generator :
      equivFun (fst quotient-to-homology) SQ.[ ℤFinGenerator fzero ]
      ≡ HurewiczMapUntrunc {n = n} B (inr (one-in (suc n) (ptSn (suc n))))
          ((λ x → inr (one-in (suc n) x)) , refl)
    quotient-to-homology-generator = cong
      (fst (HurewiczHomAb B (inl tt) connected n))
      (cong (Iso.inv (fst (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α)))
        (sym (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegreePresGens α fzero))
      ∙ Iso.ret (fst (π'ᵃᵇCofibFinSphereBouquetMap≅ℤ[]/BouquetDegree α))
        (πᵃᵇFinSphereBouquetMapGenerator α fzero))

  opaque
    quotient-to-actual : GroupEquiv (ℤ[]/ImSphereMap (one-map f)) (H̃ᶜʷ X (suc n))
    quotient-to-actual = compGroupEquiv quotient-to-homology
      (H̃ᶜʷ→Equiv {C = B} {D = X} (suc n) (one-cofibre f))

  opaque
    unfolding quotient-to-actual
    quotient-to-actual-generator :
      equivFun (fst quotient-to-actual) SQ.[ ℤFinGenerator fzero ]
      ≡ HurewiczMapUntrunc {n = n} X (inr (ptSn (suc n))) (inr , refl)
    quotient-to-actual-generator =
      cong (fst (H̃ᶜʷ→ {C = B} {D = X} (suc n) (equivFun (one-cofibre f))))
        quotient-to-homology-generator
      ∙ funExt⁻ (cong fst (sym (H̃ᶜʷ→comp
          {C = Sᶜʷ (suc n)} {D = B} {E = X} (suc n)
          (equivFun (one-cofibre f)) (λ x → inr (one-in (suc n) x)))))
        (genHₙSⁿ n)

  opaque
    marked : (m : ℕ) (positive : 0 < m) → degree (suc n) f ≡ pos m
      → GroupEquiv (H̃ᶜʷ X (suc n)) (ℤGroup/ m)
    marked m positive deg = compGroupEquiv (invGroupEquiv quotient-to-actual)
      (one-cokernel f m positive deg)

  opaque
    unfolding marked
    marked-generator : (m : ℕ) (positive : 0 < m) (deg : degree (suc n) f ≡ pos m)
      → equivFun (fst (marked m positive deg))
          (HurewiczMapUntrunc {n = n} X (inr (ptSn (suc n))) (inr , refl))
        ≡ oneMod m positive
    marked-generator m positive deg =
      cong (equivFun (fst (one-cokernel f m positive deg)))
        (cong (invEq (fst quotient-to-actual)) (sym quotient-to-actual-generator)
        ∙ retEq (fst quotient-to-actual) SQ.[ ℤFinGenerator fzero ])
      ∙ one-cokernel-generator f m positive deg
