{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.CircleCofibre where

-- The degree-one specialization of Bridge.CofibreHomology's one-petal
-- argument.  No LES or identification of unrelated RP² HITs is used.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; abs ; ·IdL)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; isContrFin1)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.HITs.S1.Base using (S¹)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr ; push ; pushoutEquiv)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal ; bouquetDegree ; bouquetDegreeSusp)
open import Cubical.HITs.Sn.Degree using (degree)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ ; ∂ ; CW-AugChainComplex)
open import Cubical.CW.Instances.SphereBouquetMap using
  (SphereBouquet/ˢᵏᵉˡ ; SphereBouquet/ᶜʷ)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→Equiv)
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap using
  (ℤ[]/ImSphereMap ; GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap ; bouquetSusp→Charac)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Algebra.Group.ZAction using (ℤ/imIso ; imℤHomSubGroup)
open import Cubical.Algebra.Group.QuotientGroup using (_/_ ; Hom/ImIso)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; Hzero)
open import DeloopS3.Bridge.ComponentHomology.ChainTools

one-petal : SphereBouquet 1 (Fin 1) → S¹
one-petal = pickPetal fzero

one-in : S¹ → SphereBouquet 1 (Fin 1)
one-in x = inr (fzero , x)

private
  one-ret : (x : SphereBouquet 1 (Fin 1)) → one-in (one-petal x) ≡ x
  one-ret (inl tt) = sym (push fzero)
  one-ret (inr ((0 , tt) , x)) = refl
  one-ret (push (0 , tt) i) j = push fzero (i ∨ ~ j)

one-equiv : SphereBouquet 1 (Fin 1) ≃ S¹
one-equiv = isoToEquiv (iso one-petal one-in (λ _ → refl) one-ret)

one-map : (S¹ → S¹) → FinSphereBouquetMap 1 1 0
one-map f = one-in ∘ f ∘ one-petal

abstract
  one-cofibre : (f : S¹ → S¹) → cofib (one-map f) ≃ cofib f
  one-cofibre f = pushoutEquiv (λ _ → tt) (one-map f) (λ _ → tt) f
    one-equiv (idEquiv Unit) one-equiv refl refl

private
  eval-iso : GroupIso (AbGroup→Group ℤ[Fin 1 ]) ℤGroup
  Iso.fun (fst eval-iso) r = r fzero
  Iso.inv (fst eval-iso) z = λ _ → z
  Iso.sec (fst eval-iso) z = refl
  Iso.ret (fst eval-iso) r = funExt λ x → cong r (snd isContrFin1 x)
  snd eval-iso = makeIsGroupHom λ _ _ → refl

  conjugate-degree : (S¹ → S¹) → GroupHom ℤGroup ℤGroup
  conjugate-degree f = compGroupHom (GroupIso→GroupHom (invGroupIso eval-iso))
    (compGroupHom (bouquetDegree (one-map f)) (GroupIso→GroupHom eval-iso))

  abstract
    conjugate-degree-one : (f : S¹ → S¹)
      → fst (conjugate-degree f) (pos 1) ≡ degree 1 f
    conjugate-degree-one f = ·IdL _

    one-cokernel : (f : S¹ → S¹) (m : ℕ) → degree 1 f ≡ pos m
      → GroupEquiv (ℤ[]/ImSphereMap (one-map f)) (ℤGroup/ m)
    one-cokernel f m deg = GroupIso→GroupEquiv
      (compGroupIso
        (Hom/ImIso (bouquetDegree (one-map f)) (conjugate-degree f)
          eval-iso eval-iso
          (λ r → cong (λ s → fst (bouquetDegree (one-map f)) s fzero)
            (Iso.ret (fst eval-iso) r)))
        (subst (λ z → GroupIso (ℤGroup / imℤHomSubGroup (conjugate-degree f))
                    (ℤGroup/ abs z))
          (conjugate-degree-one f ∙ deg) (ℤ/imIso (conjugate-degree f))))

abstract
  circle-cofibre-H₀ : (f : S¹ → S¹) (X : CW₀) → fst X ≃ cofib f → Hzero X 0
  circle-cofibre-H₀ f X e = isOfHLevelRespectEquiv 0
    (invEquiv (fst (H̃ᶜʷ→Equiv {C = X} {D = SphereBouquet/ᶜʷ (one-map f)} 0
      (compEquiv e (invEquiv (one-cofibre f))))))
    (one-vertex-homology (SphereBouquet/ˢᵏᵉˡ (one-map f)) refl)

  circle-cofibre-H₁ : (f : S¹ → S¹) (X : CW₀) → fst X ≃ cofib f
    → (m : ℕ) → degree 1 f ≡ pos m
    → GroupEquiv (H̃ᶜʷ X 1) (ℤGroup/ m)
  circle-cofibre-H₁ f X e m deg = compGroupEquiv
    (H̃ᶜʷ→Equiv {C = X} {D = SphereBouquet/ᶜʷ (one-map f)} 1
      (compEquiv e (invEquiv (one-cofibre f))))
    (compGroupEquiv
      (GroupIso→GroupEquiv (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap (one-map f)))
      (one-cokernel f m deg))

  circle-cofibre-boundary : (α : FinSphereBouquetMap 1 1 0)
    → α (inl tt) ≡ inl tt
    → ∂ (SphereBouquet/ˢᵏᵉˡ α) 1 ≡ bouquetDegree α
  circle-cofibre-boundary α apt = cong bouquetDegree
    (bouquetSusp→Charac α (λ _ → pos 0) (λ _ → pos 0) apt refl refl)
    ∙ sym (bouquetDegreeSusp α)

  circle-cofibre-H₂ : (f : S¹ → S¹) (X : CW₀) → fst X ≃ cofib f
    → (m : ℕ) → degree 1 f ≡ pos (suc m)
    → f Cubical.HITs.S1.Base.base ≡ Cubical.HITs.S1.Base.base
    → Hzero X 2
  circle-cofibre-H₂ f X e m deg pointed = isOfHLevelRespectEquiv 0
    (invEquiv (fst (H̃ᶜʷ→Equiv {C = X} {D = SphereBouquet/ᶜʷ (one-map f)} 2
      (compEquiv e (invEquiv (one-cofibre f))))))
    (zero-kernel-homology (CW-AugChainComplex (SphereBouquet/ˢᵏᵉˡ (one-map f))) 2
      λ r ker → funExt λ x → cong r (sym (snd isContrFin1 x))
        ∙ Z.·suc→0 (r fzero) m
          (cong (r fzero Z.·_) (sym deg)
            ∙ funExt⁻
              (sym (funExt⁻ (cong fst (circle-cofibre-boundary (one-map f)
                (cong one-in pointed ∙ sym (push fzero)))) r) ∙ ker) fzero))
