{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Conjugation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.DMCExactness.Groups using (equiv-kernel-zero)

module Change {A B C D : Group₀} (f : GroupHom A B)
  (eA : GroupEquiv A C) (eB : GroupEquiv B D) where
  hom : GroupHom C D
  hom = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv eA))
    (compGroupHom f (GroupEquiv→GroupHom eB))

  abstract
    square : (x : fst A) → fst hom (equivFun (fst eA) x) ≡ equivFun (fst eB) (fst f x)
    square x = cong (λ a → equivFun (fst eB) (fst f a)) (retEq (fst eA) x)

    onto : isSurjective f → isSurjective hom
    onto surj y = PT.map (λ { (x , p) → equivFun (fst eA) x ,
      square x ∙ cong (equivFun (fst eB)) p ∙ secEq (fst eB) y }) (surj (invEq (fst eB) y))

    reflect-isEquiv : isEquiv (fst hom) → isEquiv (fst f)
    reflect-isEquiv e = subst isEquiv
      (funExt (λ x → cong (invEq (fst eB)) (square x) ∙ retEq (fst eB) (fst f x)))
      (snd (compEquiv (fst eA) (compEquiv (fst hom , e) (invEquiv (fst eB)))))

  kernel-iso : GroupIso (kerGroup f) (kerGroup hom)
  Iso.fun (fst kernel-iso) (x , p) = equivFun (fst eA) x ,
    square x ∙ cong (equivFun (fst eB)) p ∙ IsGroupHom.pres1 (snd eB)
  Iso.inv (fst kernel-iso) (y , q) = invEq (fst eA) y ,
    equiv-kernel-zero (GroupEquiv→GroupHom eB) (snd (fst eB)) (fst f (invEq (fst eA) y))
      (sym (square (invEq (fst eA) y)) ∙ cong (fst hom) (secEq (fst eA) y) ∙ q)
  Iso.sec (fst kernel-iso) (y , q) = kerGroup≡ hom (secEq (fst eA) y)
  Iso.ret (fst kernel-iso) (x , p) = kerGroup≡ f (retEq (fst eA) x)
  snd kernel-iso = makeIsGroupHom λ x y → kerGroup≡ hom
    (IsGroupHom.pres· (snd eA) (fst x) (fst y))
