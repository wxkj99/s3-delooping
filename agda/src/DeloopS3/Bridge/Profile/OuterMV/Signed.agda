{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.OuterMV.Signed where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Int using (ℤ ; pos ; _·_ ; -_)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup ; negEquivℤ)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.Profile.OuterMV.Groups
open import DeloopS3.Bridge.Profile.OuterMV.Cyclic

open IsGroupHom

private
  -- The minus sign is absorbed into the target identification. Its
  -- underlying function is deliberately transparent on abstract groups.
  negative-right-equiv : (B C : Group₀) → isContr (fst B)
    → GroupEquiv C ℤGroup → GroupEquiv (DirProd B C) ℤGroup
  negative-right-equiv B C b0 eC = compGroupEquiv
    (GroupIso→GroupEquiv (drop , makeIsGroupHom (λ _ _ → refl)))
    (compGroupEquiv eC negEquivℤ)
    where
    drop : Iso (fst (DirProd B C)) (fst C)
    Iso.fun drop = snd
    Iso.inv drop c = GroupStr.1g (snd B) , c
    Iso.sec drop c = refl
    Iso.ret drop (b , c) = ΣPathP (sym (contr→zero B b0 b) , refl)

abstract
  signed-source-injective : {A B C : Group₀}
    (s : GroupHom A (DirProd B C)) (p : GroupHom A C)
    → ((x : fst A) → snd (fst s x) ≡ GroupStr.inv (snd C) (fst p x))
    → (N : ℕ) → 0 < N
    → (eA : GroupEquiv A ℤGroup) (eC : GroupEquiv C ℤGroup)
    → ((x : fst A) → equivFun (fst eC) (fst p x)
                    ≡ pos N · equivFun (fst eA) x)
    → isInjective s
  signed-source-injective {A = A} {C = C} s p signed N positive eA eC degree x sx0 =
    equiv-kernel-zero (GroupEquiv→GroupHom eA) (snd (fst eA)) x
      (kernel-×N-zero N positive (equivFun (fst eA) x)
        (sym (degree x) ∙ cong (equivFun (fst eC)) px0 ∙ pres1 (snd eC)))
    where
    px0 : fst p x ≡ GroupStr.1g (snd C)
    px0 = sym (GroupTheory.invInv C (fst p x))
      ∙ cong (GroupStr.inv (snd C)) (sym (signed x) ∙ cong snd sx0)
      ∙ GroupTheory.inv1g C

  signed-cyclic-cokernel : {A B C P D : Group₀}
    (s : GroupHom A (DirProd B C)) (p : GroupHom A C)
    (v : GroupHom (DirProd B C) P) (w : GroupHom P D)
    → Exact₃ s v → Exact₃ v w
    → ((x : fst A) → snd (fst s x) ≡ GroupStr.inv (snd C) (fst p x))
    → (N : ℕ) (eA : GroupEquiv A ℤGroup) (eC : GroupEquiv C ℤGroup)
    → ((x : fst A) → equivFun (fst eC) (fst p x)
                    ≡ pos N · equivFun (fst eA) x)
    → isContr (fst B) → isContr (fst D)
    → GroupEquiv P (ℤGroup/ N)
  signed-cyclic-cokernel {A = A} {B = B} {C = C} s p v w ex₁ ex₂ signed N eA eC degree b0 d0 =
    exact-cyclic-cokernel s v ex₁ (exact-right-surjective v w ex₂ d0)
      N eA (negative-right-equiv B C b0 eC) signed-degree
    where
    signed-degree : (x : fst A)
      → - equivFun (fst eC) (snd (fst s x)) ≡ pos N · equivFun (fst eA) x
    signed-degree x = cong (λ c → - equivFun (fst eC) c) (signed x)
      ∙ cong -_ (presinv (snd eC) (fst p x))
      ∙ GroupTheory.invInv ℤGroup (equivFun (fst eC) (fst p x))
      ∙ degree x
