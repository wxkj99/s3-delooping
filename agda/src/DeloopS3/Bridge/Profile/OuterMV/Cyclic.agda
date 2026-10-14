{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.OuterMV.Cyclic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; ¬-<-zero)
open import Cubical.Data.Int using (ℤ ; pos ; abs ; _·_ ; ·IdR ; ·Comm ; ·suc→0)
open import Cubical.Data.Sigma
import Cubical.Data.Empty as Empty
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup ; ℤHom)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Algebra.Group.Instances.Unit using (UnitGroup₀ ; →UnitHom)
open import Cubical.Algebra.Group.QuotientGroup using (_/_)
open import Cubical.Algebra.Group.IsomorphismTheorems using (isoThm1 ; surjImIso)
open import Cubical.Algebra.Group.ZAction using (imℤHomSubGroup ; ℤ/imIso ; ℤ/im≅ℤ/ker)
open import Cubical.Algebra.Group.Exact using (Exact4)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.Profile.OuterMV.Groups using (exact-composite)

open IsGroupHom

abstract
  kernel-×N-zero : (N : ℕ) → 0 < N
    → (x : ℤ) → pos N · x ≡ pos 0 → x ≡ pos 0
  kernel-×N-zero zero positive x p = Empty.rec (¬-<-zero positive)
  kernel-×N-zero (suc n) positive x p = ·suc→0 x n (·Comm x (pos (suc n)) ∙ p)

  -- The genuine quotient by the image of multiplication, identified with
  -- IntMod's Fin model by the library's quotient universal property.
  -- This includes N = 0 and N = 1 without exceptional conventions.
  coker-×N-≅-ℤ/N : (N : ℕ)
    → GroupEquiv (ℤGroup / imℤHomSubGroup (ℤHom (pos N))) (ℤGroup/ N)
  coker-×N-≅-ℤ/N N = subst
    (λ n → GroupEquiv (ℤGroup / imℤHomSubGroup (ℤHom (pos N))) (ℤGroup/ n))
    (cong abs (·IdR (pos N))) (GroupIso→GroupEquiv (ℤ/imIso (ℤHom (pos N))))

  -- Any exact surjective presentation of this cokernel has the same
  -- group. No choice is made from a truncated image into a raw fibre.
  exact-cyclic-cokernel : {G H K : Group₀}
    (u : GroupHom G H) (v : GroupHom H K)
    → Exact₃ u v → isSurjective v
    → (N : ℕ) (eG : GroupEquiv G ℤGroup) (eH : GroupEquiv H ℤGroup)
    → ((x : fst G) → equivFun (fst eH) (fst u x)
                    ≡ pos N · equivFun (fst eG) x)
    → GroupEquiv K (ℤGroup/ N)
  exact-cyclic-cokernel {G = G} {H = H} {K = K} u v ex onto N eG eH degree =
    compGroupEquiv (invGroupEquiv (GroupIso→GroupEquiv quotient→K))
      (coker-×N-≅-ℤ/N N)
    where
    v′ : GroupHom ℤGroup K
    v′ = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv eH)) v

    onto′ : isSurjective v′
    onto′ k = PT.map
      (λ { (h , p) → equivFun (fst eH) h , cong (fst v) (retEq (fst eH) h) ∙ p })
      (onto k)

    square : (x : ℤ)
      → invEq (fst eH) (pos N · x) ≡ fst u (invEq (fst eG) x)
    square x = cong (invEq (fst eH))
      (sym (degree (invEq (fst eG) x)
        ∙ cong (pos N ·_) (secEq (fst eG) x)))
      ∙ retEq (fst eH) (fst u (invEq (fst eG) x))

    ex′ : Exact4 ℤGroup ℤGroup K UnitGroup₀ (ℤHom (pos N)) v′ (→UnitHom K)
    Exact4.ImG→H⊂KerH→L ex′ z = PT.rec (GroupStr.is-set (snd K) _ _)
      (λ { (x , p) → sym (cong (fst v′) p)
        ∙ cong (fst v) (square x)
        ∙ exact-composite {u = u} {v = v} ex (invEq (fst eG) x) })
    Exact4.KerH→L⊂ImG→H ex′ z p = PT.map
      (λ { (x , q) → equivFun (fst eG) x , sym (degree x)
        ∙ cong (equivFun (fst eH)) q ∙ secEq (fst eH) z })
      (equivFun (ex (invEq (fst eH) z)) p)
    Exact4.ImH→L⊂KerL→R ex′ k _ = refl
    Exact4.KerL→R⊂ImH→L ex′ k _ = onto′ k

    quotient→K : GroupIso (ℤGroup / imℤHomSubGroup (ℤHom (pos N))) K
    quotient→K = compGroupIso (ℤ/im≅ℤ/ker (ℤHom (pos N)) K v′ ex′)
      (compGroupIso (invGroupIso (isoThm1 v′)) (surjImIso v′ onto′))
