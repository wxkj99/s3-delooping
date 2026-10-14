{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.MooreMarked.Cyclic where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (idfun)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; ¬-<-zero)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗ→< ; isProp<ᵗ)
open import Cubical.Data.Nat.Mod using (<→mod≡id ; zero-charac)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Sigma using (Σ≡Prop)
import Cubical.Data.Empty as Empty
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_ ; ℤ→Fin ; isHomℤ→Fin)
open import Cubical.Algebra.Group.ZAction using
  (_ℤ[_]·_ ; gen₁-by ; homPresℤ· ; rUnitℤ·ℤ)
open import DeloopS3.Bridge.Recognition.Torsion using (multiple ; pres-multiple)

-- The residue of 1 in the actual Fin-based cyclic group, including C₁.
oneMod : (m : ℕ) → 0 < m → fst (ℤGroup/ m)
oneMod zero positive = Empty.rec (¬-<-zero positive)
oneMod (suc m) positive = ℤ→Fin m (pos 1)

positive₂ : 0 < 2
positive₂ = 1 , refl

-- Prove the algebra on abstract groups, before any homology instantiation.
abstract
  cyclic-endomorphism-id : (G : Group₀) (g : fst G)
    → gen₁-by G g → (f : GroupHom G G) → fst f g ≡ g
    → fst f ≡ idfun (fst G)
  cyclic-endomorphism-id G g generates f fixes = funExt λ x →
    cong (fst f) (snd (generates x))
    ∙ homPresℤ· f g (fst (generates x))
    ∙ cong (λ a → fst (generates x) ℤ[ G ]· a) fixes
    ∙ sym (snd (generates x))

  residue-generates : (m : ℕ) (positive : 0 < m)
    → gen₁-by (ℤGroup/ m) (oneMod m positive)
  residue-generates zero positive = Empty.rec (¬-<-zero positive)
  residue-generates (suc m) positive x = pos (fst x) ,
    sym (Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = suc m})
      (<→mod≡id (fst x) (suc m) (<ᵗ→< (snd x))))
    ∙ cong (ℤ→Fin m) (sym (rUnitℤ·ℤ (pos (fst x))))
    ∙ homPresℤ· (ℤ→Fin m , isHomℤ→Fin m) (pos 1) (pos (fst x))

  cyclic-fixes-one : (m : ℕ) (positive : 0 < m)
    (f : GroupHom (ℤGroup/ m) (ℤGroup/ m))
    → fst f (oneMod m positive) ≡ oneMod m positive
    → fst f ≡ idfun (fst (ℤGroup/ m))
  cyclic-fixes-one m positive =
    cyclic-endomorphism-id (ℤGroup/ m) (oneMod m positive)
      (residue-generates m positive)

  multiple-as-action : (G : Group₀) (m : ℕ) (x : fst G)
    → multiple G m x ≡ pos m ℤ[ G ]· x
  multiple-as-action G zero x = refl
  multiple-as-action G (suc m) x =
    cong (GroupStr._·_ (snd G) x) (multiple-as-action G m x)

  multiple-oneMod : (m : ℕ) (positive : 0 < m)
    → multiple (ℤGroup/ m) m (oneMod m positive)
      ≡ GroupStr.1g (snd (ℤGroup/ m))
  multiple-oneMod zero positive = Empty.rec (¬-<-zero positive)
  multiple-oneMod (suc m) positive =
    sym (pres-multiple (ℤ→Fin m , isHomℤ→Fin m) (suc m) (pos 1))
    ∙ cong (ℤ→Fin m) (multiple-as-action ℤGroup (suc m) (pos 1)
      ∙ rUnitℤ·ℤ (pos (suc m)))
    ∙ Σ≡Prop (λ a → isProp<ᵗ {n = a} {m = suc m}) (zero-charac (suc m))

  marked-map-isEquiv : (m : ℕ) (positive : 0 < m)
    (G H : Group₀) (eG : GroupEquiv G (ℤGroup/ m))
    (eH : GroupEquiv H (ℤGroup/ m)) (g : fst G) (h : fst H)
    → equivFun (fst eG) g ≡ oneMod m positive
    → equivFun (fst eH) h ≡ oneMod m positive
    → (f : GroupHom G H) → fst f g ≡ h → isEquiv (fst f)
  marked-map-isEquiv m positive G H eG eH g h markG markH f value =
    subst isEquiv (sym recovered) (snd (fst equivalence))
    where
    conjugate : GroupHom (ℤGroup/ m) (ℤGroup/ m)
    conjugate = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv eG))
      (compGroupHom f (GroupEquiv→GroupHom eH))
    fixes : fst conjugate (oneMod m positive) ≡ oneMod m positive
    fixes = cong (λ z → equivFun (fst eH) (fst f z))
        (cong (invEq (fst eG)) (sym markG) ∙ retEq (fst eG) g)
      ∙ cong (equivFun (fst eH)) value ∙ markH
    identity : fst conjugate ≡ idfun (fst (ℤGroup/ m))
    identity = cyclic-fixes-one m positive conjugate fixes
    equivalence : GroupEquiv G H
    equivalence = compGroupEquiv eG (invGroupEquiv eH)
    recovered : fst f ≡ equivFun (fst equivalence)
    recovered = funExt λ x → sym (retEq (fst eH) (fst f x))
      ∙ cong (invEq (fst eH))
        (cong (λ z → equivFun (fst eH) (fst f z)) (sym (retEq (fst eG) x))
         ∙ funExt⁻ identity (equivFun (fst eG) x))
