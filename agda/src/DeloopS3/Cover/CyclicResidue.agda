{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cover.CyclicResidue where

-- The kernel of integer reduction modulo n is nℤ, including both signs.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc)
import Cubical.Data.Nat as N
import Cubical.Data.Nat.Mod as M
import Cubical.Data.Int as Z
import Cubical.Data.Fin as F
open import Cubical.Algebra.Group.Base using (GroupStr)
open import Cubical.Algebra.Group.Morphisms using (IsGroupHom)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
import DeloopS3.Cover.CircleOrbit as CO

abstract
  residue-multiple-zero : (m : ℕ) (z : Z.ℤ)
    → CO.residue m .fst (Z.pos (suc m) Z.· z)
    ≡ GroupStr.1g ((ℤGroup/ suc m) .snd)
  residue-multiple-zero m (Z.pos a) =
    cong (CO.residue m .fst) (sym (Z.pos·pos (suc m) a))
    ∙ F.toℕ-injective {k = suc m}
        (cong (M._mod suc m) (N.·-comm (suc m) a)
         ∙ M.zero-charac-gen (suc m) a)
  residue-multiple-zero m (Z.negsuc a) =
    cong (CO.residue m .fst) (Z.pos·negsuc (suc m) a)
    ∙ IsGroupHom.presinv (CO.residue m .snd) (Z.pos (suc m) Z.· Z.pos (suc a))
    ∙ cong (GroupStr.inv ((ℤGroup/ suc m) .snd))
        (residue-multiple-zero m (Z.pos (suc a)))
    ∙ GroupTheory.inv1g (ℤGroup/ suc m)

  residue-kernel-positive : (m a : ℕ)
    → CO.residue m .fst (Z.pos a) ≡ GroupStr.1g ((ℤGroup/ suc m) .snd)
    → Σ[ q ∈ Z.ℤ ] Z.pos (suc m) Z.· q ≡ Z.pos a
  residue-kernel-positive m a p = Z.pos (M.quotient a / suc m) ,
    sym (Z.pos·pos (suc m) (M.quotient a / suc m))
    ∙ cong Z.pos
        (sym (cong (N._+ (suc m N.· (M.quotient a / suc m))) (cong fst p))
         ∙ M.≡remainder+quotient (suc m) a)

  residue-kernel : (m : ℕ) (z : Z.ℤ)
    → CO.residue m .fst z ≡ GroupStr.1g ((ℤGroup/ suc m) .snd)
    → Σ[ q ∈ Z.ℤ ] Z.pos (suc m) Z.· q ≡ z
  residue-kernel m (Z.pos a) = residue-kernel-positive m a
  residue-kernel m (Z.negsuc a) p = (Z.- (w .fst)) ,
    sym (Z.-DistR· (Z.pos (suc m)) (w .fst)) ∙ cong Z.-_ (w .snd)
    where
    positive-zero : CO.residue m .fst (Z.pos (suc a))
      ≡ GroupStr.1g ((ℤGroup/ suc m) .snd)
    positive-zero = IsGroupHom.presinv (CO.residue m .snd) (Z.negsuc a)
      ∙ cong (GroupStr.inv ((ℤGroup/ suc m) .snd)) p
      ∙ GroupTheory.inv1g (ℤGroup/ suc m)
    w : Σ[ q ∈ Z.ℤ ] Z.pos (suc m) Z.· q ≡ Z.pos (suc a)
    w = residue-kernel-positive m (suc a) positive-zero
