{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.FiniteFree where

-- Additive maps on finite integer-function groups are represented by
-- their values on the standard basis.  First use FinData (the index
-- type of the matrix library), then transport the whole direct-finiteness
-- statement along FinData≡Fin to the Sigma-based CW-chain convention.

open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
open import Cubical.Data.FinData using (Fin ; zero ; suc)
open import Cubical.Data.Fin.Properties using (FinData≡Fin)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Pi using (ΠℤAbGroup)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Algebra.Ring.BigOps
open import Cubical.Algebra.Matrix.CommRingCoefficient
open import DeloopS3.Bridge.CellularPushout.PrismChains.FiniteFreeMatrix

private
  open CommRingStr (ℤCommRing .snd)
  open Coefficient ℤCommRing
  open Sum (CommRing→Ring ℤCommRing)
  open IsGroupHom

  V : ℕ → AbGroup ℓ-zero
  V n = ΠℤAbGroup (Fin n)

  variable m n : ℕ

  scalar : (h : AbGroupHom (V n) (V m)) (a : ℤ) (x : V n .fst)
    → h .fst (λ i → a · x i) ≡ (λ i → a · h .fst x i)
  scalar h (pos zero) x = pres1 (h .snd)
  scalar h (pos (suc k)) x = pres· (h .snd) x (λ i → pos k · x i)
    ∙ (λ j i → h .fst x i + scalar h (pos k) x j i)
  scalar h (negsuc zero) x = presinv (h .snd) x
  scalar h (negsuc (suc k)) x =
      pres· (h .snd) (λ i → - x i) (λ i → negsuc k · x i)
    ∙ (λ j i → presinv (h .snd) x j i + scalar h (negsuc k) x j i)

  sum-hom : (h : AbGroupHom (V n) (V m)) (k : ℕ) (w : Fin k → V n .fst)
    → h .fst (λ i → ∑ (λ j → w j i)) ≡ (λ i → ∑ (λ j → h .fst (w j) i))
  sum-hom h zero w = pres1 (h .snd)
  sum-hom h (suc k) w =
      pres· (h .snd) (w zero) (λ i → ∑ (λ j → w (suc j) i))
    ∙ (λ r i → h .fst (w zero) i + sum-hom h k (λ j → w (suc j)) r i)

  basis : Fin n → V n .fst
  basis j i = 𝟙 j i

  matrix : AbGroupHom (V n) (V m) → Mat m n
  matrix h i j = h .fst (basis j) i

  represents : (h : AbGroupHom (V n) (V m)) (x : V n .fst) (i : Fin m)
    → h .fst x i ≡ ∑ (λ j → matrix h i j · x j)
  represents {n = n} h x i =
      cong (λ y → h .fst y i) (funExt λ j → sym (∑Mulr1 n x j))
    ∙ cong (λ y → y i) (sum-hom h n (λ j k → x j · basis j k))
    ∙ ∑Ext (λ j → cong (λ y → y i) (scalar h (x j) (basis j)))
    ∙ ∑Ext (λ j → ·Comm (x j) (matrix h i j))

  matrix-faithful : (f g : AbGroupHom (V n) (V m))
    → matrix f ≡ matrix g → f ≡ g
  matrix-faithful f g p = GroupHom≡ (funExt λ x → funExt λ i →
      represents f x i
    ∙ cong (λ M → ∑ (λ j → M i j · x j)) p
    ∙ sym (represents g x i))

  matrix-comp : (f : AbGroupHom (V n) (V n)) (g : AbGroupHom (V n) (V n))
    → matrix (compGroupHom f g) ≡ matrix g ⋆ matrix f
  matrix-comp f g = funExt λ i → funExt λ j → represents g (f .fst (basis j)) i

  matrix-id : matrix (idGroupHom {G = AbGroup→Group (V n)}) ≡ 𝟙
  matrix-id = 𝟙ᵗ

  DirectFinite : AbGroup ℓ-zero → Type
  DirectFinite G = (u t : AbGroupHom G G)
    → compGroupHom u t ≡ idGroupHom → compGroupHom t u ≡ idGroupHom

  vector-direct-finite : (n : ℕ) → DirectFinite (V n)
  vector-direct-finite n u t p = matrix-faithful (compGroupHom t u) idGroupHom
    (matrix-comp t u
      ∙ integer-matrix-direct-finite n (matrix u) (matrix t)
          (sym (matrix-comp u t) ∙ cong matrix p ∙ matrix-id)
      ∙ sym matrix-id)

-- compGroupHom u t means first u, then t: the premise is t ∘ u = id.
finite-free-direct-finite : (n : ℕ)
  (u t : AbGroupHom ℤ[Fin n ] ℤ[Fin n ])
  → compGroupHom u t ≡ idGroupHom
  → compGroupHom t u ≡ idGroupHom
finite-free-direct-finite n =
  subst (λ X → DirectFinite (ΠℤAbGroup X)) (FinData≡Fin n) (vector-direct-finite n)
