{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.OuterMV where

-- Homology consequences of the geometric Mayer–Vietoris sequence.
-- The degree law concerns the unsigned right vertex map; H₂ uses the signed source.
-- The H₃ quotient formula includes N = 0, with ℤGroup/ 0 = ℤGroup.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Int using (pos ; _·_)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Subgroup using (kerGroup)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; Hzero)
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.Profile.OuterMV.Groups
open import DeloopS3.Bridge.Profile.OuterMV.Cyclic public using
  (kernel-×N-zero ; coker-×N-≅-ℤ/N)
open import DeloopS3.Bridge.Profile.OuterMV.Signed

module _ (A B C P : CW₀) (f : fst A → fst B) (g : fst A → fst C)
  (les : GeometricPushoutLES A B C f g P) where
  private
    module L = SpanSequenceData (snd les)

    abstract
      signed₃ : (x : fst (H̃ᶜʷ A 3))
        → snd (fst (L.source-map 3) x)
         ≡ GroupStr.inv (snd (H̃ᶜʷ C 3)) (fst (cellular-map A C 3 g) x)
      signed₃ x = cong snd (L.source-agrees 3 x)

  abstract
    H₄-zero-from-MV : (N : ℕ) → 0 < N
      → (eA : GroupEquiv (H̃ᶜʷ A 3) ℤGroup)
      → (eC : GroupEquiv (H̃ᶜʷ C 3) ℤGroup)
      → ((x : fst (H̃ᶜʷ A 3)) → equivFun (fst eC)
           (fst (cellular-map A C 3 g) x) ≡ pos N · equivFun (fst eA) x)
      → Hzero B 4 → Hzero C 4 → Hzero P 4
    H₄-zero-from-MV N positive eA eC degree b4 c4 =
      exact-zero-middle-mono
        {G = DirProd (H̃ᶜʷ B 4) (H̃ᶜʷ C 4)} {H = H̃ᶜʷ P 4}
        {K = H̃ᶜʷ A 3} {L = DirProd (H̃ᶜʷ B 3) (H̃ᶜʷ C 3)}
        (L.sum-map 4) (L.boundary 3) (L.source-map 3)
        (L.exact-total 3 (1 , refl)) (L.exact-source 3 (1 , refl))
        (product-zero {B = H̃ᶜʷ B 4} {C = H̃ᶜʷ C 4} b4 c4)
        (signed-source-injective {A = H̃ᶜʷ A 3} {B = H̃ᶜʷ B 3} {C = H̃ᶜʷ C 3}
          (L.source-map 3) (cellular-map A C 3 g) signed₃ N positive eA eC degree)

    H₃-iso-ℤ/N-from-MV : (N : ℕ)
      → (eA : GroupEquiv (H̃ᶜʷ A 3) ℤGroup)
      → (eC : GroupEquiv (H̃ᶜʷ C 3) ℤGroup)
      → ((x : fst (H̃ᶜʷ A 3)) → equivFun (fst eC)
           (fst (cellular-map A C 3 g) x) ≡ pos N · equivFun (fst eA) x)
      → Hzero B 3 → Hzero A 2 → GroupEquiv (H̃ᶜʷ P 3) (ℤGroup/ N)
    H₃-iso-ℤ/N-from-MV N eA eC degree b3 a2 =
      signed-cyclic-cokernel
        {A = H̃ᶜʷ A 3} {B = H̃ᶜʷ B 3} {C = H̃ᶜʷ C 3}
        {P = H̃ᶜʷ P 3} {D = H̃ᶜʷ A 2}
        (L.source-map 3) (cellular-map A C 3 g) (L.sum-map 3) (L.boundary 2)
        (L.exact-target 3 (1 , refl)) (L.exact-total 2 (2 , refl))
        signed₃ N eA eC degree b3 a2

    H₂-zero-from-MV : Hzero B 2 → Hzero C 2
      → isInjective (L.source-map 1) → Hzero P 2
    H₂-zero-from-MV b2 c2 injective =
      exact-zero-middle-mono
        {G = DirProd (H̃ᶜʷ B 2) (H̃ᶜʷ C 2)} {H = H̃ᶜʷ P 2}
        {K = H̃ᶜʷ A 1} {L = DirProd (H̃ᶜʷ B 1) (H̃ᶜʷ C 1)}
        (L.sum-map 2) (L.boundary 1) (L.source-map 1)
        (L.exact-total 1 (3 , refl)) (L.exact-source 1 (3 , refl))
        (product-zero {B = H̃ᶜʷ B 2} {C = H̃ᶜʷ C 2} b2 c2) injective

    H₂-iso-ℤ/2-from-MV : Hzero B 2 → Hzero C 2
      → GroupEquiv (kerGroup (L.source-map 1)) (ℤGroup/ 2)
      → GroupEquiv (H̃ᶜʷ P 2) (ℤGroup/ 2)
    H₂-iso-ℤ/2-from-MV b2 c2 kernel =
      compGroupEquiv {F = H̃ᶜʷ P 2} {G = kerGroup (L.source-map 1)} {H = ℤGroup/ 2}
        (exact-zero-left-ker-equiv
          {G = DirProd (H̃ᶜʷ B 2) (H̃ᶜʷ C 2)} {H = H̃ᶜʷ P 2}
          {K = H̃ᶜʷ A 1} {L = DirProd (H̃ᶜʷ B 1) (H̃ᶜʷ C 1)}
          (L.sum-map 2) (L.boundary 1) (L.source-map 1)
          (L.exact-total 1 (3 , refl)) (L.exact-source 1 (3 , refl))
          (product-zero {B = H̃ᶜʷ B 2} {C = H̃ᶜʷ C 2} b2 c2)) kernel

    -- Optional low-degree consequence. Connected source supplies H̃₀(A)=0;
    -- no unsupported degree -1 boundary is inferred from the LES record.
    H₁-zero-from-MV : Hzero A 0 → isSurjective (L.source-map 1) → Hzero P 1
    H₁-zero-from-MV a0 onto = exact-zero-map-middle
      {G = DirProd (H̃ᶜʷ B 1) (H̃ᶜʷ C 1)} {H = H̃ᶜʷ P 1} {K = H̃ᶜʷ A 0}
      (L.sum-map 1) (L.boundary 0) (L.exact-total 0 (4 , refl))
      (exact-after-surjective-zero
        {G = H̃ᶜʷ A 1} {H = DirProd (H̃ᶜʷ B 1) (H̃ᶜʷ C 1)} {K = H̃ᶜʷ P 1}
        (L.source-map 1) (L.sum-map 1) (L.exact-target 1 (3 , refl)) onto)
      (λ x → contr→zero (H̃ᶜʷ A 0) a0 (fst (L.boundary 0) x))

    source₁-onto-from-H₁-zero : Hzero P 1 → isSurjective (L.source-map 1)
    source₁-onto-from-H₁-zero p1 = exact-right-surjective
      {G = H̃ᶜʷ A 1} {H = DirProd (H̃ᶜʷ B 1) (H̃ᶜʷ C 1)} {K = H̃ᶜʷ P 1}
      (L.source-map 1) (L.sum-map 1) (L.exact-target 1 (3 , refl)) p1

    -- Convenient joint conclusions. The individual exports above have
    -- strictly smaller hypotheses and are preferable for separate uses.
    outer-mv-O : (N : ℕ) → 0 < N
      → (eA : GroupEquiv (H̃ᶜʷ A 3) ℤGroup)
      → (eC : GroupEquiv (H̃ᶜʷ C 3) ℤGroup)
      → ((x : fst (H̃ᶜʷ A 3)) → equivFun (fst eC)
           (fst (cellular-map A C 3 g) x) ≡ pos N · equivFun (fst eA) x)
      → Hzero B 4 → Hzero C 4 → Hzero B 3 → Hzero A 2
      → Hzero B 2 → Hzero C 2 → isInjective (L.source-map 1)
      → Hzero P 4 × GroupEquiv (H̃ᶜʷ P 3) (ℤGroup/ N) × Hzero P 2
    outer-mv-O N positive eA eC degree b4 c4 b3 a2 b2 c2 injective =
      H₄-zero-from-MV N positive eA eC degree b4 c4 ,
      H₃-iso-ℤ/N-from-MV N eA eC degree b3 a2 ,
      H₂-zero-from-MV b2 c2 injective

    outer-mv-I : (N : ℕ) → 0 < N
      → (eA : GroupEquiv (H̃ᶜʷ A 3) ℤGroup)
      → (eC : GroupEquiv (H̃ᶜʷ C 3) ℤGroup)
      → ((x : fst (H̃ᶜʷ A 3)) → equivFun (fst eC)
           (fst (cellular-map A C 3 g) x) ≡ pos N · equivFun (fst eA) x)
      → Hzero B 4 → Hzero C 4 → Hzero B 3 → Hzero A 2
      → Hzero B 2 → Hzero C 2
      → GroupEquiv (kerGroup (L.source-map 1)) (ℤGroup/ 2)
      → Hzero P 4 × GroupEquiv (H̃ᶜʷ P 3) (ℤGroup/ N)
        × GroupEquiv (H̃ᶜʷ P 2) (ℤGroup/ 2)
    outer-mv-I N positive eA eC degree b4 c4 b3 a2 b2 c2 kernel =
      H₄-zero-from-MV N positive eA eC degree b4 c4 ,
      H₃-iso-ℤ/N-from-MV N eA eC degree b3 a2 ,
      H₂-iso-ℤ/2-from-MV b2 c2 kernel
