{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout where

-- Normalized double mapping cylinder with differential (db+fa, dc-ga, -da),
-- one augmentation, vertex chain maps, and unsigned cell coordinates.
-- The augmentation comparison covers ordinary degrees -1 and 0;
-- PrismChains supplies the all-degree triangular chain equivalence.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base using (Group₀)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Finite
open import Cubical.Algebra.ChainComplex.Homology
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.ChainComplex
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import DeloopS3.Bridge.CellularPushout.Algebra
open import DeloopS3.Bridge.CellularPushout.Cellular
open import DeloopS3.Bridge.CellularPushout.CellGroups
open import DeloopS3.Bridge.CellularPushout.Vertices using (module Vertices)

open ChainComplex
open ChainComplexMap
open finChainComplexMap

module CellularPushout (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where

  module P = CWPushout ℓ-zero A B C f g
  open Vertices A B C f g public
  module Model = DoubleCylinder
    (CW-augmented P.B) (CW-augmented P.C) (CW-augmented P.D)
    (cellular-augmented-map P.f) (cellular-augmented-map P.g)

  DMC : ChainComplex ℓ-zero
  DMC = Model.DMC

  -- Chain maps from the actual vertex cellular complexes into the DMC.
  inclB : ChainComplexMap (CW-AugChainComplex P.C) DMC
  chainmap inclB zero = Model.inclB-groups 0
  chainmap inclB (suc zero) = Model.inclB-groups 1
  chainmap inclB (suc (suc n)) = Model.inclB-groups (suc (suc n))
  bdrycomm inclB zero = Model.inclB-comm 0
  bdrycomm inclB (suc zero) = Model.inclB-comm 1
  bdrycomm inclB (suc (suc n)) = Model.inclB-comm (suc (suc n))

  inclC : ChainComplexMap (CW-AugChainComplex P.D) DMC
  chainmap inclC zero = Model.inclC-groups 0
  chainmap inclC (suc zero) = Model.inclC-groups 1
  chainmap inclC (suc (suc n)) = Model.inclC-groups (suc (suc n))
  bdrycomm inclC zero = Model.inclC-comm 0
  bdrycomm inclC (suc zero) = Model.inclC-comm 1
  bdrycomm inclC (suc (suc n)) = Model.inclC-comm (suc (suc n))

  H̃DMC : (n : Fin 6) → Group₀
  H̃DMC n = homology (fst n) DMC

  H̃inclB : (n : Fin 6) → GroupHom (H̃ˢᵏᵉˡ P.C (fst n)) (H̃DMC n)
  H̃inclB n = chainComplexMap→HomologyMap inclB (fst n)

  H̃inclC : (n : Fin 6) → GroupHom (H̃ˢᵏᵉˡ P.D (fst n)) (H̃DMC n)
  H̃inclC n = chainComplexMap→HomologyMap inclC (fst n)

  -- There is exactly one copy of Z below the ordinary zero-cell group.
  DMC-augmentation-group : chain DMC 0 ≡ ℤ[Fin 1 ]
  DMC-augmentation-group = refl

  DMC-d² : (n : ℕ)
    → compGroupHom (bdry DMC (suc n)) (bdry DMC n) ≡ trivGroupHom
  DMC-d² = Model.differential²

  -- Explicit formula API. Here Aₙ/Bₙ/Cₙ are ordinary cell groups,
  -- whereas the library's ChainComplex indices are shifted by one.
  Aₙ Bₙ Cₙ : (n : ℕ) → AbGroup ℓ-zero
  Aₙ n = chain (CW-ordinary P.B) n
  Bₙ n = chain (CW-ordinary P.C) n
  Cₙ n = chain (CW-ordinary P.D) n

  f_* : (n : ℕ) → AbGroupHom (Aₙ n) (Bₙ n)
  f_* = cellular-coefficients P.f

  g_* : (n : ℕ) → AbGroupHom (Aₙ n) (Cₙ n)
  g_* = cellular-coefficients P.g

  DMC-cells₀ : chain DMC 1 ≡ dirProdAb (Bₙ 0) (Cₙ 0)
  DMC-cells₀ = refl

  DMC-cells₊ : (n : ℕ)
    → chain DMC (suc (suc n)) ≡ dirProdAb (Bₙ (suc n)) (dirProdAb (Cₙ (suc n)) (Aₙ n))
  DMC-cells₊ n = refl

  private
    module AG (n : ℕ) = AbGroupStr (snd (Aₙ n))
    module BG (n : ℕ) = AbGroupStr (snd (Bₙ n))
    module CG (n : ℕ) = AbGroupStr (snd (Cₙ n))
    module ZG = AbGroupStr (snd ℤ[Fin 1 ])

  DMC-ε : (b : fst (Bₙ 0)) (c : fst (Cₙ 0))
    → fst (bdry DMC 0) (b , c)
     ≡ ZG._+_ (fst (augmentation.ϵ P.C) b) (fst (augmentation.ϵ P.D) c)
  DMC-ε b c = refl

  DMC-∂₁ : (b : fst (Bₙ 1)) (c : fst (Cₙ 1)) (a : fst (Aₙ 0))
    → fst (bdry DMC 1) (b , c , a)
     ≡ (BG._+_ 0 (fst (∂ P.C 0) b) (fst (f_* 0) a)
       , CG._+_ 0 (fst (∂ P.D 0) c) (CG.-_ 0 (fst (g_* 0) a)))
  DMC-∂₁ b c a = refl

  DMC-∂₊ : (n : ℕ) (b : fst (Bₙ (suc (suc n))))
    (c : fst (Cₙ (suc (suc n)))) (a : fst (Aₙ (suc n)))
    → fst (bdry DMC (suc (suc n))) (b , c , a)
     ≡ (BG._+_ (suc n) (fst (∂ P.C (suc n)) b) (fst (f_* (suc n)) a)
       , CG._+_ (suc n) (fst (∂ P.D (suc n)) c) (CG.-_ (suc n) (fst (g_* (suc n)) a))
       , AG.-_ n (fst (∂ P.B n) a))
  DMC-∂₊ n b c a = refl

  -- Unsigned cell-coordinate equivalences, rather than chain equivalences.
  -- Positive-degree cells have library order ((B + A[-1]) + C).
  pushout-cell-groups : (n : ℕ)
    → AbGroupEquiv (chain (CW-AugChainComplex P.pushoutSkel) n) (chain DMC n)
  pushout-cell-groups zero = idEquiv _ , snd (idGroupHom {G = AbGroup→Group ℤ[Fin 1 ]})
  pushout-cell-groups (suc zero) = Split₂.splitEquiv (snd P.C .fst 0) (snd P.D .fst 0)
  pushout-cell-groups (suc (suc n)) = Split₃.splitEquiv
    (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n))

  pushout-cell-map : (n : ℕ)
    → AbGroupHom (chain (CW-AugChainComplex P.pushoutSkel) n) (chain DMC n)
  pushout-cell-map n = GroupEquiv→GroupHom (pushout-cell-groups n)

  abstract
    pushout-augmentation :
      compGroupHom (pushout-cell-map 1) (bdry DMC 0)
      ≡ compGroupHom (bdry (CW-AugChainComplex P.pushoutSkel) 0) (pushout-cell-map 0)
    pushout-augmentation =
      cong (compGroupHom (pushout-cell-map 1))
        (cong₂ (addGroupHom Model.cells₀ ℤ[Fin 1 ])
          (cong (compGroupHom (fstHom (chain (CW-ordinary P.C) 0) (chain (CW-ordinary P.D) 0)))
            (augmentation.ϵ-alt P.C))
          (cong (compGroupHom (sndHom (chain (CW-ordinary P.C) 0) (chain (CW-ordinary P.D) 0)))
            (augmentation.ϵ-alt P.D)))
      ∙ Split₂.split-augmentation (snd P.C .fst 0) (snd P.D .fst 0)
      ∙ sym (augmentation.ϵ-alt P.pushoutSkel)
      ∙ sym (compGroupHomId (augmentation.ϵ P.pushoutSkel))

  -- Comparison in augmented indices 0 and 1, i.e. ordinary degrees -1 and 0.
  -- Computing H̃₀ also requires incoming 1-cells (augmented index 2).
  pushout-chains₋₁,₀ : CW-AugChainComplex P.pushoutSkel ≃⟨ 1 ⟩Chain DMC
  fchainmap (fst pushout-chains₋₁,₀) n = pushout-cell-map (fst n)
  fbdrycomm (fst pushout-chains₋₁,₀) (zero , _) = pushout-augmentation
  snd pushout-chains₋₁,₀ n = snd (fst (pushout-cell-groups (fst n)))

