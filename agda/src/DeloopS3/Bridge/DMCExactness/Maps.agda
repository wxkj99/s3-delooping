{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Maps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
import Cubical.HITs.SetQuotients as SQ
open import DeloopS3.Bridge.CellularPushout.Algebra
open import DeloopS3.Bridge.DMCExactness.Quotient

open ChainComplex
open ChainComplexMap
open IsGroupHom
private variable ℓ : Level

module Laws (G : AbGroup ℓ) where
  open AbGroupStr (snd G)
  open GroupTheory (AbGroup→Group G)
  abstract
    neg-zero : {x : fst G} → - x ≡ 0g → x ≡ 0g
    neg-zero {x} p = sym (invInv x) ∙ cong -_ p ∙ inv1g
    neg-of-zero : {x : fst G} → x ≡ 0g → - x ≡ 0g
    neg-of-zero p = cong -_ p ∙ inv1g
    sum-right-zero : {x y : fst G} → x + y ≡ 0g → y ≡ - x
    sum-right-zero = invUniqueR

augmentMap : {E : AbGroup ℓ} {A B : Augmented E}
  → AugmentedMap A B → ChainComplexMap (augment A) (augment B)
chainmap (augmentMap f) zero = idGroupHom
chainmap (augmentMap f) (suc n) = chainmap (ordinaryMap f) n
bdrycomm (augmentMap f) zero = GroupHom≡ (cong fst (εcomm f))
bdrycomm (augmentMap f) (suc n) = bdrycomm (ordinaryMap f) n

module ConeMaps {E : AbGroup ℓ} (A B C : Augmented E)
  (f : AugmentedMap A B) (g : AugmentedMap A C) where
  module M = DoubleCylinder A B C f g
  D aC bC cC : ChainComplex ℓ
  D = M.DMC
  aC = ordinary A
  bC = ordinary B
  cC = ordinary C
  F : (n : ℕ) → AbGroupHom (chain aC n) (chain bC n)
  F = chainmap (ordinaryMap f)
  G : (n : ℕ) → AbGroupHom (chain aC n) (chain cC n)
  G = chainmap (ordinaryMap g)
  module AG (n : ℕ) = AbGroupStr (snd (chain aC n))
  module BG (n : ℕ) = AbGroupStr (snd (chain bC n))
  module CG (n : ℕ) = AbGroupStr (snd (chain cC n))
  module EG = AbGroupStr (snd E)
  module HA (n : ℕ) = Homology (augment A) n
  module HB (n : ℕ) = Homology (augment B) n
  module HC (n : ℕ) = Homology (augment C) n
  module HD (n : ℕ) = Homology D n

  abstract
    augmentation-source : (b : fst (chain bC 1)) (a : fst (chain aC 0))
      → fst (ε B) (BG._+_ 0 (fst (bdry bC 0) b) (fst (F 0) a)) ≡ fst (ε A) a
    augmentation-source b a = pres· (snd (ε B)) _ _
      ∙ cong₂ EG._+_ (funExt⁻ (cong fst (εd B)) b)
          (funExt⁻ (cong fst (εcomm f)) a)
      ∙ EG.+IdL _

    project-cycle : (n : ℕ) (z : HD.Cycle (suc n))
      → fst (bdry (augment A) n) (snd (snd (fst z)))
       ≡ AbGroupStr.0g (snd (chain (augment A) n))
    project-cycle zero ((b , c , a) , p) =
      sym (augmentation-source b a) ∙ cong (fst (ε B)) (cong fst p) ∙ pres1 (snd (ε B))
    project-cycle (suc n) (z , p) = Laws.neg-zero (chain aC n) (cong (snd ∘ snd) p)

  projection : (n : ℕ) → GroupHom (HD.Z (suc n)) (HA.Z n)
  fst (projection n) z = snd (snd (fst z)) , project-cycle n z
  snd (projection n) = makeIsGroupHom λ x y → HA.cycle-path n refl

  abstract
    projection-boundary : (n : ℕ) (v : fst (chain D (suc (suc (suc n)))))
      → HA.boundary n (AG.-_ (suc n) (snd (snd v)))
       ≡ fst (projection n) (HD.boundary (suc n) v)
    projection-boundary n v = HA.cycle-path n (presinv (snd (bdry aC n)) _)

  -- Positive sign: [(b,c,a)] is sent to [a]. A cone boundary projects
  -- to d_A(-v), explaining the minus sign in the boundary lift.
  δ : (n : ℕ) → GroupHom (HD.H (suc n)) (HA.H n)
  δ n = Descent.induced (projection n) (λ v → AG.-_ (suc n) (snd (snd v)))
    (projection-boundary n)

  target : (n : ℕ) → AbGroup ℓ
  target n = dirProdAb (HB.HAb n) (HC.HAb n)

  sumH : (n : ℕ) → GroupHom (AbGroup→Group (target n)) (HD.H n)
  sumH n = addGroupHom (target n) (HD.HAb n)
    (compGroupHom (fstHom (HB.HAb n) (HC.HAb n)) (M.H̃inclB n))
    (compGroupHom (sndHom (HB.HAb n) (HC.HAb n)) (M.H̃inclC n))

  fH : (n : ℕ) → GroupHom (HA.H n) (HB.H n)
  fH = chainComplexMap→HomologyMap (augmentMap f)
  gH : (n : ℕ) → GroupHom (HA.H n) (HC.H n)
  gH = chainComplexMap→HomologyMap (augmentMap g)

  spanH : (n : ℕ) → GroupHom (HA.H n) (AbGroup→Group (target n))
  spanH n = pairHom (fH n) (negGroupHom (HA.HAb n) (HC.HAb n) (gH n))

  fCycle : (n : ℕ) → HA.Cycle n → HB.Cycle n
  fCycle n (a , p) = fst (F n) a ,
    funExt⁻ (cong fst (bdrycomm (augmentMap f) n)) a
      ∙ cong (fst (chainmap (augmentMap f) n)) p
      ∙ pres1 (snd (chainmap (augmentMap f) n))

  minusGCycle : (n : ℕ) → HA.Cycle n → HC.Cycle n
  minusGCycle n (a , p) = CG.-_ n (fst (G n) a) ,
    presinv (snd (bdry (augment C) n)) _
      ∙ Laws.neg-of-zero (chain (augment C) n)
        (funExt⁻ (cong fst (bdrycomm (augmentMap g) n)) a
          ∙ cong (fst (chainmap (augmentMap g) n)) p
          ∙ pres1 (snd (chainmap (augmentMap g) n)))

  embed : (n : ℕ) → fst (chain bC n) → fst (chain cC n)
    → fst (chain D (suc n))
  embed zero b c = b , c
  embed (suc n) b c = b , c , AG.0g n

  embedCycle : (n : ℕ) → HB.Cycle n → HC.Cycle n → HD.Cycle n
  embedCycle n b c = GroupStr._·_ (snd (HD.Z n))
    (fst (chainmap M.inclB (suc n)) (fst b) ,
      funExt⁻ (cong fst (bdrycomm M.inclB n)) (fst b)
        ∙ cong (fst (chainmap M.inclB n)) (snd b) ∙ pres1 (snd (chainmap M.inclB n)))
    (fst (chainmap M.inclC (suc n)) (fst c) ,
      funExt⁻ (cong fst (bdrycomm M.inclC n)) (fst c)
        ∙ cong (fst (chainmap M.inclC n)) (snd c) ∙ pres1 (snd (chainmap M.inclC n)))

  abstract
    embedCycle-coordinates : (n : ℕ) (b : HB.Cycle n) (c : HC.Cycle n)
      → fst (embedCycle n b c) ≡ embed n (fst b) (fst c)
    embedCycle-coordinates zero b c = ΣPathP (BG.+IdR 0 _ , CG.+IdL 0 _)
    embedCycle-coordinates (suc n) b c =
      ΣPathP (BG.+IdR (suc n) _ , ΣPathP (CG.+IdL (suc n) _ , AG.+IdL n _))

    sumH-β : (n : ℕ) (b : HB.Cycle n) (c : HC.Cycle n)
      → fst (sumH n) (HB.class n b , HC.class n c) ≡ HD.class n (embedCycle n b c)
    sumH-β n b c = HD.class-path n refl

    spanH-β : (n : ℕ) (a : HA.Cycle n)
      → fst (spanH n) (HA.class n a)
       ≡ (HB.class n (fCycle n a) , HC.class n (minusGCycle n a))
    spanH-β n a = ΣPathP (HB.class-path n refl , HC.class-path n refl)

    δ-β : (n : ℕ) (z : HD.Cycle (suc n))
      → fst (δ n) (HD.class (suc n) z) ≡ HA.class n (fst (projection n) z)
    δ-β n z = refl
