{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.Algebra where

-- The normalized, singly augmented algebraic double mapping cylinder.
-- Library ChainComplex index 0 is the augmentation group; index (suc n)
-- is the ordinary n-cell group.  In particular the differential out of
-- ordinary 1-cells has NO source-augmentation coordinate.
--
-- Paper calculation: epsilon d(b,c,a) = epsilon_A(a)-epsilon_A(a).
-- In higher degrees the first two coordinates of d^2 are respectively
-- d_B^2 b + d_B f a - f d_A a and
-- d_C^2 c - d_C g a + g d_A a; the third is d_A^2 a.
-- This construction does not assert a geometric comparison.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology

open ChainComplex
open ChainComplexMap
open IsGroupHom

private
  variable
    ℓ : Level

-- Ordinary nonnegative chains, with one separately specified augmentation.
record Augmented (E : AbGroup ℓ) : Type (ℓ-suc ℓ) where
  field
    ordinary : ChainComplex ℓ
    ε : AbGroupHom (chain ordinary 0) E
    εd : compGroupHom (bdry ordinary 0) ε ≡ trivGroupHom

open Augmented public

augment : {E : AbGroup ℓ} → Augmented E → ChainComplex ℓ
chain (augment {E = E} X) zero = E
chain (augment X) (suc n) = chain (ordinary X) n
bdry (augment X) zero = ε X
bdry (augment X) (suc n) = bdry (ordinary X) n
bdry²=0 (augment X) zero = εd X
bdry²=0 (augment X) (suc n) = bdry²=0 (ordinary X) n

record AugmentedMap {E : AbGroup ℓ} (X Y : Augmented E) : Type ℓ where
  field
    ordinaryMap : ChainComplexMap (ordinary X) (ordinary Y)
    εcomm : compGroupHom (chainmap ordinaryMap 0) (ε Y) ≡ ε X

open AugmentedMap public

-- Small typed homomorphism combinators keep product conversion local.
fstHom : (X Y : AbGroup ℓ) → AbGroupHom (dirProdAb X Y) X
fstHom X Y = fst , makeIsGroupHom (λ _ _ → refl)

sndHom : (X Y : AbGroup ℓ) → AbGroupHom (dirProdAb X Y) Y
sndHom X Y = snd , makeIsGroupHom (λ _ _ → refl)

pairHom : {X Y Z : AbGroup ℓ} → AbGroupHom X Y → AbGroupHom X Z
  → AbGroupHom X (dirProdAb Y Z)
pairHom f g .fst x = fst f x , fst g x
pairHom f g .snd = makeIsGroupHom λ x y → ΣPathP (pres· (snd f) x y , pres· (snd g) x y)

abstract
  plusHomZero : {X Y : AbGroup ℓ} (h : AbGroupHom X Y) (y : fst Y)
    → AbGroupStr._+_ (snd Y) y (fst h (AbGroupStr.0g (snd X))) ≡ y
  plusHomZero {Y = Y} h y = cong (AbGroupStr._+_ (snd Y) y) (pres1 (snd h))
    ∙ AbGroupStr.+IdR (snd Y) y

  negHomZero : {X Y : AbGroup ℓ} (h : AbGroupHom X Y)
    → AbGroupStr.-_ (snd Y) (fst h (AbGroupStr.0g (snd X))) ≡ AbGroupStr.0g (snd Y)
  negHomZero {Y = Y} h = cong (AbGroupStr.-_ (snd Y)) (pres1 (snd h))
    ∙ GroupTheory.inv1g (AbGroup→Group Y)

  minusHomZero : {X Y : AbGroup ℓ} (h : AbGroupHom X Y) (y : fst Y)
    → AbGroupStr._+_ (snd Y) y (AbGroupStr.-_ (snd Y) (fst h (AbGroupStr.0g (snd X)))) ≡ y
  minusHomZero {Y = Y} h y = cong (AbGroupStr._+_ (snd Y) y) (negHomZero h)
    ∙ AbGroupStr.+IdR (snd Y) y

module DoubleCylinder {E : AbGroup ℓ} (A B C : Augmented E)
  (f : AugmentedMap A B) (g : AugmentedMap A C) where

  private
    aC = ordinary A
    bC = ordinary B
    cC = ordinary C
    F = chainmap (ordinaryMap f)
    G = chainmap (ordinaryMap g)
    module E = AbGroupStr (snd E)
    module AG (n : ℕ) = AbGroupStr (snd (chain aC n))
    module BG (n : ℕ) = AbGroupStr (snd (chain bC n))
    module CG (n : ℕ) = AbGroupStr (snd (chain cC n))

  cells₀ : AbGroup ℓ
  cells₀ = dirProdAb (chain bC 0) (chain cC 0)

  cells₊ : (n : ℕ) → AbGroup ℓ
  cells₊ n = dirProdAb (chain bC (suc n))
    (dirProdAb (chain cC (suc n)) (chain aC n))

  private
    bProj : (n : ℕ) → AbGroupHom (cells₊ n) (chain bC (suc n))
    bProj n = fstHom (chain bC (suc n)) (dirProdAb (chain cC (suc n)) (chain aC n))
    caProj : (n : ℕ) → AbGroupHom (cells₊ n) (dirProdAb (chain cC (suc n)) (chain aC n))
    caProj n = sndHom (chain bC (suc n)) (dirProdAb (chain cC (suc n)) (chain aC n))
    cProj : (n : ℕ) → AbGroupHom (cells₊ n) (chain cC (suc n))
    cProj n = compGroupHom (caProj n) (fstHom (chain cC (suc n)) (chain aC n))
    aProj : (n : ℕ) → AbGroupHom (cells₊ n) (chain aC n)
    aProj n = compGroupHom (caProj n) (sndHom (chain cC (suc n)) (chain aC n))

  bBoundary : (n : ℕ) → AbGroupHom (cells₊ n) (chain bC n)
  bBoundary n = addGroupHom (cells₊ n) (chain bC n)
    (compGroupHom (bProj n) (bdry bC n)) (compGroupHom (aProj n) (F n))

  cBoundary : (n : ℕ) → AbGroupHom (cells₊ n) (chain cC n)
  cBoundary n = subtrGroupHom (cells₊ n) (chain cC n)
    (compGroupHom (cProj n) (bdry cC n)) (compGroupHom (aProj n) (G n))

  aBoundary : (n : ℕ) → AbGroupHom (cells₊ (suc n)) (chain aC n)
  aBoundary n = negGroupHom (cells₊ (suc n)) (chain aC n)
    (compGroupHom (aProj (suc n)) (bdry aC n))

  groups : (n : ℕ) → AbGroup ℓ
  groups zero = E
  groups (suc zero) = cells₀
  groups (suc (suc n)) = cells₊ n

  differential : (n : ℕ) → AbGroupHom (groups (suc n)) (groups n)
  differential zero = addGroupHom cells₀ E
    (compGroupHom (fstHom (chain bC 0) (chain cC 0)) (ε B))
    (compGroupHom (sndHom (chain bC 0) (chain cC 0)) (ε C))
  differential (suc zero) = pairHom (bBoundary 0) (cBoundary 0)
  differential (suc (suc n)) = pairHom (bBoundary (suc n))
    (pairHom (cBoundary (suc n)) (aBoundary n))

  abstract
    augmentation-square : (x : fst (cells₊ 0))
      → fst (differential 0) (fst (differential 1) x) ≡ E.0g
    augmentation-square (b , c , a) =
      cong₂ E._+_
        (pres· (snd (ε B)) _ _
          ∙ cong₂ E._+_ (funExt⁻ (cong fst (εd B)) b)
                           (funExt⁻ (cong fst (εcomm f)) a)
          ∙ E.+IdL (fst (ε A) a))
        (pres· (snd (ε C)) _ _
          ∙ cong₂ E._+_ (funExt⁻ (cong fst (εd C)) c)
              (presinv (snd (ε C)) _
               ∙ cong E.-_ (funExt⁻ (cong fst (εcomm g)) a))
          ∙ E.+IdL (E.- fst (ε A) a))
      ∙ E.+InvR (fst (ε A) a)

    b-square : (n : ℕ) (b : fst (chain bC (suc (suc n))))
      (a : fst (chain aC (suc n)))
      → BG._+_ n
          (fst (bdry bC n) (BG._+_ (suc n) (fst (bdry bC (suc n)) b) (fst (F (suc n)) a)))
          (fst (F n) (AG.-_ n (fst (bdry aC n) a))) ≡ BG.0g n
    b-square n b a =
      cong₂ (BG._+_ n)
        (pres· (snd (bdry bC n)) _ _
          ∙ cong₂ (BG._+_ n) (funExt⁻ (cong fst (bdry²=0 bC n)) b)
              (funExt⁻ (cong fst (bdrycomm (ordinaryMap f) n)) a)
          ∙ BG.+IdL n (fst (F n) (fst (bdry aC n) a)))
        (presinv (snd (F n)) _)
      ∙ BG.+InvR n (fst (F n) (fst (bdry aC n) a))

    c-square : (n : ℕ) (c : fst (chain cC (suc (suc n))))
      (a : fst (chain aC (suc n)))
      → CG._+_ n
          (fst (bdry cC n) (CG._+_ (suc n) (fst (bdry cC (suc n)) c)
              (CG.-_ (suc n) (fst (G (suc n)) a))))
          (CG.-_ n (fst (G n) (AG.-_ n (fst (bdry aC n) a)))) ≡ CG.0g n
    c-square n c a =
      cong₂ (CG._+_ n)
        (pres· (snd (bdry cC n)) _ _
          ∙ cong₂ (CG._+_ n) (funExt⁻ (cong fst (bdry²=0 cC n)) c)
              (presinv (snd (bdry cC n)) _
                ∙ cong (CG.-_ n) (funExt⁻ (cong fst (bdrycomm (ordinaryMap g) n)) a))
          ∙ CG.+IdL n (CG.-_ n (fst (G n) (fst (bdry aC n) a))))
        (cong (CG.-_ n) (presinv (snd (G n)) _)
          ∙ GroupTheory.invInv (AbGroup→Group (chain cC n)) _)
      ∙ CG.+InvL n (fst (G n) (fst (bdry aC n) a))

    a-square : (n : ℕ) (a : fst (chain aC (suc (suc n))))
      → AG.-_ n (fst (bdry aC n) (AG.-_ (suc n) (fst (bdry aC (suc n)) a))) ≡ AG.0g n
    a-square n a = cong (AG.-_ n) (presinv (snd (bdry aC n)) _)
      ∙ GroupTheory.invInv (AbGroup→Group (chain aC n)) _
      ∙ funExt⁻ (cong fst (bdry²=0 aC n)) a

    differential² : (n : ℕ)
      → compGroupHom (differential (suc n)) (differential n) ≡ trivGroupHom
    differential² zero = GroupHom≡ (funExt augmentation-square)
    differential² (suc zero) = GroupHom≡ (funExt λ (b , c , a) → ΣPathP (b-square 0 b a , c-square 0 c a))
    differential² (suc (suc n)) = GroupHom≡ (funExt λ (b , c , a)
      → ΣPathP (b-square (suc n) b a , ΣPathP (c-square (suc n) c a , a-square n a)))

  DMC : ChainComplex ℓ
  chain DMC = groups
  bdry DMC = differential
  bdry²=0 DMC = differential²

  -- Genuine chain maps, identity on the ONE augmentation group.
  inclB-groups : (n : ℕ) → AbGroupHom (chain (augment B) n) (groups n)
  inclB-groups zero = idGroupHom
  inclB-groups (suc zero) = pairHom idGroupHom trivGroupHom
  inclB-groups (suc (suc n)) = pairHom idGroupHom (pairHom trivGroupHom trivGroupHom)

  inclC-groups : (n : ℕ) → AbGroupHom (chain (augment C) n) (groups n)
  inclC-groups zero = idGroupHom
  inclC-groups (suc zero) = pairHom trivGroupHom idGroupHom
  inclC-groups (suc (suc n)) = pairHom trivGroupHom (pairHom idGroupHom trivGroupHom)

  abstract
    inclB-comm : (n : ℕ)
      → compGroupHom (inclB-groups (suc n)) (differential n)
       ≡ compGroupHom (bdry (augment B) n) (inclB-groups n)
    inclB-comm zero = GroupHom≡ (funExt λ b → plusHomZero (ε C) (fst (ε B) b))
    inclB-comm (suc zero) = GroupHom≡ (funExt λ b → ΣPathP
      (plusHomZero (F 0) (fst (bdry bC 0) b)
      , minusHomZero (G 0) (fst (bdry cC 0) (CG.0g 1)) ∙ pres1 (snd (bdry cC 0))))
    inclB-comm (suc (suc n)) = GroupHom≡ (funExt λ b → ΣPathP
      (plusHomZero (F (suc n)) (fst (bdry bC (suc n)) b)
      , ΣPathP
        (minusHomZero (G (suc n)) (fst (bdry cC (suc n)) (CG.0g (suc (suc n))))
          ∙ pres1 (snd (bdry cC (suc n)))
        , negHomZero (bdry aC n))))

    inclC-comm : (n : ℕ)
      → compGroupHom (inclC-groups (suc n)) (differential n)
       ≡ compGroupHom (bdry (augment C) n) (inclC-groups n)
    inclC-comm zero = GroupHom≡ (funExt λ c
      → cong (λ z → E._+_ z (fst (ε C) c)) (pres1 (snd (ε B))) ∙ E.+IdL _)
    inclC-comm (suc zero) = GroupHom≡ (funExt λ c → ΣPathP
      (plusHomZero (F 0) (fst (bdry bC 0) (BG.0g 1)) ∙ pres1 (snd (bdry bC 0))
      , minusHomZero (G 0) (fst (bdry cC 0) c)))
    inclC-comm (suc (suc n)) = GroupHom≡ (funExt λ c → ΣPathP
      (plusHomZero (F (suc n)) (fst (bdry bC (suc n)) (BG.0g (suc (suc n))))
        ∙ pres1 (snd (bdry bC (suc n)))
      , ΣPathP
        (minusHomZero (G (suc n)) (fst (bdry cC (suc n)) c)
        , negHomZero (bdry aC n))))

  inclB : ChainComplexMap (augment B) DMC
  chainmap inclB = inclB-groups
  bdrycomm inclB = inclB-comm

  inclC : ChainComplexMap (augment C) DMC
  chainmap inclC = inclC-groups
  bdrycomm inclC = inclC-comm

  H̃DMC : (n : ℕ) → Group ℓ
  H̃DMC n = homology n DMC

  H̃inclB : (n : ℕ) → GroupHom (homology n (augment B)) (H̃DMC n)
  H̃inclB = chainComplexMap→HomologyMap inclB

  H̃inclC : (n : ℕ) → GroupHom (homology n (augment C)) (H̃DMC n)
  H̃inclC = chainComplexMap→HomologyMap inclC
