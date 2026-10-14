{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Map where

-- The actual seam defines an all-degree chain map.
-- Its equivalence is established in Comparison.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.ChainComplex
open import Cubical.CW.Strictification using (strictCWskel)
open import DeloopS3.Bridge.CellularPushout using (module CellularPushout)
open import DeloopS3.Bridge.CellularPushout.Algebra
open import DeloopS3.Bridge.CellularPushout.Cellular
open import DeloopS3.Bridge.CellularPushout.Seam using (module Seam)

open ChainComplex
open ChainComplexMap
open IsGroupHom

module PrismMap (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  module CP = CellularPushout A B C f g
  open Seam A B C f g using (X ; Y ; YB ; YC ; K ; VB ; VC ; K-boundary₀ ; K-boundary₊)

  actual : ChainComplex ℓ-zero
  actual = CW-AugChainComplex Y

  private
    module T (n : ℕ) = AbGroupStr (snd (chain actual n))
    b₀ = fstHom (Z YB 0) (Z YC 0)
    c₀ = sndHom (Z YB 0) (Z YC 0)

  q : (i : ℕ) → AbGroupHom (chain CP.DMC i) (chain actual i)
  q zero = idGroupHom
  q (suc zero) = addGroupHom (chain CP.DMC 1) (chain actual 1)
    (compGroupHom b₀ (VB 0)) (compGroupHom c₀ (VC 0))
  q (suc (suc n)) = addGroupHom (chain CP.DMC (suc (suc n))) (chain actual (suc (suc n)))
    (addGroupHom (chain CP.DMC (suc (suc n))) (chain actual (suc (suc n)))
      (compGroupHom (fstHom (Z YB (suc n)) (dirProdAb (Z YC (suc n)) (Z X n))) (VB (suc n)))
      (compGroupHom
        (compGroupHom (sndHom (Z YB (suc n)) (dirProdAb (Z YC (suc n)) (Z X n)))
          (fstHom (Z YC (suc n)) (Z X n))) (VC (suc n))))
    (compGroupHom
      (compGroupHom (sndHom (Z YB (suc n)) (dirProdAb (Z YC (suc n)) (Z X n)))
        (sndHom (Z YC (suc n)) (Z X n))) (K n))

  abstract
    q-augmentation : compGroupHom (q 1) (bdry actual 0)
      ≡ compGroupHom (bdry CP.DMC 0) (q 0)
    q-augmentation = GroupHom≡ (funExt λ (b , c) →
      pres· (snd (bdry actual 0)) _ _
      ∙ cong₂ (T._+_ 0)
        (funExt⁻ (cong fst (cellular-augmentation CP.vertexB-cell)) b)
        (funExt⁻ (cong fst (cellular-augmentation CP.vertexC-cell)) c))

    q-edge : compGroupHom (q 2) (bdry actual 1)
      ≡ compGroupHom (bdry CP.DMC 1) (q 1)
    q-edge = GroupHom≡ (funExt λ (b , c , a) →
      pres· (snd (∂ Y 0)) _ _
      ∙ cong₂ (T._+_ 1)
        (pres· (snd (∂ Y 0)) _ _
          ∙ cong₂ (T._+_ 1)
            (funExt⁻ (cong fst (cellular-boundary CP.vertexB-cell 0)) b)
            (funExt⁻ (cong fst (cellular-boundary CP.vertexC-cell 0)) c))
        (funExt⁻ (cong fst K-boundary₀) a)
      ∙ AbGroupTheory.comm-4 (chain actual 1) _ _ _ _
      ∙ cong₂ (T._+_ 1)
        (sym (pres· (snd (VB 0)) _ _))
        (cong (T._+_ 1 _) (sym (presinv (snd (VC 0)) _))
          ∙ sym (pres· (snd (VC 0)) _ _)))

    q-higher : (n : ℕ)
      → compGroupHom (q (suc (suc (suc n)))) (bdry actual (suc (suc n)))
       ≡ compGroupHom (bdry CP.DMC (suc (suc n))) (q (suc (suc n)))
    q-higher n = GroupHom≡ (funExt λ (b , c , a) →
      pres· (snd (∂ Y (suc n))) _ _
      ∙ cong₂ (T._+_ (suc (suc n)))
        (pres· (snd (∂ Y (suc n))) _ _
          ∙ cong₂ (T._+_ (suc (suc n)))
            (funExt⁻ (cong fst (cellular-boundary CP.vertexB-cell (suc n))) b)
            (funExt⁻ (cong fst (cellular-boundary CP.vertexC-cell (suc n))) c))
        (funExt⁻ (cong fst (K-boundary₊ n)) a)
      ∙ T.+Assoc (suc (suc n)) _ _ _
      ∙ cong₂ (T._+_ (suc (suc n)))
        (AbGroupTheory.comm-4 (chain actual (suc (suc n))) _ _ _ _
          ∙ cong₂ (T._+_ (suc (suc n)))
            (sym (pres· (snd (VB (suc n))) _ _))
            (cong (T._+_ (suc (suc n)) _) (sym (presinv (snd (VC (suc n))) _))
              ∙ sym (pres· (snd (VC (suc n))) _ _)))
        (sym (presinv (snd (K n)) _)))

  q-chain : ChainComplexMap CP.DMC actual
  chainmap q-chain = q
  bdrycomm q-chain zero = q-augmentation
  bdrycomm q-chain (suc zero) = q-edge
  bdrycomm q-chain (suc (suc n)) = q-higher n

  vertexB-chain : ChainComplexMap (CW-AugChainComplex YB) actual
  chainmap vertexB-chain zero = idGroupHom
  chainmap vertexB-chain (suc n) = VB n
  bdrycomm vertexB-chain zero = cellular-augmentation CP.vertexB-cell
    ∙ sym (compGroupHomId (augmentation.ϵ YB))
  bdrycomm vertexB-chain (suc n) = cellular-boundary CP.vertexB-cell n

  vertexC-chain : ChainComplexMap (CW-AugChainComplex YC) actual
  chainmap vertexC-chain zero = idGroupHom
  chainmap vertexC-chain (suc n) = VC n
  bdrycomm vertexC-chain zero = cellular-augmentation CP.vertexC-cell
    ∙ sym (compGroupHomId (augmentation.ϵ YC))
  bdrycomm vertexC-chain (suc n) = cellular-boundary CP.vertexC-cell n

  abstract
    q-inclB : (i : ℕ) → compGroupHom (chainmap CP.inclB i) (q i)
      ≡ chainmap vertexB-chain i
    q-inclB zero = GroupHom≡ refl
    q-inclB (suc zero) = GroupHom≡ (funExt λ b → plusHomZero (VC 0) _)
    q-inclB (suc (suc n)) = GroupHom≡ (funExt λ b →
      plusHomZero (K n) _ ∙ plusHomZero (VC (suc n)) _)

    q-inclC : (i : ℕ) → compGroupHom (chainmap CP.inclC i) (q i)
      ≡ chainmap vertexC-chain i
    q-inclC zero = GroupHom≡ refl
    q-inclC (suc zero) = GroupHom≡ (funExt λ c →
      cong (λ z → T._+_ 1 z (fst (VC 0) c)) (pres1 (snd (VB 0))) ∙ T.+IdL 1 _)
    q-inclC (suc (suc n)) = GroupHom≡ (funExt λ c → plusHomZero (K n) _
      ∙ cong (λ z → T._+_ (suc (suc n)) z (fst (VC (suc n)) c)) (pres1 (snd (VB (suc n))))
      ∙ T.+IdL (suc (suc n)) _)

    q-vertexB : compChainMap CP.inclB q-chain ≡ vertexB-chain
    q-vertexB = ChainComplexMap≡ q-inclB

    q-vertexC : compChainMap CP.inclC q-chain ≡ vertexC-chain
    q-vertexC = ChainComplexMap≡ q-inclC
