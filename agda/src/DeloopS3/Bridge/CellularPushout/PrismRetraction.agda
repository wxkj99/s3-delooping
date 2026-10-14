{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismRetraction where

-- Relative prism retraction and coefficient projection in every degree.
-- The inverse law uses degree functoriality and the two specified quotient
-- isomorphisms; the submodules supply quotient coherence.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.HITs.SphereBouquet.Degree
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.CW.Homotopy using (cofibIso)
open import DeloopS3.Bridge.CellularPushout.Seam using (module Seam)
open import Cubical.CW.Base
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.Strictification using (strictCWskel)
open import DeloopS3.Bridge.CellularPushout.PrismRetraction.Quotient using (module Quotient)
open import DeloopS3.Bridge.CellularPushout.PrismRetraction.Homotopy using (module Homotopy)

module PrismRetraction (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  open Quotient A B C f g public using (prismRet ; R ; R-VB ; R-VC)
  open Homotopy A B C f g public using (prismRet-H)
  open Seam A B C f g using (X ; Y ; HC ; KBouquet ; K)
  open Quotient A B C f g using (BQ)

  abstract
    R-K : (n : ℕ) → compGroupHom (K n) (R n) ≡ idGroupHom
    R-K n =
      sym (bouquetDegreeComp
        (Iso.fun (cofibIso n X) ∘ prismRet n ∘ Iso.inv (BQ Y (suc n)))
        (KBouquet n))
      ∙ cong bouquetDegree (funExt λ z →
          cong (Iso.fun (cofibIso n X) ∘ prismRet n)
            (Iso.ret (BQ Y (suc n)) (HC n (Iso.inv (cofibIso n X) z)))
          ∙ cong (Iso.fun (cofibIso n X))
              (funExt⁻ (prismRet-H n) (Iso.inv (cofibIso n X) z))
          ∙ Iso.sec (cofibIso n X) z)
      ∙ bouquetDegreeId
