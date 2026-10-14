{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.HPInf.LocalExtension where

-- An actual fibre-unit comparison determines an equivalence after localization.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import DeloopS3.Local.Base using (L; η; Local)
open import DeloopS3.Local.RouteB2 using (SC; L-map)
import DeloopS3.Local.Base as Base
import DeloopS3.Local.RouteB2 as B2
open import DeloopS3.Local.Unique using (module Unique)
import DeloopS3.Assembly.LocalizationMaps as LM
import Cubical.HITs.Localization.Properties as Loc

abstract
  local-extension-isEquiv : {F E P : Type} (m : ℕ)
    (p : E → P) (b : P) (sc : SC P)
    (e : F ≃ fiber p b)
    (h : F → fiber (L-map m p) (η {m} b))
    (l : Local m (fiber (L-map m p) (η {m} b)))
    (β : (x : F) → h x ≡ B2.fiber-unit m p b (equivFun e x))
    → isEquiv (Loc.rec l h)
  local-extension-isEquiv {F} {E} {P} m p b sc e h l β =
    subst isEquiv (sym comparison) (snd extended-equiv)
    where
    extended-equiv : L m F ≃ fiber (L-map m p) (η {m} b)
    extended-equiv = compEquiv
      (L-map m (equivFun e) , LM.L-map-isEquiv m e)
      (B2.fiber-comparison m p b , B2.localization-preserves-fiber m p b sc)

    comparison : Loc.rec l h ≡ equivFun extended-equiv
    comparison = funExt (Unique.≡onη {F = Base.F m} l
      (Loc.rec l h) (equivFun extended-equiv) β)
