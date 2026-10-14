{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.EO where

-- The Moore HIT S³ ∪₃ e⁴ contracts under degree-3 circle localization.
-- Its sphere is S₊ 3 = Susp (Susp S¹), and its attaching map is the
-- double suspension of Base.deg₁ 3. No separate CW cell-count certificate
-- is asserted here; contraction uses the mapping-space universal property.

open import DeloopS3.Local.Kernel
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Unit using (Unit ; tt ; isContr→≃Unit)
open import Cubical.HITs.Pushout.Base using (cofib ; inl)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
open import Cubical.Homotopy.Connected using
  ( isConnected ; isConnectedCofib ; isConnectedFunCancel'
  ; isConnected→isConnectedFun ; isConnectedSubtr )
import Cubical.HITs.PropositionalTruncation as PT

-- The S³ model is definitionally SphereFromCircle 2.
degree3-S³ : S₊ 3 → S₊ 3
degree3-S³ = degSphere 3 2

EO-cofibre : Type
EO-cofibre = cofib degree3-S³

-- The singleton-bouquet case, on UNTRUNCATED map spaces.
degree3-S³-local-equiv : LocalEquiv 3 degree3-S³
degree3-S³-local-equiv Z localZ = local-sphere localZ 2

-- The library indexes connectivity by hlevel: 4 means 2-connected.
-- A map from a 1-connected type to a 2-connected type is 1-connected;
-- its cofibre is 2-connected.  Both spheres here are 2-connected.
EO-cofibre-2-connected : isConnected 4 EO-cofibre
EO-cofibre-2-connected = isConnectedCofib 2
  (isConnectedFunCancel' degree3-S³ (λ _ → tt) 3
    (isConnected→isConnectedFun 4 (sphereConnected 3))
    (isConnected→isConnectedFun 3
      (isConnectedSubtr 3 1 (sphereConnected 3))))

-- The homology-free terminal contraction step.
EO-cofibre-local-contr : isContr (L 3 EO-cofibre)
EO-cofibre-local-contr =
  local-cofib-contr degree3-S³ degree3-S³-local-equiv

EO-cofibre-local≃Unit : L 3 (cofib degree3-S³) ≃ Unit
EO-cofibre-local≃Unit = isContr→≃Unit EO-cofibre-local-contr

-- The abstract model is represented by the degree-3 cofibre.
abstract
  E_O : Type
  E_O = EO-cofibre

  E_O≃cofibre : E_O ≃ cofib degree3-S³
  E_O≃cofibre = idEquiv EO-cofibre

  E_O-base : E_O
  E_O-base = inl tt

  E_O-2-connected : isConnected 4 E_O
  E_O-2-connected = EO-cofibre-2-connected

  E_O-local-contr : isContr (L 3 E_O)
  E_O-local-contr = EO-cofibre-local-contr

  -- Every map from this model to a degree-3-local target is constant.
  -- This also exposes the stronger mapping-space form of the contraction.
  E_O-const-isEquiv : {Z : Type} → Local 3 Z
    → isEquiv (λ (z : Z) (_ : E_O) → z)
  E_O-const-isEquiv {Z} localZ =
    cofib-const-isEquiv degree3-S³ (degree3-S³-local-equiv Z localZ)

E_O-local≃Unit : L 3 E_O ≃ Unit
E_O-local≃Unit = isContr→≃Unit E_O-local-contr

-- A mere equivalence with the model suffices, since contractibility is a
-- proposition. Bridge.Profile.Contraction constructs it for the O profile.
EO-model-contraction : {E : Type} → PT.∥ E ≃ E_O ∥₁
  → isContr (L 3 E)
EO-model-contraction {E} = PT.rec isPropIsContr λ e →
  subst (λ X → isContr (L 3 X)) (sym (ua e)) E_O-local-contr

