{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.HPInf.ActualFiberUnits where

-- Actual coordinate maps, retaining the common-square homotopy.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed using (typ)
open import Cubical.Foundations.GroupoidLaws using (cong-∙; lUnit)
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Homotopy.Connected using (isConnected; isConnectedRetractFromIso)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
open import DeloopS3.Local.Base using (η; Local)
import Cubical.HITs.Localization.Properties as Loc
import DeloopS3.Local.RouteB2 as B2
import DeloopS3.Assembly.Final.Geometry as G
import DeloopS3.Assembly.MixedTruncation as Mixed
import DeloopS3.Assembly.LocalCubes as LC
import DeloopS3.Assembly.StarCube as Star
import DeloopS3.HPInf.CommonSquare as C
import DeloopS3.HPInf.Inputs as Inputs
open import DeloopS3.HPInf.LocalExtension using (local-extension-isEquiv)

X3 X10 X30 : Type
X3 = fiber (C.pL G.octa) (η {3} {G.P G.octa} (G.b G.octa))
X10 = fiber (C.pL G.icosa) (η {10} {G.P G.icosa} (G.b G.icosa))
X30 = fiber C.pL* (η {30} {G.P*} G.b*)

kappa : (n : G.N) → fiber Mixed.u n → fiber C.pT (C.j n)
kappa n (r , q) = C.alpha r , C.H r ∙ cong C.j q

pr3 : C.B → typ (G.Q G.octa)
pr3 = fst

pr10 : C.B → typ (G.Q G.icosa)
pr10 = fst ∘ snd

c3 : G.F → X3
c3 (r , q) = fst (C.alpha r) , cong pr3 (C.H r ∙ cong C.j q)

c10 : G.F → X10
c10 (r , q) = fst (snd (C.alpha r)) , cong pr10 (C.H r ∙ cong C.j q)

a : X3 → X30
a (x , q) = C.v G.octa x , C.HO x ∙ cong (fst (G.u G.octa)) q

c30 : G.F → X30
c30 = a ∘ c3

abstract
  c3-beta : (z : G.F) → c3 z
    ≡ B2.fiber-unit 3 (G.p G.octa) (G.b G.octa) (LC.λG G.octa z)
  c3-beta (r , q) = ΣPathP (refl ,
    cong-∙ pr3 (C.H r) (cong C.j q)
    ∙ sym (lUnit (cong (η {3} {G.P G.octa}) (cong (G.jN G.octa) q))))

  c10-beta : (z : G.F) → c10 z
    ≡ B2.fiber-unit 10 (G.p G.icosa) (G.b G.icosa) (LC.λG G.icosa z)
  c10-beta (r , q) = ΣPathP (refl ,
    cong-∙ pr10 (C.H r) (cong C.j q)
    ∙ sym (lUnit (cong (η {10} {G.P G.icosa}) (cong (G.jN G.icosa) q))))

  star-unit : (z : G.F)
    → a (B2.fiber-unit 3 (G.p G.octa) (G.b G.octa) (LC.λG G.octa z))
      ≡ B2.fiber-unit 30 G.p* G.b* (Star.λ* z)
  star-unit (r , q) = ΣPathP (refl ,
    cong (λ h → h ∙ cong (η {30} {G.P*}) (cong (G.kP G.octa ∘ G.jN G.octa) q))
      (C.O.HᴸG-β (G.iR G.octa r))
    ∙ sym (lUnit (cong (η {30} {G.P*}) (cong (G.kP G.octa ∘ G.jN G.octa) q))))

  c30-beta : (z : G.F) → c30 z
    ≡ B2.fiber-unit 30 G.p* G.b* (Star.λ* z)
  c30-beta z = cong a (c3-beta z) ∙ star-unit z

l3 : Local 3 X3
l3 = B2.fiber-target-local 3 (G.p G.octa) (G.b G.octa)

l10 : Local 10 X10
l10 = B2.fiber-target-local 10 (G.p G.icosa) (G.b G.icosa)

l30 : Local 30 X30
l30 = B2.fiber-target-local 30 G.p* G.b*

abstract
  extension-c3-isEquiv : isEquiv (Loc.rec l3 c3)
  extension-c3-isEquiv = local-extension-isEquiv
    3 (G.p G.octa) (G.b G.octa) (Inputs.base-SC G.octa)
    (G.λG G.octa) c3 l3 c3-beta

  extension-c10-isEquiv : isEquiv (Loc.rec l10 c10)
  extension-c10-isEquiv = local-extension-isEquiv
    10 (G.p G.icosa) (G.b G.icosa) (Inputs.base-SC G.icosa)
    (G.λG G.icosa) c10 l10 c10-beta

  extension-c30-isEquiv : isEquiv (Loc.rec l30 c30)
  extension-c30-isEquiv = local-extension-isEquiv
    30 G.p* G.b* Inputs.star-base-SC G.λ* c30 l30 c30-beta

  F-connected : isConnected 4 G.F
  F-connected = isConnectedRetractFromIso 4 (equivToIso G.σ) (sphereConnected 3)
