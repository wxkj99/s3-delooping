{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.HPInf.RelativeFracture where

-- The actual common-corner square is cartesian, including its chosen seam.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
  using (isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.HLevels using (isProp→isOfHLevelSuc)
open import Cubical.Foundations.Pointed using (typ)
import Cubical.HITs.Truncation as Tr
import Cubical.Homotopy.Connected as Connected
open import DeloopS3.Local.Base using (η)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (PB)
import DeloopS3.Sphere.TruncationCartesian as TC
import DeloopS3.Assembly.Final.Geometry as G
import DeloopS3.Assembly.MixedTruncation as Mixed
import DeloopS3.Assembly.ConnectivityGlue as Connectivity
import DeloopS3.HPInf.CommonSquare as Square
import DeloopS3.HPInf.PullbackFiber as PullbackFiber
import DeloopS3.HPInf.ActualFiberUnits as Units
import DeloopS3.HPInf.CartesianFromFibers as Cartesian
open import DeloopS3.HPInf.UnitFracture using (unit-aware-fracture)

module Arrow = PullbackFiber.Cospan
  (Square.TE G.octa) (Square.TE G.icosa) Square.TE*
  (typ (G.Q G.octa)) (typ (G.Q G.icosa)) (typ G.T)
  (Square.pL G.octa) (Square.pL G.icosa) Square.pL*
  (Square.v G.octa) (Square.v G.icosa)
  (fst (G.u G.octa)) (fst (G.u G.icosa)) Square.HO Square.HI

module At = Arrow.At
  (η {3} (G.b G.octa)) (η {10} (G.b G.icosa))
  (Square.base-seam G.n₀)

comparison : G.F → PB At.a At.b
comparison = equivFun At.fiber-equiv ∘ Units.kappa G.n₀

-- The supplied seam is extracted from the actual fiber map, not chosen afresh.
comparison-seam : (z : G.F) → At.a (Units.c3 z) ≡ At.b (Units.c10 z)
comparison-seam z = snd (snd (comparison z))

abstract
  comparison-isEquiv : isEquiv comparison
  comparison-isEquiv = unit-aware-fracture At.a At.b Units.c3 Units.c10
    comparison-seam Units.l3 Units.l10 Units.l30 Units.F-connected
    Units.extension-c3-isEquiv Units.extension-c10-isEquiv
    Units.extension-c30-isEquiv

  base-fiber-isEquiv : isEquiv (Units.kappa G.n₀)
  base-fiber-isEquiv = isEquiv[equivFunA≃B∘f]→isEquiv[f]
    (Units.kappa G.n₀) At.fiber-equiv comparison-isEquiv

  -- Eliminate only the proposition isEquiv, first over the connected R,
  -- then over its 2-truncation. No family of sphere coordinates is chosen.
  all-fibers-isEquiv : (n : G.N) → isEquiv (Units.kappa n)
  all-fibers-isEquiv = Tr.elim
    (λ n → isProp→isOfHLevelSuc 3 (isPropIsEquiv (Units.kappa n)))
    (Connected.isConnectedPoint.elim 1 Connectivity.R-connected
      (λ r → isPropIsEquiv (Units.kappa (Mixed.u r)))
      (G.r₀ , base-fiber-isEquiv))

  common-square-cartesian : TC.CartSquare Mixed.u Square.pT
    Square.alpha Square.j Square.H
  common-square-cartesian = Cartesian.cartesian-from-fibers
    Mixed.u Square.pT Square.alpha Square.j Square.H all-fibers-isEquiv
