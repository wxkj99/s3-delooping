{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Assembly.LocalCubes where

-- The mixed cube uses the literal upper span of ActualSpans.
open import Cubical.Foundations.Prelude renaming (J to pathJ)
open import Cubical.Foundations.Equiv
open import Cubical.HITs.Pushout.Base using (inl)
import DeloopS3.Sphere.TruncationCartesian as TC
import DeloopS3.Assembly.CartesianPushout as CP
open import DeloopS3.Assembly.ActualSpans public using
  (ShortCase; octa; icosa; R; N; r₀; n₀; F; f₀; F≃S³; A; C; q; p; E)
open import DeloopS3.Assembly.MixedTruncation public using
  (Case; BA; BC; u; qbar; pbar; Hq; Hp; left-cartesian; right-cartesian)

module LocalCube (c : Case) where
  module D = CP.CartesianPushout
    {ℓ = ℓ-zero} {A = A c} {B = R} {C = C c}
    {A' = BA c} {B' = N} {C' = BC c}
    (q c) (p c) (qbar c) (pbar c)
    TC.η₁ u TC.η₁ (Hq c) (Hp c)
    (left-cartesian c) (right-cartesian c)

  open D public using (P; t; J; J-isEquiv; λC; λC-isEquiv; descend-right)

P : Case → Type
P c = LocalCube.D.P c

t : (c : Case) → E c → P c
t c = LocalCube.D.t c

iG : (c : Case) → R → E c
iG c = inl {f = q c} {g = p c}

nG : (c : Case) → N → P c
nG c = inl {f = qbar c} {g = pbar c}

eG₀ : (c : Case) → E c
eG₀ c = iG c r₀

pG₀ : (c : Case) → P c
pG₀ c = nG c n₀

λG : (c : Case) → F → fiber (t c) (pG₀ c)
λG c (r , s) = iG c r , cong (nG c) s

abstract
  λG-isEquiv : (c : Case) → isEquiv (λG c)
  λG-isEquiv c = LocalCube.D.λB-isEquiv c n₀

  restriction-G : (c : Case)
    → TC.CartSquare (iG c) (nG c) u (t c) (λ _ → refl)
  restriction-G c = LocalCube.D.descend-left c

local-fibre : (c : Case) → F ≃ fiber (t c) (pG₀ c)
local-fibre c = λG c , λG-isEquiv c

-- Keep the specified J transparent: its first projection is definitionally t.
-- In particular, this is not an opaque replacement total-space equivalence.
total-space : (c : Case) → E c ≃ Σ (P c) (LocalCube.D.D c)
total-space c = LocalCube.J c , LocalCube.J-isEquiv c
