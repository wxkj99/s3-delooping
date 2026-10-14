{-# OPTIONS --cubical --safe --guardedness #-}
module DeloopS3.Assembly.Final.Geometry where

-- Adapters to the actual mixed τ-bottom cubes with upper spaces
-- ActualSpans.E. StarCube retains the strict seam and pointings.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Data.Nat using (ℕ)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (IsoS³S3)
import DeloopS3.Assembly.ActualSpans as Actual
open Actual public using (ShortCase ; octa ; icosa ; R ; N ; r₀ ; n₀ ; F ; f₀ ; E)
import DeloopS3.Assembly.LocalCubes as LC
open LC public using (P) renaming (t to p ; iG to iR ; nG to jN ; eG₀ to e₀ ; pG₀ to b)
import DeloopS3.Assembly.StarCube as Star
open Star public using (E* ; P*) renaming (t* to p* ; e*₀ to e* ; p*₀ to b*)
import DeloopS3.Local.Base as Loc
open import DeloopS3.Local.RouteB2.Common using (L-map)
open import DeloopS3.Local.Fracture.Fracture.Maps using (ι_m ; ι_n)
open import DeloopS3.Local.EI using (local-factor)
import DeloopS3.Assembly.LocalizationMaps as LM

kE : (c : ShortCase) → E c → E*
kE octa = Star.kEO
kE icosa = Star.kEI
kP : (c : ShortCase) → P c → P*
kP octa = Star.kPO
kP icosa = Star.kPI

-- The I-side path is essential; replacing it by refl loses monodromy data.
boundary : (c : ShortCase) → kP c (b c) ≡ b*
boundary octa = Star.bO
boundary icosa = Star.bI

Fib : ShortCase → Type
Fib c = fiber (p c) (b c)
Fib* : Type
Fib* = fiber p* b*

λG : (c : ShortCase) → F ≃ Fib c
λG = LC.local-fibre
λ* : F ≃ Fib*
λ* = Star.λ* , Star.λ*-isEquiv

-- Actual maps of the fibre sequences, with normalized vertex squares.
U : (c : ShortCase) → Fib c → Fib*
U octa = Star.UO
U icosa = Star.UI

-- One common UNPOINTED sphere chart; pointedness is supplied only by DefB
-- at the final step, so no path from an arbitrary sphere point is assumed.
abstract
  σ : F ≃ S₊ 3
  σ = compEquiv Actual.F≃S³ (isoToEquiv IsoS³S3)
χ : (c : ShortCase) → Fib c ≃ S₊ 3
χ c = compEquiv (invEquiv (λG c)) σ
χ* : Fib* ≃ S₊ 3
χ* = compEquiv (invEquiv λ*) σ

m : ShortCase → ℕ
m octa = 3
m icosa = 10

ι : (c : ShortCase) (X : Type) → Loc.L (m c) X → Loc.L 30 X
ι octa X = ι_m 3 10 X
ι icosa X = ι_n 3 10 X

abstract
  transfer : (c : ShortCase) (Z : Type) → Loc.Local 30 Z → Loc.Local (m c) Z
  transfer octa Z = local-factor {m = 30} {d = 3} {b = 10} {Z = Z} refl
  transfer icosa Z = local-factor {m = 30} {d = 10} {b = 3} {Z = Z} refl

ι-β : (c : ShortCase) (X : Type) (x : X)
  → ι c X (Loc.η {m c} {X} x) ≡ Loc.η {30} {X} x
ι-β octa X x = refl
ι-β icosa X x = refl

Q : ShortCase → Pointed ℓ-zero
Q c = Loc.L (m c) (P c) , Loc.η {m c} {P c} (b c)
T : Pointed ℓ-zero
T = Loc.L 30 P* , Loc.η {30} {P*} b*

u : (c : ShortCase) → Q c →∙ T
u octa = LM.overlap-map₃ {A = P octa} {B = P*} (kP octa) , refl
u icosa = LM.overlap-map₁₀ {A = P icosa} {B = P*} (kP icosa) ,
  cong (Loc.η {30} {P*}) (boundary icosa)

ι-natural : (c : ShortCase) {A B : Type} (f : A → B)
  → L-map 30 {A = A} {B = B} f ∘ ι c A
    ≡ ι c B ∘ L-map (m c) {A = A} {B = B} f
ι-natural octa f = LM.ι₃-natural f
ι-natural icosa f = LM.ι₁₀-natural f
