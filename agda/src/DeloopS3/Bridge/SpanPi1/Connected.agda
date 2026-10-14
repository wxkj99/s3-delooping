{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.SpanPi1.Connected where

-- Connectedness of the actual three-torus Seifert pushouts and RP 2,
-- without a presentation complex or binary-group enumeration.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (invIso)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (false)
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Sum using (_⊎_) renaming (inl to left; inr to right)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.RPn.Base using (cov⁻¹)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as T
import Cubical.HITs.EilenbergMacLane1.Properties as EM
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Homotopy.Connected
  using (isConnected; isConnectedFun; isConnectedRetractFromIso; inrConnected;
         connectedTruncIso)
import DeloopS3.Move.CancelMinimal as Circle
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
import DeloopS3.Seifert.MarkedSeifert.FinalDone as Final
import DeloopS3.Cert.Input.Model as Input
import DeloopS3.Cert.Check as Ch
open import DeloopS3.Bridge.OriginalSpan

abstract
  paths→connected : ∀ {ℓ} {Y : Type ℓ} (y₀ : Y)
    → ((y : Y) → PT.∥ y₀ ≡ y ∥₁) → isConnected 2 Y
  paths→connected y₀ paths = T.∣ y₀ ∣ , T.elim
    (λ _ → isProp→isSet (T.isOfHLevelTrunc 2 _ _))
    (λ y → PT.rec (T.isOfHLevelTrunc 2 _ _) (cong T.∣_∣) (paths y))

  circle-paths : (u : Circle.C) → PT.∥ Circle.0C ≡ u ∥₁
  circle-paths = EM.elimProp ℤGroup (λ _ → PT.squash₁) PT.∣ refl ∣₁

  circle-connected : isConnected 2 Circle.C
  circle-connected = paths→connected Circle.0C circle-paths

  wedge-paths : (w : Literal.P) → PT.∥ Literal.p₀ ≡ w ∥₁
  wedge-paths (inl u) = PT.map (cong inl) (circle-paths u)
  wedge-paths (inr u) = PT.map
    (λ v → Literal.edge ∙ cong inr v) (circle-paths u)
  wedge-paths (push tt i) = isProp→PathP
    {B = λ j → PT.∥ Literal.p₀ ≡ Literal.edge j ∥₁}
    (λ _ → PT.squash₁)
    (wedge-paths (inl Circle.0C)) (wedge-paths (inr Circle.0C)) i

  core-paths : (v : Literal.Core)
    → PT.∥ (Literal.p₀ , Circle.0C) ≡ v ∥₁
  core-paths (w , u) = PT.rec PT.squash₁
    (λ s → PT.map (λ t → ΣPathP (s , t)) (circle-paths u))
    (wedge-paths w)

module SeifertConnected (a b d : ℤ) where
  private
    module S = Literal.Seifert a b d

  ιL : Literal.Core → Literal.M a b d
  ιL = inl
  ιR : (Circle.C ⊎ Circle.C) ⊎ Circle.C → Literal.M a b d
  ιR = inr
  glue : (z : (Circle.T² ⊎ Circle.T²) ⊎ Circle.T²)
    → ιL (S.allLeft z) ≡ ιR (S.allRight z)
  glue = push

  base : Literal.M a b d
  base = ιL (Literal.p₀ , Circle.0C)

  abstract
    right-paths : (u : (Circle.C ⊎ Circle.C) ⊎ Circle.C)
      → PT.∥ base ≡ ιR u ∥₁
    right-paths (left (left u)) = PT.map
      (λ t → glue (left (left (Circle.0C , Circle.0C)))
        ∙ cong (ιR ∘ left ∘ left) t) (circle-paths u)
    right-paths (left (right u)) = PT.map
      (λ t → cong (λ w → ιL (w , Circle.0C)) Literal.edge
        ∙ glue (left (right (Circle.0C , Circle.0C)))
        ∙ cong (ιR ∘ left ∘ right) t) (circle-paths u)
    right-paths (right u) = PT.map
      (λ t → glue (right (Circle.0C , Circle.0C))
        ∙ cong (ιR ∘ right) t) (circle-paths u)

    paths : (m : Literal.M a b d) → PT.∥ base ≡ m ∥₁
    paths (inl v) = PT.map (cong ιL) (core-paths v)
    paths (inr u) = right-paths u
    paths (push z i) = isProp→PathP
      {B = λ j → PT.∥ base ≡ glue z j ∥₁} (λ _ → PT.squash₁)
      (PT.map (cong ιL) (core-paths (S.allLeft z)))
      (right-paths (S.allRight z)) i

    connected : isConnected 2 (Literal.M a b d)
    connected = paths→connected base paths

abstract
  A-connected : (c : ShortCase) → isConnected 2 (A c)
  A-connected c = SeifertConnected.connected (pos 2) (pos 2) (pos (e c))

  C-connected : (c : ShortCase) → isConnected 2 (C c)
  C-connected c = SeifertConnected.connected
    (pos 2) (pos 3) (pos (Input.localOrder c Ch.C))

  -- Each point of RP 1 has a merely inhabited double-cover fibre.  Its
  -- pushout seam connects it to the cap, in the literal RP 2 model.
  R-paths : (b : R) → PT.∥ inr tt ≡ b ∥₁
  R-paths (inl x) = PT.rec PT.squash₁
    (λ eq → PT.∣ sym (push (x , invEq eq false)) ∣₁)
    (snd (cov⁻¹ 1 x))
  R-paths (inr _) = PT.∣ refl ∣₁
  R-paths (push (x , u) i) = isProp→PathP
    {B = λ j → PT.∥ Path R (inr tt) (push (x , u) j) ∥₁}
    (λ _ → PT.squash₁) (R-paths (inl x)) PT.∣ refl ∣₁ i

  R-connected : isConnected 2 R
  R-connected = paths→connected (inr tt) R-paths

  -- This is the circle-fibre input needed for pi-one surjectivity and
  -- van Kampen, not merely a statement about the abstract presentation.
  q-connected : (c : ShortCase) → isConnectedFun 2 (q c)
  q-connected c b = PT.rec isPropIsContr
    (λ eq → isConnectedRetractFromIso 2 (equivToIso eq) circle-connected)
    (Final.circleFibres (pos (e c)) b)

  X-inr-connected : (c : ShortCase)
    → isConnectedFun 2 {A = C c} {B = X c} (inr {f = q c} {g = p c})
  X-inr-connected c = inrConnected 2 (q c) (p c) (q-connected c)

  -- The generic proof is sealed before specializing either large leg.
  connected-codomain : ∀ {ℓ} {Y Z : Type ℓ}
    (f : Y → Z) → isConnected 2 Y → isConnectedFun 2 f → isConnected 2 Z
  connected-codomain f connY connf = isOfHLevelRetractFromIso 0
    (invIso (connectedTruncIso 2 f connf)) connY

  X-connected : (c : ShortCase) → isConnected 2 (X c)
  X-connected c = connected-codomain {Y = C c} {Z = X c}
    (inr {f = q c} {g = p c}) (C-connected c) (X-inr-connected c)
