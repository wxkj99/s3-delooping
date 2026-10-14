{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.TargetLoops where

-- Shared marked coordinates in the specified rose/Kind model.  The
-- connecting edge is retained in every core loop; it is not a generator.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base using (inl; inr; push)
import Cubical.HITs.SetTruncation as ST
open import Cubical.Algebra.Group.Base using (Group₀)
open import Cubical.Homotopy.Group.Base using (πGr)
open import DeloopS3.Cert.Interpret.Short using (ShortCase; octa; icosa)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Model
open import DeloopS3.Cover.Orientation.CircleModel using (hC)

m₀ : (c : ShortCase) → Model.M_G c
m₀ c = inl (R.root , R.0C)

G : ShortCase → Group₀
G c = πGr 0 (Model.M_G c , m₀ c)

coreEdge : (c : ShortCase) (k : Ch.Kind)
  → Path (Model.M_G c) (m₀ c) (inr (k , R.0C))
coreEdge c k = push (k , R.0C , R.0C)

coreCircle : (c : ShortCase) → Ch.Kind → R.C → Model.M_G c
coreCircle c k u = inr (k , u)

coreLoop : (c : ShortCase) (k : Ch.Kind) → m₀ c ≡ m₀ c
coreLoop c k = coreEdge c k ∙∙ cong (coreCircle c k) hC ∙∙ sym (coreEdge c k)

coreClass : (c : ShortCase) → Ch.Kind → fst (G c)
coreClass c k = ST.∣ coreLoop c k ∣₂

x y z h : (c : ShortCase) → fst (G c)
x c = coreClass c Ch.A
y c = coreClass c Ch.B
z c = coreClass c Ch.C
h c = ST.∣ (λ i → inl (R.root , hC i)) ∣₂

w : (c : ShortCase) → fst (G c)
w octa = z octa
w icosa = y icosa
