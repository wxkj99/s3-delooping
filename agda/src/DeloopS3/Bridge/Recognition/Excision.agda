{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.Excision where

-- Blakers–Massey raises map connectivity from cofibre connectivity.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (_×_ ; fiberProjIso)
open import Cubical.HITs.Pushout.Base using (cofib ; inl ; inr)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.BlakersMassey using (module BlakersMassey□)

cofib5conn→map4conn : {A B : Type} (f : A → B)
  → isConnected 4 A → isConnectedFun 4 f
  → isConnected 7 (cofib f) → isConnectedFun 6 f
cofib5conn→map4conn {A} {B} f connA connf connC =
  isConnectedComp fst comparison 6 projection-connected comparison-connected
  where
  -- Put the constant map first: the library pushout is literally cofib f.
  module BM = BlakersMassey□ (λ (_ : A) → tt) f 3 3
    (isConnected→isConnectedFun 4 connA) connf

  Paths : B → Type
  Paths b = Path (cofib f) (inl tt) (inr b)

  Pullback : Type
  Pullback = Σ B Paths

  forget-unit : Iso (Σ (Unit × B) BM.PushoutPath×) Pullback
  Iso.fun forget-unit ((tt , b) , p) = b , p
  Iso.inv forget-unit (b , p) = (tt , b) , p
  Iso.sec forget-unit (b , p) = refl
  Iso.ret forget-unit ((tt , b) , p) = refl

  comparison : A → Pullback
  comparison = Iso.fun forget-unit ∘ BM.toPullback

  comparison-connected : isConnectedFun 6 comparison
  comparison-connected = isConnectedComp (Iso.fun forget-unit) BM.toPullback 6
    (isEquiv→isConnected (Iso.fun forget-unit) (isoToIsEquiv forget-unit) 6)
    BM.isConnected-toPullback

  projection-connected : isConnectedFun 6 (fst {B = Paths})
  projection-connected b = isConnectedRetractFromIso 6
    (invIso (fiberProjIso B Paths b))
    (isConnectedPath 6 connC (inl tt) (inr b))
