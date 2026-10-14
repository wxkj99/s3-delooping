{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.TargetAssembly where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (invIso)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.HITs.Pushout.Base
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as T
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (GroupEquiv→GroupHom)
open import Cubical.Homotopy.Group.Base using (πGr; πHom)
open import Cubical.Homotopy.Group.Properties using (connectedFun→πSurj)
open import Cubical.Homotopy.Connected
  using (isConnected; isConnectedFun; isConnectedComp; isEquiv→isConnected;
    isConnectedPath; isConnectedRetract; isConnectedPoint2)
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
import DeloopS3.Cert.Input.Model as Model
import DeloopS3.Bridge.OriginalSpan as OS
open import DeloopS3.Bridge.SpanPi1.TargetLoops
open import DeloopS3.Bridge.SpanPi1.TargetNormal using (target-normal-generation)
open import DeloopS3.Bridge.SpanPi1.Connected using (X-connected; X-inr-connected)
open import DeloopS3.Bridge.SpanPi1.Coordinates
open import DeloopS3.Bridge.SpanPi1.Seam using (Π; πHom-loop)
open import DeloopS3.Bridge.SpanPi1.Character using (rotationCharacter)
open import DeloopS3.Bridge.SpanPi1.RP2Pi1 using (RP²-π₁)

abstract
  -- The ordinary connected-type/trivial-fundamental-group criterion.
  connected-trivial-π₁→simple : (A : Type₀) (a : A)
    → isConnected 2 A → isContr (fst (πGr 0 (A , a))) → isConnected 3 A
  connected-trivial-π₁→simple A a conn trivial = isConnectedPoint2 2 a
    (λ b → isConnectedRetract 2 snd (tt ,_) (λ _ → refl) (paths-connected b))
    where
    loops-connected : isConnected 2 (a ≡ a)
    loops-connected = isOfHLevelRetractFromIso 0 (invIso T.setTruncTrunc2Iso) trivial
    paths-connected : (b : A) → isConnected 2 (a ≡ b)
    paths-connected b = T.rec isPropIsContr
      (λ p → subst (λ v → isConnected 2 (a ≡ v)) p loops-connected)
      (fst (isConnectedPath 1 conn a b))

  π-compose : {A B C : Type₀} (f : A → B) (g : B → C) (a : A)
    (u : fst (Π A a))
    → fst (πHom 0 (g ∘ f , refl)) u
      ≡ fst (πHom 0 (g , refl)) (fst (πHom 0 (f , refl)) u)
  π-compose f g a = ST.elim (λ _ → isProp→isSet (ST.squash₂ _ _)) (λ l →
    πHom-loop (g ∘ f) a l
    ∙ sym (cong (fst (πHom 0 (g , refl))) (πHom-loop f a l)
      ∙ πHom-loop g (f a) (cong f l)))

right : (c : ShortCase) → OS.C c → OS.X c
right c = inr

model-inclusion : (c : ShortCase) → Model.M_G c → OS.X c
model-inclusion c = right c ∘ invEq (Model.originalTotalEquiv c)

x₀ : (c : ShortCase) → OS.X c
x₀ c = model-inclusion c (m₀ c)

Xπ : ShortCase → Group₀
Xπ c = Π (OS.X c) (x₀ c)

inclusionπ : (c : ShortCase) → GroupHom (G c) (Xπ c)
inclusionπ c = πHom 0 (model-inclusion c , refl)

abstract
  model-inclusion-connected : (c : ShortCase) → isConnectedFun 2 (model-inclusion c)
  model-inclusion-connected c = isConnectedComp (right c) (invEq (Model.originalTotalEquiv c)) 2
    (X-inr-connected c)
    (isEquiv→isConnected _ (snd (invEquiv (Model.originalTotalEquiv c))) 2)

-- Assemble the source character, core lift, and seam comparison without
-- a target marking or an assumed normal-closure theorem.
module Assembly
  (normal-core-lift : (c : ShortCase)
    → Σ[ u ∈ fst (K c) ] (fst (projectionπ c) u ≡ w c)
        × (fst (rotationCharacter c) (fst (subgroupπ c) u) ≡ zero₂))
  (cover-kernel-character : (c : ShortCase)
    (rp : GroupEquiv (Π OS.R (qCover c (a₀ c))) C₂)
    → (u : fst (K c)) → fst (qCoverπ c rp) u
      ≡ fst (rotationCharacter c) (fst (subgroupπ c) u))
  (pushout-kills-kernel : {A B C : Type₀} (q : A → B) (p : A → C) (a : A)
    (u : fst (Π A a))
    → fst (πHom 0 (q , refl)) u ≡ GroupStr.1g (snd (Π B (q a)))
    → fst (πHom 0 (inr {f = q} {g = p} , refl)) (fst (πHom 0 (p , refl)) u)
      ≡ GroupStr.1g (snd (Π (Pushout q p) (inr (p a))))) where

  module At (c : ShortCase) where
    -- Only a comparison MAP is needed. The conclusion remains about
    -- OS.X, with its exact p and q. The seam retains the inverse law of
    -- sourceCoverEquiv, rather than identifying loops through Done.
    Y : Type₀
    Y = Pushout (qCover c) (fst {B = Model.Q c})
    yr : Model.M_G c → Y
    yr = inr
    yl : OS.R → OS.X c
    yl = inl

    comparison : Y → OS.X c
    comparison (inl b) = yl b
    comparison (inr m) = model-inclusion c m
    comparison (push a i) =
      (push (invEq (OS.sourceCoverEquiv c) a)
       ∙ cong (model-inclusion c) (cong fst (secEq (OS.sourceCoverEquiv c) a))) i

    compareπ : GroupHom (Π Y (yr (m₀ c))) (Xπ c)
    compareπ = πHom 0 (comparison , refl)

    abstract
      model-kills-kernel : (u : fst (K c))
        → fst (πHom 0 (qCover c , refl)) u ≡ GroupStr.1g (snd (Π OS.R (qCover c (a₀ c))))
        → fst (inclusionπ c) (fst (projectionπ c) u) ≡ GroupStr.1g (snd (Xπ c))
      model-kills-kernel u ku = π-compose yr comparison (m₀ c) (fst (projectionπ c) u)
        ∙ cong (fst compareπ) (pushout-kills-kernel (qCover c) fst (a₀ c) u ku)
        ∙ IsGroupHom.pres1 (snd compareπ)

      w-killed-with-chart : (rp : GroupEquiv (Π OS.R (qCover c (a₀ c))) C₂)
        → fst (inclusionπ c) (w c) ≡ GroupStr.1g (snd (Xπ c))
      w-killed-with-chart rp = cong (fst (inclusionπ c)) (sym (snd witness .fst))
        ∙ model-kills-kernel (fst witness) q-zero
        where
        witness : Σ[ u ∈ fst (K c) ] (fst (projectionπ c) u ≡ w c)
          × (fst (rotationCharacter c) (fst (subgroupπ c) u) ≡ zero₂)
        witness = normal-core-lift c
        q-zero : fst (πHom 0 (qCover c , refl)) (fst witness)
          ≡ GroupStr.1g (snd (Π OS.R (qCover c (a₀ c))))
        q-zero = sym (retEq (fst rp) _)
          ∙ cong (invEq (fst rp))
            (cover-kernel-character c rp (fst witness) ∙ snd witness .snd
             ∙ sym (IsGroupHom.pres1 (snd (GroupEquiv→GroupHom rp))))
          ∙ retEq (fst rp) _

      w-killed : fst (inclusionπ c) (w c) ≡ GroupStr.1g (snd (Xπ c))
      w-killed = PT.rec (GroupStr.is-set (snd (Xπ c)) _ _) w-killed-with-chart
        (RP²-π₁ (qCover c (a₀ c)))

      target-image-trivial : (u : fst (G c)) → fst (inclusionπ c) u ≡ GroupStr.1g (snd (Xπ c))
      target-image-trivial = target-normal-generation c (Xπ c) (inclusionπ c) w-killed

      π₁-trivial : (v : fst (Xπ c)) → v ≡ GroupStr.1g (snd (Xπ c))
      π₁-trivial v = PT.rec (GroupStr.is-set (snd (Xπ c)) _ _)
        (λ { (u , p) → sym p ∙ target-image-trivial u })
        (connectedFun→πSurj 0 (model-inclusion c , refl) (model-inclusion-connected c) v)

  abstract
    X-simple : (c : ShortCase) → isConnected 3 (OS.X c)
    X-simple c = connected-trivial-π₁→simple (OS.X c) (x₀ c) (X-connected c)
      (GroupStr.1g (snd (Xπ c)) , λ v → sym (At.π₁-trivial c v))
