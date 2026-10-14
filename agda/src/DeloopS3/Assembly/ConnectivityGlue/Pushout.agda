{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Assembly.ConnectivityGlue.Pushout where

-- Finite truncation arguments for pushout connectivity.  These lemmas know
-- nothing about the actual Seifert spans or localization.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (fiber)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Homotopy.Connected using (isConnected; isConnectedPath)
open import Cubical.HITs.Pushout.Base
import Cubical.HITs.Truncation as T
import Cubical.HITs.PropositionalTruncation as PT

abstract
  -- A map from a simply connected type to a groupoid has a based
  -- contraction, including the normalization needed at the common seam.
  based-contraction : {X Z : Type} → isConnected 3 X → isGroupoid Z
    → (f : X → Z) → (x₀ : X)
    → Σ[ h ∈ ((x : X) → f x₀ ≡ f x) ] (h x₀ ≡ refl)
  based-contraction {X} {Z} conn gz f x₀ = h , β
    where
    f₃ : T.hLevelTrunc 3 X → Z
    f₃ = T.rec gz f
    prop₃ : isProp (T.hLevelTrunc 3 X)
    prop₃ = isContr→isProp conn
    h : (x : X) → f x₀ ≡ f x
    h x = cong f₃ (prop₃ T.∣ x₀ ∣ T.∣ x ∣)
    β : h x₀ ≡ refl
    β = cong (cong f₃)
      (isProp→isSet prop₃ T.∣ x₀ ∣ T.∣ x₀ ∣
        (prop₃ T.∣ x₀ ∣ T.∣ x₀ ∣) refl)

module SimplePushout {A B C : Type} (f : A → B) (g : A → C)
  (a₀ : A) (connA : isConnected 2 A)
  (scB : isConnected 3 B) (scC : isConnected 3 C) where
  private
    X : Type
    X = Pushout f g
    Z : Type
    Z = T.hLevelTrunc 3 X
    z₀ : Z
    z₀ = T.∣ inl (f a₀) ∣
    edge : (a : A) → Path Z T.∣ inl (f a) ∣ T.∣ inr (g a) ∣
    edge a i = T.∣ push a i ∣

    left-data : Σ[ h ∈ ((b : B) → Path Z z₀ T.∣ inl b ∣) ]
      (h (f a₀) ≡ refl)
    left-data = based-contraction scB (T.isOfHLevelTrunc 3)
      (λ b → T.∣ inl b ∣) (f a₀)
    right-data : Σ[ h ∈ ((c : C) → Path Z T.∣ inr (g a₀) ∣ T.∣ inr c ∣) ]
      (h (g a₀) ≡ refl)
    right-data = based-contraction scC (T.isOfHLevelTrunc 3)
      (λ c → T.∣ inr c ∣) (g a₀)

    left : (b : B) → Path Z z₀ T.∣ inl b ∣
    left = fst left-data
    right : (c : C) → Path Z z₀ T.∣ inr c ∣
    right c = edge a₀ ∙ fst right-data c

    right-β : right (g a₀) ≡ edge a₀
    right-β = cong (edge a₀ ∙_) (snd right-data) ∙ sym (rUnit (edge a₀))

    Seam : A → Type
    Seam a = PathP (λ i → z₀ ≡ edge a i) (left (f a)) (right (g a))
    seam-prop : (a : A) → isProp (Seam a)
    seam-prop a = isOfHLevelPathP' 1
      (T.isOfHLevelTrunc 3 z₀ (edge a i1)) (left (f a)) (right (g a))
    seam₀ : Seam a₀
    seam₀ = transport
      (λ k → PathP (λ i → z₀ ≡ edge a₀ i)
        (snd left-data (~ k)) (right-β (~ k)))
      (λ i j → edge a₀ (i ∧ j))
    seam : (a : A) → Seam a
    seam a = T.rec (seam-prop a) (λ s → subst Seam s seam₀)
      (fst (isConnectedPath 1 connA a₀ a))

    contraction : (x : X) → z₀ ≡ T.∣ x ∣
    contraction (inl b) = left b
    contraction (inr c) = right c
    contraction (push a i) = seam a i

  abstract
    connected : isConnected 3 (Pushout f g)
    connected = z₀ , T.elim
      (λ z → isSet→isGroupoid (T.isOfHLevelTrunc 3 z₀ z)) contraction

abstract
  pushout-simple : {A B C : Type} (f : A → B) (g : A → C)
    → A → isConnected 2 A → isConnected 3 B → isConnected 3 C
    → isConnected 3 (Pushout f g)
  pushout-simple = SimplePushout.connected

  -- Merely surjective maps preserve connectedness; the centre is the
  -- image of the centre of the set truncation, not a chosen preimage.
  surjective-connected : {X Y : Type} (f : X → Y)
    → ((y : Y) → PT.∥ fiber f y ∥₁)
    → isConnected 2 X → isConnected 2 Y
  surjective-connected {X} {Y} f surj conn = centre , T.elim
    (λ y → isProp→isSet (T.isOfHLevelTrunc 2 centre y)) paths
    where
    map₂ : T.hLevelTrunc 2 X → T.hLevelTrunc 2 Y
    map₂ = T.map f
    centre : T.hLevelTrunc 2 Y
    centre = map₂ (fst conn)
    paths : (y : Y) → centre ≡ T.∣ y ∣
    paths y = PT.rec (T.isOfHLevelTrunc 2 centre T.∣ y ∣)
      (λ { (x , s) → cong map₂ (snd conn T.∣ x ∣) ∙ cong T.∣_∣ s })
      (surj y)

module ConnectedPushout {A B C : Type} (f : A → B) (g : A → C)
  (a₀ : A) (connB : isConnected 2 B) (connC : isConnected 2 C) where
  private
    X : Type
    X = Pushout f g
    Z : Type
    Z = T.hLevelTrunc 2 X
    z₀ : Z
    z₀ = T.∣ inl (f a₀) ∣
    left : (b : B) → Path Z z₀ T.∣ inl b ∣
    left b = cong (T.map {n = 2} (inl {f = f} {g = g}))
      (isContr→isProp connB T.∣ f a₀ ∣ T.∣ b ∣)
    right : (c : C) → Path Z z₀ T.∣ inr c ∣
    right c = cong T.∣_∣ (push a₀)
      ∙ cong (T.map {n = 2} (inr {f = f} {g = g}))
          (isContr→isProp connC T.∣ g a₀ ∣ T.∣ c ∣)
    contraction : (x : X) → z₀ ≡ T.∣ x ∣
    contraction (inl b) = left b
    contraction (inr c) = right c
    contraction (push a i) = isProp→PathP
      {B = λ j → Path Z z₀ T.∣ push a j ∣}
      (λ j → T.isOfHLevelTrunc 2 z₀ T.∣ push a j ∣)
      (left (f a)) (right (g a)) i
  abstract
    connected : isConnected 2 (Pushout f g)
    connected = z₀ , T.elim
      (λ z → isProp→isSet (T.isOfHLevelTrunc 2 z₀ z)) contraction

abstract
  pushout-connected : {A B C : Type} (f : A → B) (g : A → C)
    → A → isConnected 2 B → isConnected 2 C
    → isConnected 2 (Pushout f g)
  pushout-connected = ConnectedPushout.connected
