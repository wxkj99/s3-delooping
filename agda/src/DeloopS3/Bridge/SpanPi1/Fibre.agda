{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.SpanPi1.Fibre where

-- Exactness and surjectivity for the actual bundle leg q, with specified
-- basepoints and no choice of an untruncated lift.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Int using (pos)
open import Cubical.Algebra.Group.Base using (Group; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as T
open import Cubical.HITs.Pushout.Base using (inr)
open import Cubical.Homotopy.Group.Base using (πGr)
open import Cubical.Homotopy.Connected using (isConnectedFun; isConnectedCong)
import DeloopS3.Move.CancelMinimal as Circle
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
import DeloopS3.Seifert.MarkedSeifert.FinalDone as Final
open import DeloopS3.Bridge.OriginalSpan
open import DeloopS3.Bridge.SpanPi1.Connected using (q-connected)

-- Strict pointing is intentional: the other vertex is pointed at f a.
-- cap-point below separately retains the path to the RP 2 cap.
module Map {ℓ ℓ'} {Y : Type ℓ} {Z : Type ℓ'} (f : Y → Z) (a : Y) where
  sourceπ : Group ℓ
  sourceπ = πGr 0 (Y , a)
  targetπ : Group ℓ'
  targetπ = πGr 0 (Z , f a)

  mapπ : fst sourceπ → fst targetπ
  mapπ = ST.map (cong f)

  abstract
    mapHom : GroupHom sourceπ targetπ
    mapHom = mapπ , makeIsGroupHom
      (ST.elim2 (λ _ _ → isProp→isSet (ST.squash₂ _ _))
        (λ s t → cong ST.∣_∣₂ (cong-∙ f s t)))

    surjective : isConnectedFun 2 f
      → (u : fst targetπ) → PT.∥ fiber mapπ u ∥₁
    surjective connected = ST.elim (λ _ → isProp→isSet PT.squash₁)
      (λ s → T.rec PT.squash₁
        (λ { (t , eq) → PT.∣ ST.∣ t ∣₂ , cong ST.∣_∣₂ eq ∣₁ })
        (isConnectedCong 1 f connected {a₀ = a} {a₁ = a} s .fst))

  F : Type (ℓ-max ℓ ℓ')
  F = fiber f (f a)
  f₀ : F
  f₀ = a , refl
  fibreπ : Group (ℓ-max ℓ ℓ')
  fibreπ = πGr 0 (F , f₀)
  includeπ : fst fibreπ → fst sourceπ
  includeπ = ST.map (cong fst)

  abstract
    image-in-kernel : (u : fst fibreπ) → mapπ (includeπ u) ≡ ST.∣ refl ∣₂
    image-in-kernel = ST.elim (λ _ → isProp→isSet (ST.squash₂ _ _))
      (λ s → cong ST.∣_∣₂ (λ j i → snd (s i) j))

    -- Exactness uses effectiveness of set truncation, not an asserted
    -- long exact sequence and not a quotient of an abstract finite group.
    kernel-in-image : (u : fst sourceπ) → mapπ u ≡ ST.∣ refl ∣₂
      → PT.∥ fiber includeπ u ∥₁
    kernel-in-image = ST.elim
      (λ _ → isProp→isSet (isPropΠ (λ _ → PT.squash₁)))
      (λ s eq → PT.rec PT.squash₁
        (λ h → PT.∣ ST.∣ (λ i → s i , (λ j → h j i)) ∣₂ , refl ∣₁)
        (Iso.fun ST.PathIdTrunc₀Iso eq))

abstract
  -- A loop in any specified fibre projects to a null loop, also when
  -- the fibre's pointing path is not judgmentally refl.
  fibre-loop-null : ∀ {ℓ ℓ'} {Y : Type ℓ} {Z : Type ℓ'}
    (f : Y → Z) (a : Y) (b : Z) (pointing : f a ≡ b)
    (s : Path (fiber f b) (a , pointing) (a , pointing))
    → cong f (cong fst s) ≡ refl
  fibre-loop-null f a b pointing = J
    (λ b pointing → (s : Path (fiber f b) (a , pointing) (a , pointing))
      → cong f (cong fst s) ≡ refl)
    (λ s j i → snd (s i) j) pointing

-- Final's cap chart retains an explicit circle fibre.  Its inverse gives
-- a genuine fibre loop, rather than an arbitrary element of ker pi-one(q).
cap : (c : ShortCase) → Circle.C → fiber (q c) (inr tt)
cap c = invEq (Final.capFibre (pos (e c)))

a₀ : (c : ShortCase) → A c
a₀ c = fst (cap c Circle.0C)

cap-point : (c : ShortCase) → q c (a₀ c) ≡ inr tt
cap-point c = snd (cap c Circle.0C)

Aπ Rπ Cπ : ShortCase → Group ℓ-zero
Aπ c = πGr 0 (A c , a₀ c)
Rπ c = πGr 0 (R , q c (a₀ c))
Cπ c = πGr 0 (C c , p c (a₀ c))

qπ : (c : ShortCase) → fst (Aπ c) → fst (Rπ c)
qπ c = Map.mapπ (q c) (a₀ c)
pπ : (c : ShortCase) → fst (Aπ c) → fst (Cπ c)
pπ c = Map.mapπ (p c) (a₀ c)

r-loop : (c : ShortCase) → a₀ c ≡ a₀ c
r-loop c = cong fst (cong (cap c) hC)

rπ : (c : ShortCase) → fst (Aπ c)
rπ c = ST.∣ r-loop c ∣₂

abstract
  q-r : (c : ShortCase) → qπ c (rπ c) ≡ GroupStr.1g (snd (Rπ c))
  q-r c = cong ST.∣_∣₂ (fibre-loop-null (q c) (a₀ c) (inr tt)
    (cap-point c) (cong (cap c) hC))

  qπ-surjective : (c : ShortCase) (u : fst (Rπ c))
    → PT.∥ fiber (qπ c) u ∥₁
  qπ-surjective c = Map.surjective (q c) (a₀ c) (q-connected c)

  qπ-kernel-in-fibre-image : (c : ShortCase) (u : fst (Aπ c))
    → qπ c u ≡ GroupStr.1g (snd (Rπ c))
    → PT.∥ fiber (Map.includeπ (q c) (a₀ c)) u ∥₁
  qπ-kernel-in-fibre-image c = Map.kernel-in-image (q c) (a₀ c)

  qπ-fibre-image-in-kernel : (c : ShortCase)
    (u : fst (Map.fibreπ (q c) (a₀ c)))
    → qπ c (Map.includeπ (q c) (a₀ c) u) ≡ GroupStr.1g (snd (Rπ c))
  qπ-fibre-image-in-kernel c = Map.image-in-kernel (q c) (a₀ c)
