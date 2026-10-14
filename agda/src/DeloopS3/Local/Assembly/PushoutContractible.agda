{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Assembly.PushoutContractible where

-- Contractibility of localized pushouts.  The locality-transfer
-- hypotheses express divisibility without fixing a factorization of m.
-- Only the mapping-space universal properties are used, not preservation
-- of pushouts by localization.
open import DeloopS3.Local.Base
open import DeloopS3.Local.Unique using (module Unique)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using
  (isEquiv[f∘equivFunA≃B]→isEquiv[f]
  ; isEquiv[equivFunA≃B∘f]→isEquiv[f])
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-contractSnd)
open import Cubical.HITs.Pushout.Base using (Pushout ; inl ; inr ; push)

-- Map(P,Z) is the homotopy pullback of the two restriction maps.
-- Reverse the matching path so that its last two entries form a fiber.
pushout-maps-Iso : (X1 X2 Y Z : Type) (f : Y → X1) (g : Y → X2)
  → Iso (Pushout f g → Z)
      (Σ[ h1 ∈ (X1 → Z) ] fiber (λ (h2 : X2 → Z) → h2 ∘ g) (h1 ∘ f))
Iso.fun (pushout-maps-Iso X1 X2 Y Z f g) h =
  h ∘ inl , h ∘ inr , (λ i y → h (push y (~ i)))
Iso.inv (pushout-maps-Iso X1 X2 Y Z f g) (h1 , h2 , p) (inl x) = h1 x
Iso.inv (pushout-maps-Iso X1 X2 Y Z f g) (h1 , h2 , p) (inr x) = h2 x
Iso.inv (pushout-maps-Iso X1 X2 Y Z f g) (h1 , h2 , p) (push y i) = p (~ i) y
Iso.sec (pushout-maps-Iso X1 X2 Y Z f g) (h1 , h2 , p) = refl
Iso.ret (pushout-maps-Iso X1 X2 Y Z f g) h = funExt λ
  { (inl x) → refl ; (inr x) → refl ; (push y i) → refl }

private
  -- Contractibility of L_d X identifies maps X → Z with their constant
  -- values, provided Z is d-local.  The forward map is literally const.
  local-contr-const : (d : ℕ) (X Z : Type)
    → isContr (L d X) → Local d Z
    → isEquiv (λ (z : Z) (_ : X) → z)
  local-contr-const d X Z c lZ = snd (compEquiv constants restriction)
    where
    constants : Z ≃ (L d X → Z)
    constants = isoToEquiv (iso (λ z _ → z) (λ h → h (fst c))
      (λ h → funExt (λ x → cong h (snd c x))) (λ _ → refl))

    restriction : (L d X → Z) ≃ (X → Z)
    restriction = (λ h → h ∘ η {d} {X}) ,
      Unique.isEquiv-preη {F = F d} {X = X} {Y = Z} lZ

  -- The right-hand restriction is an equivalence by two-out-of-three.
  -- Its fibers contract the mapping-space pullback to Map(X1,Z).
  pushout-const : (X1 X2 Y Z : Type) (f : Y → X1) (g : Y → X2)
    → isEquiv (λ (z : Z) (_ : X1) → z)
    → isEquiv (λ (z : Z) (_ : X2) → z)
    → isEquiv (λ (z : Z) (_ : Y) → z)
    → isEquiv (λ (z : Z) (_ : Pushout f g) → z)
  pushout-const X1 X2 Y Z f g e1 e2 eY =
    isEquiv[equivFunA≃B∘f]→isEquiv[f]
      (λ (z : Z) (_ : Pushout f g) → z) left-restriction e1
    where
    right-restriction : isEquiv (λ (h : X2 → Z) → h ∘ g)
    right-restriction = isEquiv[f∘equivFunA≃B]→isEquiv[f]
      (λ (h : X2 → Z) → h ∘ g) ((λ z _ → z) , e2) eY

    left-restriction : (Pushout f g → Z) ≃ (X1 → Z)
    left-restriction = compEquiv
      (isoToEquiv (pushout-maps-Iso X1 X2 Y Z f g))
      (Σ-contractSnd (λ h1 → equiv-proof right-restriction (h1 ∘ f)))

-- In the application (m,m1,m2,m3) = (30,3,10,2).  More generally m
-- can be any common multiple: supply Local m Z → Local mi Z for each i
-- (for example via EI.local-factor).  No connectedness or chosen points
-- of the span are required.
localize-pushout-contractible : (m m1 m2 m3 : ℕ)
  (X1 X2 Y : Type) (f : Y → X1) (g : Y → X2)
  → ((Z : Type) → Local m Z → Local m1 Z)
  → ((Z : Type) → Local m Z → Local m2 Z)
  → ((Z : Type) → Local m Z → Local m3 Z)
  → isContr (L m1 X1) → isContr (L m2 X2) → isContr (L m3 Y)
  → isContr (L m (Pushout f g))
localize-pushout-contractible m m1 m2 m3 X1 X2 Y f g
  transfer1 transfer2 transfer3 c1 c2 cY =
  fst null-unit , Unique.≡onη {F = F m} {X = P} {Y = LP}
    (local-L m P) (λ _ → fst null-unit) (idfun LP)
    (funExt⁻ (snd null-unit))
  where
  P = Pushout f g
  LP = L m P

  -- For every m-local Z the constant-map inclusion Z → Map(P,Z)
  -- is an equivalence, with the specified (not merely some) forward map.
  constants : (Z : Type) → Local m Z
    → isEquiv (λ (z : Z) (_ : P) → z)
  constants Z lZ = pushout-const X1 X2 Y Z f g
    (local-contr-const m1 X1 Z c1 (transfer1 Z lZ))
    (local-contr-const m2 X2 Z c2 (transfer2 Z lZ))
    (local-contr-const m3 Y Z cY (transfer3 Z lZ))

  -- Test against L_m P and extend const ≡ η by uniqueness of localization.
  null-unit : fiber (λ (z : LP) (_ : P) → z) (η {m} {P})
  null-unit = fst (equiv-proof (constants LP (local-L m P)) (η {m} {P}))
