{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Recognition.TruncatedMap where

-- Naturality of the actual Hurewicz map and Whitehead on 3-truncations.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (second-in-isEquiv-comp→isEquiv ; isEquivFromIsContr)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace using (Ω^_)
open import Cubical.Homotopy.Group.Base
open import Cubical.Homotopy.Group.Properties using (connectedFun→π'Equiv)
open import Cubical.Homotopy.WhiteheadsLemma using (WhiteheadsLemma)
import Cubical.HITs.Truncation as TR
import Cubical.HITs.SetTruncation as ST

private
  trunc-unit-connected : {A : Type} (n : ℕ)
    → isConnectedFun (suc n) (TR.∣_∣ {A = A} {n = n})
  trunc-unit-connected n = elim.isConnectedPrecompose TR.∣_∣ (suc n)
    (λ P → (λ g → TR.elim (λ x → snd (P x)) g) , λ g → refl)

  π₁-zero : (A : Pointed ℓ-zero) → isConnected 3 (fst A) → isContr (π 1 A)
  π₁-zero A conn = isOfHLevelRetractFromIso 0 TR.setTruncTrunc2Iso
    (isConnectedPath 2 conn (snd A) (snd A))

  π₂-zero : (A : Pointed ℓ-zero) → isConnected 4 (fst A) → isContr (π 2 A)
  π₂-zero A conn = isOfHLevelRetractFromIso 0 TR.setTruncTrunc2Iso
    (isConnectedPath 2 (isConnectedPath 3 conn (snd A) (snd A)) refl refl)

  higher-zero : (A : Pointed ℓ-zero) → isOfHLevel 5 (fst A)
    → (k : ℕ) → isContr (π (4 + k) A)
  higher-zero A hA k = ST.isContr→isContrSetTrunc
    (snd ((Ω^ (4 + k)) A) ,
      hLevΩ+ {A = A} 1 (4 + k)
        (subst (λ n → isOfHLevel n (fst A))
          (+-assoc k 4 1 ∙ cong (_+ 1) (+-comm k 4)) (isOfHLevelPlus k hA))
        (snd ((Ω^ (4 + k)) A)))

  π'→π-isEquiv : {A B : Pointed ℓ-zero} (n : ℕ) (f : A →∙ B)
    → isEquiv (fst (π'∘∙Hom n f)) → isEquiv (fst (πHom n f))
  π'→π-isEquiv n f = transport
    (λ i → isEquiv (fst (GroupHomπ≅π'PathP-hom n f (~ i))))

π₃-iso→connected4 : {A B : Type} (f : A → B)
  → isConnected 4 A → isConnected 4 B
  → ((a : A) → isEquiv (fst (π'∘∙Hom {A = A , a} 2 (f , refl))))
  → isConnectedFun 4 f
π₃-iso→connected4 {A} {B} f connA connB πf-equiv =
  isConnectedFunCancel' f TR.∣_∣ 4 (trunc-unit-connected 4)
    (isConnectedComp tf TR.∣_∣ 4
      (isEquiv→isConnected tf tf-equiv 4)
      (isConnectedFunSubtr 4 1 TR.∣_∣ (trunc-unit-connected 4)))
  where
  TA = TR.hLevelTrunc 5 (A)
  TB = TR.hLevelTrunc 5 (B)
  tf : TA → TB
  tf = TR.map f

  connTA : isConnected 4 TA
  connTA = isOfHLevelRetractFromIso 0 (invIso (TR.truncOfTruncIso 4 1)) connA

  connTB : isConnected 4 TB
  connTB = isOfHLevelRetractFromIso 0 (invIso (TR.truncOfTruncIso 4 1)) connB

  πtf-equiv-at : (a : A)
    → isEquiv (fst (π'∘∙Hom {A = TA , TR.∣ a ∣} 2 (tf , refl)))
  πtf-equiv-at a = second-in-isEquiv-comp→isEquiv
    (fst (π'∘∙Hom 2 unitA∙)) (fst (π'∘∙Hom 2 tf∙))
    (fst (π'∘∙Hom 2 unitB∙) ∘ fst (π'∘∙Hom 2 f∙))
    (snd (fst (connectedFun→π'Equiv 2 unitA∙ (trunc-unit-connected 4))))
    (snd (compEquiv (_ , πf-equiv a)
      (fst (connectedFun→π'Equiv 2 unitB∙ (trunc-unit-connected 4)))))
    square
    where
    f∙ : (A , a) →∙ (B , f a)
    f∙ = f , refl
    unitA∙ : (A , a) →∙ (TA , TR.∣ a ∣)
    unitA∙ = TR.∣_∣ , refl
    unitB∙ : (B , f a) →∙ (TB , TR.∣ f a ∣)
    unitB∙ = TR.∣_∣ , refl
    tf∙ : (TA , TR.∣ a ∣) →∙ (TB , TR.∣ f a ∣)
    tf∙ = tf , refl

    square : fst (π'∘∙Hom 2 unitB∙) ∘ fst (π'∘∙Hom 2 f∙)
           ≡ fst (π'∘∙Hom 2 tf∙) ∘ fst (π'∘∙Hom 2 unitA∙)
    square = funExt (ST.elim (λ _ → isProp→isSet (ST.isSetSetTrunc _ _))
      (λ s → cong ST.∣_∣₂
        (sym (∘∙-assoc unitB∙ f∙ s) ∙ ∘∙-assoc tf∙ unitA∙ s)))

  πtf-equiv : (a : TA) → isEquiv (fst (πHom {A = TA , a} 2 (tf , refl)))
  πtf-equiv = TR.elim (λ _ → isProp→isOfHLevelSuc 4 (isPropIsEquiv _))
    (λ a → π'→π-isEquiv 2 (tf , refl) (πtf-equiv-at a))

  all-π : (a : TA) (k : ℕ) → isEquiv (fst (πHom {A = TA , a} k (tf , refl)))
  all-π a zero = isEquivFromIsContr _
    (π₁-zero (TA , a) (isConnectedSubtr 3 1 connTA))
    (π₁-zero (TB , tf a) (isConnectedSubtr 3 1 connTB))
  all-π a (suc zero) = isEquivFromIsContr _
    (π₂-zero (TA , a) connTA) (π₂-zero (TB , tf a) connTB)
  all-π a (suc (suc zero)) = πtf-equiv a
  all-π a (suc (suc (suc k))) = isEquivFromIsContr _
    (higher-zero (TA , a) (TR.isOfHLevelTrunc 5) k)
    (higher-zero (TB , tf a) (TR.isOfHLevelTrunc 5) k)

  tf-equiv : isEquiv tf
  tf-equiv = WhiteheadsLemma (TR.isOfHLevelTrunc 5) (TR.isOfHLevelTrunc 5) tf
    (isEquivFromIsContr (ST.map tf)
      (isOfHLevelRetractFromIso 0 TR.setTruncTrunc2Iso (isConnectedSubtr 2 2 connTA))
      (isOfHLevelRetractFromIso 0 TR.setTruncTrunc2Iso (isConnectedSubtr 2 2 connTB)))
    all-π
