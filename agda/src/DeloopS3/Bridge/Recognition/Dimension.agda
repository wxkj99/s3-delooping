{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.Dimension where

-- Sharp finite-dimensional bounds, without connected-CW replacement
-- or geometric cancellation.
open import DeloopS3.Bridge.Recognition.Notation using (Finite≤)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Data.Nat
open import Cubical.Data.Nat.Order
open import Cubical.Data.Unit using (Unit ; tt ; Unit≃Unit*)
open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.Approximation using (finCWmap→CellMap)
open import Cubical.CW.Strictification using
  (strictCWskel ; elimStrictCW ; strictCwMap≡)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import Cubical.CW.Instances.Unit using (hasFinCWskelUnit*)
open import Cubical.CW.Instances.Sn using (hasFinCWskelSphere)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Pushout using (Pushout ; cofib ; inl ; inr ; push ; pushoutEquiv)
import Cubical.HITs.PropositionalTruncation as PT

private
  stabilizes-after : (C : CWskel ℓ-zero) (d : ℕ)
    → ((k : ℕ) → isEquiv (CW↪ C (k + d)))
    → (r : ℕ) → d ≤ r → isEquiv (CW↪ C r)
  stabilizes-after C d stable r (k , p) =
    subst (λ j → isEquiv (CW↪ C j)) p (stable k)

  module Sharp (A B C : CWskel ℓ-zero)
    (p : cellMap (strictCWskel A) (strictCWskel B))
    (q : cellMap (strictCWskel A) (strictCWskel C)) where
    module PO = CWPushout ℓ-zero A B C p q

    stable : (a b c t : ℕ)
      → ((k : ℕ) → isEquiv (CW↪ PO.B (k + a)))
      → ((k : ℕ) → isEquiv (CW↪ PO.C (k + b)))
      → ((k : ℕ) → isEquiv (CW↪ PO.D (k + c)))
      → a ≤ t → b ≤ suc t → c ≤ suc t
      → (k : ℕ) → isEquiv (CW↪ PO.pushoutSkel (k + suc t))
    stable a b c t ea eb ec at bt ct k =
      subst (λ r → isEquiv (CW↪ PO.pushoutSkel r)) (sym (+-suc k t))
        (subst isEquiv
          (funExt (λ { (inl x) → refl ; (inr x) → refl
                     ; (push x i) j → rUnit (push (inl x)) (~ j) i }))
          (snd (pushoutEquiv _ _ _ _
            (inl , stabilizes-after PO.B a ea (k + t) (≤-trans at ≤SumRight))
            (inl , stabilizes-after PO.C b eb (suc (k + t))
              (≤-trans bt (suc-≤-suc ≤SumRight)))
            (inl , stabilizes-after PO.D c ec (suc (k + t))
              (≤-trans ct (suc-≤-suc ≤SumRight)))
            refl refl)))

  cellular-bound : (a b c t : ℕ)
    → a ≤ t → b ≤ suc t → c ≤ suc t
    → (A B C : CWskel ℓ-zero)
    → ((k : ℕ) → isEquiv (CW↪ A (k + a)))
    → ((k : ℕ) → isEquiv (CW↪ B (k + b)))
    → ((k : ℕ) → isEquiv (CW↪ C (k + c)))
    → (p : cellMap A B) (q : cellMap A C)
    → Finite≤ t (Pushout (realiseCellMap {C = A} {D = B} p)
                        (realiseCellMap {C = A} {D = C} q))
  cellular-bound a b c t at bt ct =
    elimStrictCW λ A → elimStrictCW λ B → elimStrictCW λ C → strict-case A B C
    where
    strict-case : (A B C : CWskel ℓ-zero)
      → ((k : ℕ) → isEquiv (CW↪ (strictCWskel A) (k + a)))
      → ((k : ℕ) → isEquiv (CW↪ (strictCWskel B) (k + b)))
      → ((k : ℕ) → isEquiv (CW↪ (strictCWskel C) (k + c)))
      → (p : cellMap (strictCWskel A) (strictCWskel B))
        (q : cellMap (strictCWskel A) (strictCWskel C))
      → Finite≤ t (Pushout
          (realiseCellMap {C = strictCWskel A} {D = strictCWskel B} p)
          (realiseCellMap {C = strictCWskel A} {D = strictCWskel C} q))
    strict-case A B C ea eb ec p q =
      subst2 (λ p q → Finite≤ t
        (Pushout (realiseCellMap {C = strictCWskel A} {D = strictCWskel B} p)
                 (realiseCellMap {C = strictCWskel A} {D = strictCWskel C} q)))
        (strictCwMap≡ p) (strictCwMap≡ q)
        PT.∣ ((PO.pushoutSkel .fst , PO.pushoutSkel .snd ,
          Sharp.stable A B C p q a b c t ea eb ec at bt ct) ,
          PO.hasCWskelPushout .snd) ∣₁
      where
      module PO = CWPushout ℓ-zero A B C p q

-- A slightly stronger stage-indexed helper avoids fragile max arithmetic
-- inside the strictification and cellular approximation proof.
private
  skeletal-pushout : (a b c t : ℕ)
    → a ≤ t → b ≤ suc t → c ≤ suc t
    → (A : finCWskel ℓ-zero a) (B : finCWskel ℓ-zero b)
      (C : finCWskel ℓ-zero c)
    → (p : realise (finCWskel→CWskel a A) → realise (finCWskel→CWskel b B))
      (q : realise (finCWskel→CWskel a A) → realise (finCWskel→CWskel c C))
    → Finite≤ t (Pushout p q)
  skeletal-pushout a b c t at bt ct A B C p q = PT.rec2 PT.squash₁
    (λ (p' , hp) (q' , hq) → subst2 (λ p q → Finite≤ t (Pushout p q)) hp hq
      (cellular-bound a b c t at bt ct A' B' C'
        (A .snd .snd) (B .snd .snd) (C .snd .snd) p' q'))
    (finCWmap→CellMap a A B' p) (finCWmap→CellMap a A C' q)
    where
    A' = finCWskel→CWskel a A
    B' = finCWskel→CWskel b B
    C' = finCWskel→CWskel c C

pushout-finite≤ : {A B C : Type} (p : A → B) (q : A → C)
  (dA dB dC : ℕ) → Finite≤ dA A → Finite≤ dB B → Finite≤ dC C
  → Finite≤ (max (suc dA) (max dB dC)) (Pushout p q)
pushout-finite≤ {A} {B} {C} p q dA dB dC finA finB finC =
  PT.rec3 PT.squash₁ (λ a b c → presentations a b c p q) finA finB finC
  where
  t = max (suc dA) (max dB dC)

  presentations :
    (Σ[ As ∈ finCWskel ℓ-zero (suc dA) ] (A ≃ realise (finCWskel→CWskel (suc dA) As)))
    → (Σ[ Bs ∈ finCWskel ℓ-zero (suc dB) ] (B ≃ realise (finCWskel→CWskel (suc dB) Bs)))
    → (Σ[ Cs ∈ finCWskel ℓ-zero (suc dC) ] (C ≃ realise (finCWskel→CWskel (suc dC) Cs)))
    → (p : A → B) (q : A → C) → Finite≤ t (Pushout p q)
  presentations (As , ea) (Bs , eb) (Cs , ec) =
    subst (λ A → (p : A → B) (q : A → C) → Finite≤ t (Pushout p q))
      (sym (ua ea))
      (subst2 (λ B C → (p : realise (finCWskel→CWskel (suc dA) As) → B)
                       (q : realise (finCWskel→CWskel (suc dA) As) → C)
                       → Finite≤ t (Pushout p q))
        (sym (ua eb)) (sym (ua ec))
        (skeletal-pushout (suc dA) (suc dB) (suc dC) t
          (left-≤-max {m = suc dA} {n = max dB dC})
          (suc-≤-suc (≤-trans (left-≤-max {m = dB} {n = dC})
            (right-≤-max {n = max dB dC} {m = suc dA})))
          (suc-≤-suc (≤-trans (right-≤-max {n = dC} {m = dB})
            (right-≤-max {n = max dB dC} {m = suc dA}))) As Bs Cs))

sphere-finite≤ : (n : ℕ) → Finite≤ n (S₊ n)
sphere-finite≤ n = PT.∣ snd (hasFinCWskelSphere n) ∣₁

unit-finite≤ : Finite≤ 0 Unit
unit-finite≤ = subst (Finite≤ 0) (sym (ua Unit≃Unit*))
  PT.∣ snd hasFinCWskelUnit* ∣₁

cofib-finite≤ : {A B : Type} (f : A → B) (dA dB : ℕ)
  → Finite≤ dA A → Finite≤ dB B
  → Finite≤ (max (suc dA) dB) (cofib f)
cofib-finite≤ f dA dB finA finB =
  pushout-finite≤ (λ _ → tt) f dA 0 dB finA unit-finite≤ finB
