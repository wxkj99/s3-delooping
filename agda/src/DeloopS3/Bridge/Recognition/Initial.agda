{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Recognition.Initial where

-- Naturality for the specified map, followed by bounded Whitehead on
-- its 3-truncation.
open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Bridge.Recognition.Hurewicz
open import DeloopS3.Bridge.Recognition.TruncatedMap
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base using (π'∘∙Hom)
open import Cubical.CW.HurewiczTheorem using (HurewiczMapNat)

private
  abstract
    equiv-from-square : {A B HA HB : Type}
      (eA : A ≃ HA) (eB : B ≃ HB) (h : HA → HB) (f : A → B)
      → isEquiv h → h ∘ fst eA ≡ fst eB ∘ f → isEquiv f
    equiv-from-square eA eB h f eh square =
      subst isEquiv
        (cong (invEq eB ∘_) square ∙ funExt (λ a → retEq eB (f a)))
        (snd (compEquiv (compEquiv eA (h , eh)) (invEquiv eB)))

H₃-iso→connected4 : (A B : CW₀) (f : fst A → fst B)
  → isConnected 4 (fst A) → isConnected 4 (fst B)
  → Hiso A B 3 f → isConnectedFun 4 f
H₃-iso→connected4 A B f connA connB isoH =
  π₃-iso→connected4 f connA connB πf-equiv
  where
  abstract
    πf-equiv : (a : fst A) → isEquiv (fst (π'∘∙Hom {A = fst A , a} 2 (f , refl)))
    πf-equiv a = equiv-from-square
      (hurewicz-equiv A 1 connA a) (hurewicz-equiv B 1 connB (f a))
      (fst (H̃ᶜʷ→ {C = A} {D = B} 3 f))
      (fst (π'∘∙Hom {A = fst A , a} 2 (f , refl))) isoH
      (HurewiczMapNat {n = 2} A B a (f a) (f , refl))
