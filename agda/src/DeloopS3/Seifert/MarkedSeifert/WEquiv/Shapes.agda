{-# OPTIONS --safe --cubical #-}

-- Generic untruncated shapes.
module DeloopS3.Seifert.MarkedSeifert.WEquiv.Shapes where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_) renaming (inl to left; inr to right)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv; pushoutSwitchEquiv)
open import DeloopS3.Move.CancelMinimalCore using (module IdentityCancellation)

-- Arbitrary right vertices, unlike Move.CancelGeneral.Staging.
module Stage {ℓ : Level} {L A B R S : Type ℓ}
  (a : A → L) (b : B → L) (f : A → R) (g : B → S) where
  allLeft : A ⊎ B → L
  allLeft (left x) = a x
  allLeft (right x) = b x
  allRight : A ⊎ B → R ⊎ S
  allRight (left x) = left (f x)
  allRight (right x) = right (g x)
  All = Pushout allLeft allRight
  First = Pushout a f
  remaining : B → First
  remaining = inl ∘ b
  Staged = Pushout remaining g

  forward : All → Staged
  forward (inl z) = inl (inl z)
  forward (inr (left z)) = inl (inr z)
  forward (inr (right z)) = inr z
  forward (push (left z) i) = inl (push z i)
  forward (push (right z) i) = push z i
  backFirst : First → All
  backFirst (inl z) = inl z
  backFirst (inr z) = inr (left z)
  backFirst (push z i) = push (left z) i
  backward : Staged → All
  backward (inl z) = backFirst z
  backward (inr z) = inr (right z)
  backward (push z i) = push (right z) i
  secFirst : (z : First) → forward (backFirst z) ≡ inl z
  secFirst (inl z) = refl
  secFirst (inr z) = refl
  secFirst (push z i) = refl
  sec : (z : Staged) → forward (backward z) ≡ z
  sec (inl z) = secFirst z
  sec (inr z) = refl
  sec (push z i) = refl
  ret : (z : All) → backward (forward z) ≡ z
  ret (inl z) = refl
  ret (inr (left z)) = refl
  ret (inr (right z)) = refl
  ret (push (left z) i) = refl
  ret (push (right z) i) = refl
  abstract
    stage₂ : All ≃ Staged
    stage₂ = isoToEquiv (iso forward backward sec ret)
    stage₂-left : (z : L) → stage₂ .fst (inl z) ≡ inl (inl z)
    stage₂-left z = refl

-- Constant-family flattening, with literal vertex and seam computations.
module Product {ℓ : Level} {A B C : Type ℓ}
  (f : A → B) (g : A → C) (D : Type ℓ) where
  leftMap : A × D → B × D
  leftMap (a , d) = f a , d
  rightMap : A × D → C × D
  rightMap (a , d) = g a , d
  Total = Pushout leftMap rightMap
  forward : Pushout f g × D → Total
  forward (inl b , d) = inl (b , d)
  forward (inr c , d) = inr (c , d)
  forward (push a i , d) = push (a , d) i
  backward : Total → Pushout f g × D
  backward (inl (b , d)) = inl b , d
  backward (inr (c , d)) = inr c , d
  backward (push (a , d) i) = push a i , d
  sec : (z : Total) → forward (backward z) ≡ z
  sec (inl z) = refl
  sec (inr z) = refl
  sec (push z i) = refl
  ret : (z : Pushout f g × D) → backward (forward z) ≡ z
  ret (inl b , d) = refl
  ret (inr c , d) = refl
  ret (push a i , d) = refl
  abstract
    productPushout : (Pushout f g × D) ≃ Total
    productPushout = isoToEquiv (iso forward backward sec ret)
    product-left : (b : B) (d : D)
      → productPushout .fst (inl b , d) ≡ inl (b , d)
    product-left b d = refl
    product-right : (c : C) (d : D)
      → productPushout .fst (inr c , d) ≡ inr (c , d)
    product-right c d = refl
    product-seam : (a : A) (d : D)
      → PathP (λ k → product-left (f a) d k ≡ product-right (g a) d k)
          (cong (λ z → productPushout .fst (z , d)) (push a)) (push (a , d))
    product-seam a d = refl

-- Reassociate to expose Pushout id f, then use R1.
module AttachLeft {ℓ : Level} {H A B X : Type ℓ}
  (a : H → A) (b : H → B) (f : A → X) where
  V = Pushout a b
  inc : A → V
  inc = inl
  Attached = Pushout inc f
  module R1 = IdentityCancellation {A = A} {R = X} f
  newLeft : H → R1.E
  newLeft = inl ∘ a
  Exposed = Pushout newLeft b
  forward : Attached → Exposed
  forward (inl (inl z)) = inl (inl z)
  forward (inl (inr z)) = inr z
  forward (inl (push z i)) = push z i
  forward (inr z) = inl (inr z)
  forward (push z i) = inl (push z i)
  backFirst : R1.E → Attached
  backFirst (inl z) = inl (inl z)
  backFirst (inr z) = inr z
  backFirst (push z i) = push z i
  backward : Exposed → Attached
  backward (inl z) = backFirst z
  backward (inr z) = inl (inr z)
  backward (push z i) = inl (push z i)
  secFirst : (z : R1.E) → forward (backFirst z) ≡ inl z
  secFirst (inl z) = refl
  secFirst (inr z) = refl
  secFirst (push z i) = refl
  sec : (z : Exposed) → forward (backward z) ≡ z
  sec (inl z) = secFirst z
  sec (inr z) = refl
  sec (push z i) = refl
  retVertex : (z : V) → backward (forward (inl z)) ≡ inl z
  retVertex (inl z) = refl
  retVertex (inr z) = refl
  retVertex (push z i) = refl
  ret : (z : Attached) → backward (forward z) ≡ z
  ret (inl z) = retVertex z
  ret (inr z) = refl
  ret (push z i) = refl
  abstract
    expose : Attached ≃ Exposed
    expose = isoToEquiv (iso forward backward sec ret)
    cancel : Attached ≃ Pushout (f ∘ a) b
    cancel = compEquiv expose
      (pushoutEquiv newLeft b (f ∘ a) b
        (idEquiv H) R1.cancel (idEquiv B) refl refl)
    cancel-other : (z : B) → cancel .fst (inl (inr z)) ≡ inr z
    cancel-other z = refl
    cancel-core : (z : X) → cancel .fst (inr z) ≡ inl z
    cancel-core z = refl

module FillBoth {ℓ : Level} {H A B X Y : Type ℓ}
  (a : H → A) (b : H → B) (f : A → X) (g : B → Y) where
  V = Pushout a b
  incA : A → V
  incA = inl
  incB : B → V
  incB = inr
  module S = Stage incA incB f g
  module F = AttachLeft a b f
  Joint = Pushout (f ∘ a) b
  incB′ : B → Joint
  incB′ = inr
  Jswap = Pushout b (f ∘ a)
  incB″ : B → Jswap
  incB″ = inl
  module G = AttachLeft b (f ∘ a) g
  abstract
    first : S.Staged ≃ Pushout incB′ g
    first = pushoutEquiv S.remaining g incB′ g
      (idEquiv B) F.cancel (idEquiv Y) (funExt F.cancel-other) refl
    switchMiddle : Pushout incB′ g ≃ Pushout incB″ g
    switchMiddle = pushoutEquiv incB′ g incB″ g
      (idEquiv B) (pushoutSwitchEquiv {f = f ∘ a} {g = b})
      (idEquiv Y) refl refl
    fillBoth : S.All ≃ Pushout (f ∘ a) (g ∘ b)
    fillBoth = compEquiv S.stage₂
      (compEquiv first (compEquiv switchMiddle
        (compEquiv G.cancel (pushoutSwitchEquiv {f = g ∘ b} {g = f ∘ a}))))
