{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Fracture.Assembly where

-- The arithmetic fracture assembly applies fibre localization,
-- followed by the marked overlap/cospan comparison.  No loop reflection
-- or connectivity assertion about the pullback is used.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; _·_)
open import DeloopS3.Local.Base using (F ; L ; η)
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.RouteB2 using (L-map ; L-preserves-SC)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (SC ; module Square)
open import DeloopS3.Local.Fracture.Arithmetic.Bezout using (Bezout)
open import DeloopS3.Local.Fracture.RouteBWrap using (local-fibres-unit-cartesian)
open import DeloopS3.Local.Fracture.Heart using (coprime-unit-fibres-local)
open import DeloopS3.Local.Fracture.Overlap using
  (iterated-localization ; iterated-localization-β)
open import DeloopS3.Local.Fracture.Fracture.Maps
open import DeloopS3.Local.Fracture.Fracture.Pullback using (module ChangeApex ; marked-refl)

module Assembly (m n : ℕ) (A : Type) (sc : SC A) where
  private
    Iter : Type
    Iter = L m (L n A)
    P : Type
    P = L (m · n) A
    u : A → L m A
    u = η {m} {A}
    v : A → L n A
    v = η {n} {A}
    f : L m A → Iter
    f = L-map m {A = A} {B = L n A} v
    g : L n A → Iter
    g = η {m} {L n A}
    k : Iter → P
    k = equivFun (iterated-localization m n {A = A} sc)

  abstract
    overlap-isEquiv : isEquiv k
    overlap-isEquiv = snd (iterated-localization m n {A = A} sc)

  -- Both homotopies are extended with the same specified unit value,
  -- rather than obtained as unmarked equalities of the cospan maps.
  compare-m : (x : L m A) → k (f x) ≡ ι_m m n A x
  compare-m = Unique.≡onη {F = F m} {X = A} {Y = P}
    (overlap-local-m m n A) (k ∘ f) (ι_m m n A)
    (iterated-localization-β m n {A = A} sc)

  compare-n : (y : L n A) → k (g y) ≡ ι_n m n A y
  compare-n = Unique.≡onη {F = F n} {X = A} {Y = P}
    (overlap-local-n m n A) (k ∘ g) (ι_n m n A)
    (iterated-localization-β m n {A = A} sc)

  compare-m-β : (a : A) → compare-m (u a)
    ≡ iterated-localization-β m n {A = A} sc a
  compare-m-β a = refl

  compare-n-β : (a : A) → compare-n (v a)
    ≡ iterated-localization-β m n {A = A} sc a
  compare-n-β a = refl

  private
    module Change = ChangeApex (L m A) (L n A) Iter P k
      f g (ι_m m n A) (ι_n m n A) compare-m compare-n

    old-gap : A → PB {A = L m A} {B = L n A} {C = Iter} f g
    old-gap a = u a , v a , refl

  abstract
    target-isEquiv : isEquiv Change.map
    target-isEquiv = Change.map-isEquiv overlap-isEquiv

    gap-comparison : Change.map ∘ old-gap ≡ fracture-unit m n A
    gap-comparison = funExt λ a →
      cong (λ q → u a , v a , q)
        (marked-refl P (k (g (v a))) (η {m · n} {A} a)
          (iterated-localization-β m n {A = A} sc a))

    -- This is the cartesian fracture square.  Its base is L_n A,
    -- whose simple connectedness is supplied by the stable Route B export.
    unit-square-cartesian : (a : A) → SC (a ≡ a) → Bezout m n
      → isEquiv old-gap
    unit-square-cartesian a scΩ bez = local-fibres-unit-cartesian m
      {E = A} {B = L n A} v (L-preserves-SC n {X = A} sc)
      (coprime-unit-fibres-local m n (A , a) sc scΩ bez)

    pointed-fracture : (a : A) → SC (a ≡ a) → Bezout m n
      → isEquiv (fracture-unit m n A)
    pointed-fracture a scΩ bez = subst
      (isEquiv {A = A}
        {B = PB {A = L m A} {B = L n A} {C = P} (ι_m m n A) (ι_n m n A)})
      gap-comparison
      (snd (compEquiv (old-gap , unit-square-cartesian a scΩ bez)
        (Change.map , target-isEquiv)))
