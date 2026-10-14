{-# OPTIONS --cubical --safe --guardedness #-}
module DeloopS3.Assembly.Final.UnitNaturality where

-- Instantiate localization and contraction naturality on the strict actual
-- cubes, removing the normalized U's refl factors.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws using (lUnit ; rUnit)
open import Cubical.Foundations.Pointed
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
open import DeloopS3.Local.Base using (L ; η)
open import DeloopS3.Local.RouteB2.Common using (SC)
open import DeloopS3.Assembly.LocalizedLoops using (loop-of-localization)
open import DeloopS3.Assembly.Final.Geometry
open import DeloopS3.Assembly.Final.Naturality using (UnitLoopSquare)
import DeloopS3.Assembly.StarCube as Star
import DeloopS3.Assembly.LocalizedFibreNaturality as LF
import DeloopS3.Assembly.ContractibleFibreNaturality as CF

abstract
  pointing-units : {A : Type} {x y : A} (d : x ≡ y)
    → d ∙ refl ≡ refl ∙ refl ∙ d
  pointing-units d = sym (rUnit d) ∙ lUnit d ∙ lUnit (refl ∙ d)

  erase-units : {A : Type} {x y : A} (s : x ≡ y)
    → refl ∙ s ∙ refl ≡ s
  erase-units s = sym (lUnit (s ∙ refl)) ∙ sym (rUnit s)

-- Keep these equivalence wrappers shared with the consumer: their maps
-- remain the existing A2 equivalences, not newly chosen sphere coordinates.
loopG : (c : ShortCase) → SC (P c) → isContr (L (m c) (E c))
  → typ (Ω (Q c)) ≃ L (m c) (Fib c)
loopG c sc d = loop-of-localization (m c) (E c) (P c) (p c)
  (e₀ c) (b c) refl sc d

loopStar : SC P* → isContr (L 30 E*) → typ (Ω T) ≃ L 30 Fib*
loopStar sc d = loop-of-localization 30 E* P* p* e* b* refl sc d

module O (sc : SC (P octa)) (sc* : SC P*)
  (d : isContr (L 3 (E octa))) (d* : isContr (L 30 E*)) where
  module S = CF.LocalizedSquare 3 10 LF.left
    (E octa) (P octa) E* P* (p octa) p* (kE octa) (kP octa) refl
    (e₀ octa) e* (b octa) b* refl refl Star.aO (boundary octa)
    (pointing-units (boundary octa)) sc sc* d d*

  abstract
    normalize : (x : Fib octa) → S.UG x ≡ U octa x
    normalize (x , s) = ΣPathP (refl , erase-units (cong (kP octa) s))

    square : UnitLoopSquare 3 (Fib octa) (typ (Ω (Q octa))) (typ (Ω T)) Fib*
      (loopG octa sc d) (loopStar sc* d*) (fst (Ω→ (u octa))) (U octa)
    square = S.unit-loop-square-for (U octa) normalize

module I (sc : SC (P icosa)) (sc* : SC P*)
  (d : isContr (L 10 (E icosa))) (d* : isContr (L 30 E*)) where
  module S = CF.LocalizedSquare 3 10 LF.right
    (E icosa) (P icosa) E* P* (p icosa) p* (kE icosa) (kP icosa) refl
    (e₀ icosa) e* (b icosa) b* refl refl Star.aI (boundary icosa)
    (pointing-units (boundary icosa)) sc sc* d d*

  abstract
    normalize : (x : Fib icosa) → S.UG x ≡ U icosa x
    normalize (x , s) = ΣPathP
      (refl , sym (lUnit (cong (kP icosa) s ∙ boundary icosa)))

    square : UnitLoopSquare 10 (Fib icosa) (typ (Ω (Q icosa))) (typ (Ω T)) Fib*
      (loopG icosa sc d) (loopStar sc* d*) (fst (Ω→ (u icosa))) (U icosa)
    square = S.unit-loop-square-for (U icosa) normalize

abstract
  unit-loop-square : (c : ShortCase) (sc : SC (P c)) (sc* : SC P*)
    (d : isContr (L (m c) (E c))) (d* : isContr (L 30 E*))
    → UnitLoopSquare (m c) (Fib c) (typ (Ω (Q c))) (typ (Ω T)) Fib*
        (loopG c sc d) (loopStar sc* d*) (fst (Ω→ (u c))) (U c)
  unit-loop-square octa = O.square
  unit-loop-square icosa = I.square
