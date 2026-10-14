{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- The oriented pullback uses the literal q of RP2UnitFiber.
-- No choice of a circle fibre trivializes the family over the sphere.
module DeloopS3.Seifert.TwistedBundle.TwoCap where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (isEquivFromIsContr)
import Cubical.Foundations.Equiv.Fiberwise as FW
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emsquash)
open import Cubical.HITs.EilenbergMacLane1.Properties using (elimSet)
open import Cubical.Foundations.Path using (symIso)
open import Cubical.Foundations.Transport using (substCommSlice)
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Sum using (_⊎_) renaming (inl to left; inr to right)
open import Cubical.Data.Int as Z using (ℤ; pos)
open import Cubical.Data.NatMinusOne
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import Cubical.HITs.Susp.Base using (Susp; north; south; merid)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.RPn.Base using (Bool*; cov⁻¹; TotalCov≃Sn)
open import DeloopS3.Move.CancelMinimal
  using (C; K; 0K; U; ω; ω-add; transport-U; mulC; _+C_;
         ua-equiv-family; Σ-over-equiv)
import DeloopS3.Move.CancelGeneral as R1
open import DeloopS3.Seifert.TwistedBundle.SignCircle
open import DeloopS3.Seifert.TwistedBundle.Base using (R; w₁; A; δ; fA)
open import DeloopS3.Seifert.TwistedBundle.Coherent
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
import DeloopS3.Seifert.TwistedBundle.Chart as Chart
open import DeloopS3.Sphere.RP2UnitFiber using (RP²; q; S²≃S2)

-- Evaluation of paths in a family with contractible total space.
-- This version computes as transport rather than as the J recursor.
module ContractibleTotal {ℓ ℓ' : Level} {X : Type ℓ}
  (Y : X → Type ℓ') (c : isContr (Σ X Y)) where
  x₀ = c .fst .fst
  y₀ = c .fst .snd

  abstract
    evaluate : (x : X) → (x₀ ≡ x) ≃ Y x
    evaluate x .fst p = subst Y p y₀
    evaluate x .snd = FW.fiberEquiv (λ x → x₀ ≡ x) Y
      (λ x p → subst Y p y₀)
      (isEquivFromIsContr (λ { (x , p) → x , subst Y p y₀ })
        (isContrSingl x₀) c) x

    evaluate-compute : (x : X) (p : x₀ ≡ x)
      → evaluate x .fst p ≡ subst Y p y₀
    evaluate-compute x p = refl

-- Contract precisely the universal pointed torsor, keeping its family.
actionCover : SAct Bool* ≃ Σ QuotientBase (Reg ∘ fst)
actionCover = compEquiv
  (invEquiv (Σ-contractFst {B = λ r → SAct (fst r)} rightContractible))
  (isoToEquiv (iso
    (λ { ((T , y) , s) → (T , s) , y })
    (λ { ((T , s) , y) → (T , y) , s })
    (λ _ → refl) (λ _ → refl)))

libraryCover : Type
libraryCover = Σ RP² (Reg ∘ cov⁻¹ 2)

coverSphere : libraryCover ≃ S₊ 2
coverSphere = compEquiv (TotalCov≃Sn 2) (invEquiv S²≃S2)

abstract
  coverSphere-over : (v : libraryCover) → q (coverSphere .fst v) ≡ fst v
  coverSphere-over v = cong fst
    (cong (invEq (TotalCov≃Sn 2)) (secEq S²≃S2 (TotalCov≃Sn 2 .fst v))
      ∙ retEq (TotalCov≃Sn 2) v)

  actionSphere : SAct Bool* ≃ S₊ 2
  actionSphere = compEquiv actionCover (compEquiv coverTotalEquiv coverSphere)

  actionSphere-over : (s : SAct Bool*)
    → q (actionSphere .fst s) ≡ baseQuotient .fst (Bool* , s)
  actionSphere-over s = coverSphere-over (coverTotalEquiv .fst (actionCover .fst s))
    ∙ coverTotal-over (actionCover .fst s)

module TorsorEvaluation = ContractibleTotal Reg rightContractible

equatorChart : Â Bool* ≃ A
equatorChart = Σ-cong-equiv-snd λ x →
  compEquiv (isoToEquiv symIso) (TorsorEvaluation.evaluate (w₁ x))

abstract
  equatorChart-compute : (a : Â Bool*)
    → equatorChart .fst a ≡ backPoint Bool* a false
  equatorChart-compute (x , p) = ΣPathP
    (refl , TorsorEvaluation.evaluate-compute (w₁ x) (sym p))

  op-false : op Bool* false ≡ true
  op-false = refl

  op-true : op Bool* true ≡ false
  op-true = refl

  backPoint-op : (a : Â Bool*)
    → backPoint Bool* a true ≡ δ (backPoint Bool* a false)
  backPoint-op (x , p) = ΣPathP (refl ,
    (cong (subst Reg (sym p)) (sym op-false)
      ∙ substCommSlice Reg Reg op (sym p) false))

  mulC-one : (a : C) → mulC (pos 1) a ≡ a
  mulC-one = elimSet ℤGroup (λ _ → emsquash _ _) refl (λ n i j → emloop n i)

  negC-mulC : (e : ℤ) (a : C) → negC (mulC e a) ≡ mulC (Z.- e) a
  negC-mulC e = elimSet ℤGroup (λ _ → emsquash _ _) refl
    (λ n i j → emloop (Z.-DistL· e n j) i)

equatorCircle : Â Bool* ≃ C
equatorCircle = compEquiv equatorChart fA

module Pullback (e : ℤ) where
  open Bundle e using (Fₑ; actionFamily)
  open Action e

  abstract
    pullbackAction : (s : SAct Bool*)
      → Fₑ (q (actionSphere .fst s)) ≃ FAct Bool* s
    pullbackAction s = compEquiv
      (pathToEquiv (cong Fₑ (actionSphere-over s)))
      (pathToEquiv (cong actionFamily (retEq baseQuotient (Bool* , s))))

  -- These are the two actual seam maps before using the deck homotopy.
  seam : Bool → Â Bool* → C
  seam b a = ε Bool* false .fst (clutching Bool* a b)

  abstract
    seam-false : (a : Â Bool*)
      → seam false a ≡ mulC e (fA .fst (backPoint Bool* a false))
    seam-false a = secEq (ε Bool* false)
      (mulC e (fA .fst (backPoint Bool* a false)))

    seam-true : (a : Â Bool*)
      → seam true a ≡ mulC (Z.- e) (fA .fst (δ (backPoint Bool* a false)))
    seam-true a =
      cong (λ y → ε Bool* y .fst (clutching Bool* a true)) (sym op-true)
      ∙ ε-op Bool* true (clutching Bool* a true)
      ∙ cong negC (secEq (ε Bool* true)
          (mulC e (fA .fst (backPoint Bool* a true))))
      ∙ negC-mulC e (fA .fst (backPoint Bool* a true))
      ∙ cong (mulC (Z.- e) ∘ fA .fst) (backPoint-op a)

  actionClass : SAct Bool* → K
  actionClass (inl a) = 0K
  actionClass (inr b) = 0K
  actionClass (push (a , b) i) = ω .fst (seam b a) i

  abstract
    seam-naturality : (a : Â Bool*) (b : Bool) (t : SignC Bool*)
      → ω .fst (ε Bool* false .fst (_+S_ {T = Bool*} t (clutching Bool* a b)))
        ≡ transport (cong U (ω .fst (seam b a)))
            (ω .fst (ε Bool* false .fst t))
    seam-naturality a b t =
      cong (ω .fst) (ε-add Bool* false t (clutching Bool* a b))
      ∙ ω-add (ε Bool* false .fst t) (seam b a)
      ∙ sym (transport-U (ω .fst (seam b a)) (ω .fst (ε Bool* false .fst t)))

  actionFamilyComparison : (s : SAct Bool*) → FAct Bool* s ≃ U (actionClass s)
  actionFamilyComparison (inl a) = compEquiv (ε Bool* false) ω
  actionFamilyComparison (inr b) = compEquiv (ε Bool* false) ω
  actionFamilyComparison (push (a , b) i) =
    ua-equiv-family (rot {T = Bool*} (clutching Bool* a b))
      (λ i → U (ω .fst (seam b a) i))
      (compEquiv (ε Bool* false) ω) (compEquiv (ε Bool* false) ω)
      (λ t → toPathP (sym (seam-naturality a b t))) i

  class : S₊ 2 → K
  class x = actionClass (invEq actionSphere x)

  -- Comparison along the literal q on the stock sphere. Calibrated below
  -- identifies this class with coefficient -2e in its suspension chart.
  familyComparison : (x : S₊ 2) → Fₑ (q x) ≃ U (class x)
  familyComparison x = compEquiv
    (pathToEquiv (cong (Fₑ ∘ q) (sym (secEq actionSphere x))))
    (compEquiv (pullbackAction (invEq actionSphere x))
      (actionFamilyComparison (invEq actionSphere x)))

  totalComparison : Σ (S₊ 2) (Fₑ ∘ q) ≃ Σ (S₊ 2) (U ∘ class)
  totalComparison = Σ-cong-equiv-snd familyComparison

-- The suspension orientation, independently of the stock sphere chart.
suspensionClass : ℤ → Susp C → K
suspensionClass d north = 0K
suspensionClass d south = 0K
suspensionClass d (merid a i) = ω .fst (mulC d a) i

-- Keep the deck homotopy and its vertex paths explicit in the generic
-- comparison. Calibrated below instantiates it with Chart.H.
module Normalized (e : ℤ)
  (H : (a : A) → fA .fst (δ a) ≡ fA .fst a) where
  module P = Pullback e
  module Caps = R1.TwoCap e (Z.- e) (pos 1)

  capsChart : Bool ≃ (Unit ⊎ Unit)
  capsChart = isoToEquiv (iso to from sec ret)
    where
    to : Bool → Unit ⊎ Unit
    to false = left tt
    to true = right tt
    from : Unit ⊎ Unit → Bool
    from (left tt) = false
    from (right tt) = true
    sec : (b : Unit ⊎ Unit) → to (from b) ≡ b
    sec (left tt) = refl
    sec (right tt) = refl
    ret : (b : Bool) → from (to b) ≡ b
    ret false = refl
    ret true = refl

  seamsChart : (Â Bool* × Bool) ≃ (C ⊎ C)
  seamsChart = isoToEquiv (iso to from sec ret)
    where
    to : Â Bool* × Bool → C ⊎ C
    to (a , false) = left (equatorCircle .fst a)
    to (a , true) = right (equatorCircle .fst a)
    from : C ⊎ C → Â Bool* × Bool
    from (left a) = invEq equatorCircle a , false
    from (right a) = invEq equatorCircle a , true
    sec : (z : C ⊎ C) → to (from z) ≡ z
    sec (left a) = cong left (secEq equatorCircle a)
    sec (right a) = cong right (secEq equatorCircle a)
    ret : (z : Â Bool* × Bool) → from (to z) ≡ z
    ret (a , false) = ΣPathP (retEq equatorCircle a , refl)
    ret (a , true) = ΣPathP (retEq equatorCircle a , refl)

  leftSquare : (z : Â Bool* × Bool)
    → equatorCircle .fst (fst z) ≡ Caps.T.all-left (seamsChart .fst z)
  leftSquare (a , false) = refl
  leftSquare (a , true) = sym (mulC-one (equatorCircle .fst a))

  rightSquare : (z : Â Bool* × Bool)
    → capsChart .fst (snd z) ≡ Caps.T.all-right (seamsChart .fst z)
  rightSquare (a , false) = refl
  rightSquare (a , true) = refl

  actionTwoCap : SAct Bool* ≃ Caps.O₂
  actionTwoCap = pushoutEquiv fst snd Caps.T.all-left Caps.T.all-right
    seamsChart equatorCircle capsChart (funExt leftSquare) (funExt rightSquare)

  capVertex : Unit ⊎ Unit → Caps.O₂
  capVertex = inr

  signed : Bool → ℤ
  signed false = e
  signed true = Z.- e

  abstract
    normalized-seam : (a : Â Bool*) (b : Bool)
      → P.seam b a ≡ mulC (signed b) (equatorCircle .fst a)
    normalized-seam a false = P.seam-false a
      ∙ cong (mulC e ∘ fA .fst) (sym (equatorChart-compute a))
    normalized-seam a true = P.seam-true a
      ∙ cong (mulC (Z.- e)) (H (backPoint Bool* a false))
      ∙ cong (mulC (Z.- e) ∘ fA .fst) (sym (equatorChart-compute a))

    normalize-units : ∀ {ℓ} {X : Type ℓ} {x y : X} (p : x ≡ y)
      → refl ∙∙ p ∙∙ refl ≡ p
    normalize-units p = doubleCompPath-elim refl p refl
      ∙ sym (rUnit (refl ∙ p)) ∙ sym (lUnit p)

    marked-seam-false : (a : Â Bool*)
      → cong (Caps.c₂ ∘ actionTwoCap .fst) (push (a , false))
        ≡ ω .fst (mulC e (equatorCircle .fst a))
    marked-seam-false a =
      cong-∙∙ Caps.c₂ (cong inl (leftSquare (a , false)))
        (push (seamsChart .fst (a , false))) (cong capVertex (sym (rightSquare (a , false))))
      ∙ normalize-units (ω .fst (mulC e (equatorCircle .fst a)))
    marked-seam-true : (a : Â Bool*)
      → cong (Caps.c₂ ∘ actionTwoCap .fst) (push (a , true))
        ≡ ω .fst (mulC (Z.- e) (equatorCircle .fst a))
    marked-seam-true a =
      cong-∙∙ Caps.c₂ (cong inl (leftSquare (a , true)))
        (push (seamsChart .fst (a , true))) (cong capVertex (sym (rightSquare (a , true))))
      ∙ normalize-units (ω .fst (mulC (Z.- e) (equatorCircle .fst a)))

  marking-comparison : (s : SAct Bool*)
    → P.actionClass s ≡ Caps.c₂ (actionTwoCap .fst s)
  marking-comparison (inl a) = refl
  marking-comparison (inr false) = refl
  marking-comparison (inr true) = refl
  marking-comparison (push (a , false) i) j =
    (cong (ω .fst) (normalized-seam a false) ∙ sym (marked-seam-false a)) j i
  marking-comparison (push (a , true) i) j =
    (cong (ω .fst) (normalized-seam a true) ∙ sym (marked-seam-true a)) j i

  -- This is the R1 base equivalence, not an unmarked replacement.
  sphereTwoCap : S₊ 2 ≃ Susp C
  sphereTwoCap = compEquiv (invEquiv actionSphere)
    (compEquiv actionTwoCap Caps.two-cap-base)

  remaining-shear : (a : C)
    → Caps.Mark.τ′ a ≡ ω .fst (mulC ((Z.- e) Z.- e) a)
  remaining-shear = Caps.remaining-shear

  actionPathTotal : Σ (SAct Bool*) (U ∘ P.actionClass)
    ≃ Σ Caps.O₂ (U ∘ Caps.c₂)
  actionPathTotal = Σ-over-equiv U (actionTwoCap , marking-comparison)

  -- Both marked total equivalences are retained, including the changed
  -- second seam. Replacing them by a bare sphere equivalence loses e.
  normalizedTotal : Σ (S₊ 2) (Bundle.Fₑ e ∘ q)
    ≃ Σ Caps.Rpl.O′ (U ∘ Caps.normalized-mark)
  normalizedTotal = compEquiv P.totalComparison
    (compEquiv (Σ-cong-equiv-fst {B = U ∘ P.actionClass} (invEquiv actionSphere))
      (compEquiv actionPathTotal (invEquiv Caps.two-cap-total)))

  degree : ℤ
  degree = Z.- (pos 2 Z.· e)

  abstract
    coefficient : Caps.e ≡ degree
    coefficient = sym (Z.-Dist+ e e)

    remaining-shear-minus-twice : (a : C)
      → Caps.Mark.τ′ a ≡ ω .fst (mulC degree a)
    remaining-shear-minus-twice a = Caps.remaining-shear a
      ∙ cong (λ d → ω .fst (mulC d a)) coefficient

  sphereReduced : S₊ 2 ≃ Caps.Rpl.O′
  sphereReduced = compEquiv (invEquiv actionSphere)
    (compEquiv actionTwoCap (invEquiv Caps.cancel-two-cap))

  calibratedSphere : S₊ 2 ≃ Susp C
  calibratedSphere = compEquiv sphereReduced Caps.reduced-base

  reduced-marking : (x : S₊ 2)
    → P.class x ≡ Caps.normalized-mark (sphereReduced .fst x)
  reduced-marking x = marking-comparison (invEq actionSphere x)
    ∙ cong Caps.c₂ (sym (secEq Caps.cancel-two-cap
        (actionTwoCap .fst (invEq actionSphere x))))
    ∙ sym (Caps.two-cap-marked .snd (sphereReduced .fst x))

  suspension-marking : (z : Caps.Rpl.O′)
    → Caps.normalized-mark z ≡ suspensionClass degree (Caps.reduced-base .fst z)
  suspension-marking (inl tt) = refl
  suspension-marking (inr tt) = refl
  suspension-marking (push a i) j = ω .fst (mulC (coefficient j) a) i

  calibratedClass : S₊ 2 → K
  calibratedClass x = suspensionClass degree (calibratedSphere .fst x)

  class-comparison : (x : S₊ 2) → P.class x ≡ calibratedClass x
  class-comparison x = reduced-marking x ∙ suspension-marking (sphereReduced .fst x)

  -- The varying path-family comparison uses calibratedSphere's orientation;
  -- it does not identify that orientation positively with the stock chart.
  calibratedFamilyComparison : (x : S₊ 2)
    → Bundle.Fₑ e (q x) ≃ U (calibratedClass x)
  calibratedFamilyComparison x = compEquiv (P.familyComparison x)
    (pathToEquiv (cong U (class-comparison x)))

  calibratedTotal : Σ (S₊ 2) (Bundle.Fₑ e ∘ q)
    ≃ Σ (S₊ 2) (U ∘ calibratedClass)
  calibratedTotal = Σ-cong-equiv-snd calibratedFamilyComparison

  calibratedTotal-over : (v : Σ (S₊ 2) (Bundle.Fₑ e ∘ q))
    → calibratedTotal .fst v .fst ≡ v .fst
  calibratedTotal-over v = refl

-- Specialize to the deck homotopy of the existing library chart,
-- retaining all vertex paths.
module Calibrated (e : ℤ) where
  open Normalized e Chart.H public
