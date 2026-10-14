{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.ReflectedAttachment where

-- The direct relative 2-cell construction, with its actual cofiber map.
-- H is a boundary compatibility homotopy, not a hypothesis about degree.
-- No torus realization, marking, or homology action is asserted here.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed using (_→∙_)
open import Cubical.Foundations.Equiv using (_≃_ ; idEquiv ; invEq ; secEq)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.Univalence using (EquivJ)
open import Cubical.Foundations.GroupoidLaws using (cong-∙ ; lUnit)
open import Cubical.Data.Fin using (Fin ; fzero)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (not ; false ; true)
open import Cubical.Data.Int using (ℤ ; negsuc)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.HITs.Susp using
  (north ; merid ; suspFun ; SuspBool→S¹)
open import Cubical.HITs.Sn using (S₊ ; S₊∙ ; σSn ; suspFunS∙)
open import Cubical.HITs.Sn.Degree using (degree ; degreeSusp)
open import Cubical.HITs.Pushout using (Pushout ; cofib ; inl ; inr ; push)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; Pushout→Bouquet)
  renaming (BouquetIso-gen to BouquetIso-gen2)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal)
open import DeloopS3.Bridge.DegreeSpan.ProjectH2Sparse using
  (sphereBranch ; branchPush)

-- One-cell bouquet suspension. The unique petal is sent to the unique petal.
pointedSusp : (S₊∙ 1 →∙ S₊∙ 1)
  → SphereBouquet 2 (Fin 1) → SphereBouquet 2 (Fin 1)
pointedSusp r (inl tt) = inl tt
pointedSusp r (inr (k , s)) = sphereBranch true (suspFun (fst r) s)
pointedSusp r (push k i) = branchPush true i

abstract
  -- The basepoint path of r is needed because σSn uses a normalized meridian.
  sigma-natural : (r : S₊∙ 1 →∙ S₊∙ 1) (s : S¹)
    → cong (suspFun (fst r)) (σSn 1 s) ≡ σSn 1 (fst r s)
  sigma-natural r s =
    cong-∙ (suspFun (fst r)) (merid s) (sym (merid base))
    ∙ cong (merid (fst r s) ∙_) (cong (λ a → sym (merid a)) (snd r))

  -- Here suspFunS∙ {n = 1} r .fst is definitionally suspFun r.
  pointedSusp-degree : (r : S₊∙ 1 →∙ S₊∙ 1)
    → degree 2 (λ s → pickPetal fzero (pointedSusp r (inr (fzero , s))))
      ≡ degree 1 (fst r)
  pointedSusp-degree r = sym (degreeSusp 1 (fst r))

module DirectAttachment {X Y : Type}
  (α : Fin 1 × S¹ → X) (β : Fin 1 × S¹ → Y)
  (L : X → Y) (r : S₊∙ 1 →∙ S₊∙ 1)
  (H : (k : Fin 1) (s : S¹) → L (α (k , s)) ≡ β (fzero , fst r s)) where

  Px : Type
  Px = Pushout α fst

  Py : Type
  Py = Pushout β fst

  F : Px → Py
  F (inl x) = inl (L x)
  F (inr k) = inr fzero
  F (push (k , s) i) = (cong inl (H k s) ∙ push (fzero , fst r s)) i

  bx : Px → SphereBouquet 2 (Fin 1)
  bx = Pushout→Bouquet 2 1 α (idEquiv Px)

  by : Py → SphereBouquet 2 (Fin 1)
  by = Pushout→Bouquet 2 1 β (idEquiv Py)

  abstract
    P-push : (k : Fin 1) (s : S¹)
      → cong by (cong inl (H k s) ∙ push (fzero , fst r s))
        ≡ cong (pointedSusp r) (cong bx (push (k , s)))
    P-push k s =
      cong-∙ by (cong inl (H k s)) (push (fzero , fst r s))
      ∙ sym (lUnit (cong by (push (fzero , fst r s))))
      ∙ cong (push fzero ∙_)
          (cong {A = Path (S₊ 2) north north}
            {B = λ _ → Path (SphereBouquet 2 (Fin 1))
              (inr (fzero , north)) (inr (fzero , north))}
            (λ p i → inr (fzero , p i)) (sym (sigma-natural r s)))
      ∙ sym (cong-∙ (pointedSusp r)
          (push k) (λ i → inr (k , σSn 1 s i)))

    P-square : (u : Px)
      → by (F u) ≡ pointedSusp r (bx u)
    P-square (inl x) = refl
    P-square (inr k) = refl
    P-square (push (k , s) i) j = P-push k s j i

  -- These are the actual inclusion, stage map and specified commuting path.
  -- The cofiber push records comm; it must not be discarded during transport.
  module ActualStage {Zx Zy : Type} (eX : Zx ≃ Px) (eY : Zy ≃ Py) where
    stageTop : Zx → Zy
    stageTop = invEq eY ∘ F ∘ fst eX

    incX : X → Zx
    incX = invEq eX ∘ inl

    incY : Y → Zy
    incY = invEq eY ∘ inl

    comm : (x : X) → incY (L x) ≡ stageTop (incX x)
    comm x = sym (cong (invEq eY ∘ F) (secEq eX (inl x)))

    Q : cofib incX → cofib incY
    Q (inl tt) = inl tt
    Q (inr z) = inr (stageTop z)
    Q (push x i) =
      (push (L x)
        ∙ cong {A = Zy} {B = λ _ → cofib incY}
            {x = incY (L x)} {y = stageTop (incX x)} inr (comm x)) i

    CTBx : cofib incX → SphereBouquet 2 (Fin 1)
    CTBx = Iso.fun (BouquetIso-gen2 2 1 α eX)

    CTBy : cofib incY → SphereBouquet 2 (Fin 1)
    CTBy = Iso.fun (BouquetIso-gen2 2 1 β eY)

    quotient : SphereBouquet 2 (Fin 1) → SphereBouquet 2 (Fin 1)
    quotient = CTBy ∘ Q ∘ Iso.inv (BouquetIso-gen2 2 1 α eX)

    quotientDegree : ℤ
    quotientDegree = degree 2 (λ s → pickPetal fzero (quotient (inr (fzero , s))))

  module IdentityStage = ActualStage (idEquiv Px) (idEquiv Py)

  QuotientSquare : {Zx Zy : Type} (eX : Zx ≃ Px) (eY : Zy ≃ Py) → Type
  QuotientSquare eX eY =
    ActualStage.CTBy eX eY ∘ ActualStage.Q eX eY
      ≡ pointedSusp r ∘ ActualStage.CTBx eX eY

  abstract
    identity-outer-push : (x : X)
      → Path (Path (SphereBouquet 2 (Fin 1)) (inl tt) (inl tt))
          (cong IdentityStage.CTBy (cong IdentityStage.Q (push x))) refl
    identity-outer-push x =
      cong-∙ IdentityStage.CTBy (push (L x)) refl ∙ sym (lUnit refl)

    identity-quotient-point : (z : cofib IdentityStage.incX)
      → IdentityStage.CTBy (IdentityStage.Q z)
        ≡ pointedSusp r (IdentityStage.CTBx z)
    identity-quotient-point (inl tt) = refl
    identity-quotient-point (inr u) = P-square u
    identity-quotient-point (push x i) j = identity-outer-push x j i

    identity-quotient-square : QuotientSquare (idEquiv Px) (idEquiv Py)
    identity-quotient-square = funExt identity-quotient-point

    -- Both equivalences, including their secEq-dependent comm, are eliminated.
    quotient-square : {Zx Zy : Type} (eX : Zx ≃ Px) (eY : Zy ≃ Py)
      → QuotientSquare eX eY
    quotient-square {Zx = Zx} {Zy = Zy} eX eY =
      EquivJ
        (λ Zx eX → (Zy : Type) → (eY : Zy ≃ Py) → QuotientSquare eX eY)
        (λ Zy eY → EquivJ
          (λ Zy eY → QuotientSquare (idEquiv Px) eY)
          identity-quotient-square eY)
        eX Zy eY

    bouquet-square : {Zx Zy : Type} (eX : Zx ≃ Px) (eY : Zy ≃ Py)
      → ActualStage.quotient eX eY ≡ pointedSusp r
    bouquet-square eX eY =
      cong (λ f → f ∘ Iso.inv (BouquetIso-gen2 2 1 α eX))
        (quotient-square eX eY)
      ∙ funExt (λ s → cong (pointedSusp r)
          (Iso.sec (BouquetIso-gen2 2 1 α eX) s))

    quotient-degree : {Zx Zy : Type} (eX : Zx ≃ Px) (eY : Zy ≃ Py)
      → ActualStage.quotientDegree eX eY ≡ degree 1 (fst r)
    quotient-degree eX eY =
      cong (λ (f : SphereBouquet 2 (Fin 1) → SphereBouquet 2 (Fin 1)) →
        degree 2 (λ s → pickPetal fzero (f (inr (fzero , s)))))
        (bouquet-square eX eY)
      ∙ pointedSusp-degree r

-- The sign is computed, not inferred merely from involutivity.
reflection : S¹ → S¹
reflection base = base
reflection (loop i) = loop (~ i)

reflection∙ : S₊∙ 1 →∙ S₊∙ 1
reflection∙ = reflection , refl

abstract
  suspended-swap-loop : cong (fst (suspFunS∙ {n = 0} not)) loop ≡ sym loop
  suspended-swap-loop =
    cong-∙ (SuspBool→S¹ ∘ suspFun not) (merid false) (sym (merid true))
    ∙ sym (lUnit (sym loop))

  suspended-swap-reflection : fst (suspFunS∙ {n = 0} not) ≡ reflection
  suspended-swap-reflection = funExt λ
    { base → refl
    ; (loop i) j → suspended-swap-loop j i }

  reflection-degree : degree 1 reflection ≡ negsuc 0
  reflection-degree =
    cong (degree 1) (sym suspended-swap-reflection)
    ∙ sym (degreeSusp 0 not)

module ReflectedAttachment {X Y : Type}
  (α : Fin 1 × S¹ → X) (β : Fin 1 × S¹ → Y)
  (L : X → Y)
  (H : (k : Fin 1) (s : S¹) → L (α (k , s)) ≡ β (fzero , reflection s)) where

  module Direct = DirectAttachment α β L reflection∙ H

  abstract
    quotient-degree-minus-one : {Zx Zy : Type}
      (eX : Zx ≃ Direct.Px) (eY : Zy ≃ Direct.Py)
      → Direct.ActualStage.quotientDegree eX eY ≡ negsuc 0
    quotient-degree-minus-one eX eY =
      Direct.quotient-degree eX eY ∙ reflection-degree
