{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.FiniteSpanWitness where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (cong-∙ ; assoc ; lUnit ; rUnit)
open import Cubical.Data.Nat using (suc)
open import Cubical.Data.Fin.Base using (Fin ; injectSuc ; fsuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.Data.FinSequence using (FinSequenceMap)
open import Cubical.HITs.SequentialColimit
  using (FinSeqColim ; FinSeqColim→Colim ; fincl ; fpush ; incl ; push)
open import Cubical.HITs.PropositionalTruncation as PT
  using (∥_∥₁ ; ∣_∣₁ ; squash₁)
open import Cubical.CW.Base
open import Cubical.CW.Map
  using (cellMap ; realiseCellMap ; finCellMap ; finCellMap↓ ;
         composeFinCellMap ; finCellMap→FinSeqColim)
open import Cubical.CW.Approximation
  using (finCellApprox ; finCellHomRel ; CWmap→finCellMap)
open import Cubical.CW.Strictification using (strictCWskel)
open import DeloopS3.Bridge.DegreeSpan.MarkedHomotopy
  using (marked-finite-homotopy)
import DeloopS3.Bridge.DegreeSpan.TotalWindowStage as Stage

open FinSequenceMap

-- Only the fixed windows needed by TotalWindowStage are used below.
private
  variable
    ℓ : Level

  Col5 : CWskel ℓ → Type ℓ
  Col5 C = FinSeqColim 5 (realiseSeq C)

  incl5 : (C : CWskel ℓ) → Col5 C → realise C
  incl5 C = FinSeqColim→Colim 5

  map5 : (C D : CWskel ℓ) → finCellMap 5 C D → Col5 C → Col5 D
  map5 C D = finCellMap→FinSeqColim C D

  real5 : (C D : CWskel ℓ) → finCellMap 5 C D → Col5 C → realise D
  real5 C D f = incl5 D ∘ map5 C D f

  -- Restrict the actual track, rather than extend its top-stage value.
  track↓ : {C D : CWskel ℓ} {u : realise C → realise D}
    (a : finCellApprox C D u 6)
    → real5 C D (finCellMap↓ (fst a)) ≡ u ∘ incl5 C
  track↓ a = funExt λ
    { (fincl n x) j → snd a j (fincl (injectSuc n) x)
    ; (fpush n x i) j → snd a j (fpush (injectSuc n) x i) }

  -- Realization of a restricted infinite cellular map, with reflexive
  -- inclusion component. The push component is the composition law.
  restrict-real5 : {C D : CWskel ℓ} (f : cellMap C D)
    → real5 C D (Stage.restrictCell f 5)
      ≡ realiseCellMap {C = C} {D = D} f ∘ incl5 C
  restrict-real5 {D = D} f = funExt λ
    { (fincl n x) → refl
    ; (fpush n x i) j → cong-∙ (incl5 D)
        (fpush n (SequenceMap.map f (fst n) x))
        (cong (fincl (fsuc n)) (SequenceMap.comm f (fst n) x)) j i }

  -- Finite-colimit composition, retaining reflexive fincl components.
  map5-comp : {C D E : CWskel ℓ}
    (g : finCellMap 5 D E) (f : finCellMap 5 C D)
    → map5 C E (composeFinCellMap 5 g f)
      ≡ map5 D E g ∘ map5 C D f
  map5-comp {C = C} {D = D} {E = E} g f = funExt λ
    { (fincl n x) → refl
    ; (fpush n x i) j → main n x j i }
    where
    main : (n : Fin 5) (x : fst C (fst n))
      → (fpush n (fmap g (injectSuc n) (fmap f (injectSuc n) x))
          ∙ cong (fincl (fsuc n))
              (fcomm g n (fmap f (injectSuc n) x)
                ∙ cong (fmap g (fsuc n)) (fcomm f n x)))
        ≡ cong (map5 D E g)
            (fpush n (fmap f (injectSuc n) x)
              ∙ cong (fincl (fsuc n)) (fcomm f n x))
    main n x =
      cong (fpush n (fmap g (injectSuc n) (fmap f (injectSuc n) x)) ∙_)
        (cong-∙ (fincl (fsuc n))
          (fcomm g n (fmap f (injectSuc n) x))
          (cong (fmap g (fsuc n)) (fcomm f n x)))
      ∙ assoc
          (fpush n (fmap g (injectSuc n) (fmap f (injectSuc n) x)))
          (cong (fincl (fsuc n)) (fcomm g n (fmap f (injectSuc n) x)))
          (cong (fincl (fsuc n) ∘ fmap g (fsuc n)) (fcomm f n x))
      ∙ sym (cong-∙ (map5 D E g)
          (fpush n (fmap f (injectSuc n) x))
          (cong (fincl (fsuc n)) (fcomm f n x)))

  real5-comp : {C D E : CWskel ℓ}
    (g : finCellMap 5 D E) (f : finCellMap 5 C D)
    → real5 C E (composeFinCellMap 5 g f)
      ≡ real5 D E g ∘ map5 C D f
  real5-comp {E = E} g f = cong (incl5 E ∘_) (map5-comp g f)

  pre-track5 : {C D E : CWskel ℓ} (f : cellMap C D)
    (u : realise D → realise E) (a : finCellApprox D E u 6)
    → real5 C E (composeFinCellMap 5 (finCellMap↓ (fst a))
        (Stage.restrictCell f 5))
      ≡ u ∘ realiseCellMap {C = C} {D = D} f ∘ incl5 C
  pre-track5 {C = C} {D = D} f u a = funExt λ z →
    funExt⁻ (real5-comp (finCellMap↓ (fst a)) (Stage.restrictCell f 5)) z
    ∙∙ funExt⁻ (track↓ {u = u} a) (map5 C D (Stage.restrictCell f 5) z)
    ∙∙ cong u (funExt⁻ (restrict-real5 f) z)

  post-track5 : {C D E : CWskel ℓ} (f : cellMap D E)
    (u : realise C → realise D) (a : finCellApprox C D u 6)
    → real5 C E (composeFinCellMap 5 (Stage.restrictCell f 5)
        (finCellMap↓ (fst a)))
      ≡ realiseCellMap {C = D} {D = E} f ∘ u ∘ incl5 C
  post-track5 {C = C} {D = D} {E = E} f u a = funExt λ z →
    funExt⁻ (real5-comp (Stage.restrictCell f 5) (finCellMap↓ (fst a))) z
    ∙∙ funExt⁻ (restrict-real5 f) (map5 C D (finCellMap↓ (fst a)) z)
    ∙∙ cong (realiseCellMap {C = D} {D = E} f) (funExt⁻ (track↓ {u = u} a) z)

  -- These computations use the original approximation tracks at every
  -- inclusion. Explicit endpoints keep the unit computations independent
  -- of any particular CW skeleton or chosen track.
  pre-track5-β : {C D E : CWskel ℓ} (f : cellMap C D)
    (u : realise D → realise E) (a : finCellApprox D E u 6)
    (n : Fin 6) (x : fst C (fst n))
    → funExt⁻ (pre-track5 f u a) (fincl n x)
      ≡ funExt⁻ (snd a)
          (fincl (injectSuc n) (SequenceMap.map f (fst n) x))
  pre-track5-β f u a n x = sym (rUnit
    (funExt⁻ (snd a) (fincl (injectSuc n) (SequenceMap.map f (fst n) x))))

  post-track5-β : {C D E : CWskel ℓ} (f : cellMap D E)
    (u : realise C → realise D) (a : finCellApprox C D u 6)
    (n : Fin 6) (x : fst C (fst n))
    → funExt⁻ (post-track5 f u a) (fincl n x)
      ≡ cong (realiseCellMap {C = D} {D = E} f)
          (funExt⁻ (snd a) (fincl (injectSuc n) x))
  post-track5-β {D = D} {E = E} f u a n x = sym (lUnit
    (cong (realiseCellMap {C = D} {D = E} f)
      (funExt⁻ (snd a) (fincl (injectSuc n) x))))

module Window (ℓ : Level) (Os Ls Rs Ot Lt Rt : CWskel ℓ)
  (fs : cellMap (strictCWskel Os) (strictCWskel Ls))
  (gs : cellMap (strictCWskel Os) (strictCWskel Rs))
  (ft : cellMap (strictCWskel Ot) (strictCWskel Lt))
  (gt : cellMap (strictCWskel Ot) (strictCWskel Rt)) where

  module W = Stage.Window ℓ Os Ls Rs Ot Lt Rt fs gs ft gt
  open W using (Xs ; Bs ; Cs ; Xt ; Bt ; Ct ; module S ; module T)

  module _
    (u∞ : realise Xs → realise Xt)
    (v∞ : realise Bs → realise Bt)
    (w∞ : realise Cs → realise Ct)
    (hL∞ : (x : realise Xs)
      → v∞ (realiseCellMap {C = Xs} {D = Bs} S.f x)
      ≡ realiseCellMap {C = Xt} {D = Bt} T.f (u∞ x))
    (hR∞ : (x : realise Xs)
      → w∞ (realiseCellMap {C = Xs} {D = Cs} S.g x)
      ≡ realiseCellMap {C = Xt} {D = Ct} T.g (u∞ x)) where

    module _
      (aO : finCellApprox Xs Xt u∞ 6)
      (aL : finCellApprox Bs Bt v∞ 6)
      (aR : finCellApprox Cs Ct w∞ 6) where

      -- Function paths on the whole finite sequential colimit, not an
      -- arbitrary family of pointwise paths on its stages.
      H_L : real5 Xs Bt (W.F_L u∞ v∞ w∞ hL∞ hR∞ aL) ≡ real5 Xs Bt (W.G_L u∞ v∞ w∞ hL∞ hR∞ aO)
      H_L = funExt λ z →
        funExt⁻ (pre-track5 S.f v∞ aL) z
        ∙∙ hL∞ (incl5 Xs z)
        ∙∙ sym (funExt⁻ (post-track5 T.f u∞ aO) z)

      H_R : real5 Xs Ct (W.F_R u∞ v∞ w∞ hL∞ hR∞ aR) ≡ real5 Xs Ct (W.G_R u∞ v∞ w∞ hL∞ hR∞ aO)
      H_R = funExt λ z →
        funExt⁻ (pre-track5 S.g w∞ aR) z
        ∙∙ hR∞ (incl5 Xs z)
        ∙∙ sym (funExt⁻ (post-track5 T.g u∞ aO) z)

      markingL-exact : (λ n x → funExt⁻ H_L (fincl n x))
        ≡ W.markingL u∞ v∞ w∞ hL∞ hR∞ aO aL
      markingL-exact j n x =
        pre-track5-β S.f v∞ aL n x j
        ∙∙ hL∞ (incl x)
        ∙∙ sym (post-track5-β T.f u∞ aO n x j)

      markingR-exact : (λ n x → funExt⁻ H_R (fincl n x))
        ≡ W.markingR u∞ v∞ w∞ hL∞ hR∞ aO aR
      markingR-exact j n x =
        pre-track5-β S.g w∞ aR n x j
        ∙∙ hR∞ (incl x)
        ∙∙ sym (post-track5-β T.g u∞ aO n x j)

      marked-left-merely :
        ∥ finCellHomRel 5 (W.F_L u∞ v∞ w∞ hL∞ hR∞ aL) (W.G_L u∞ v∞ w∞ hL∞ hR∞ aO)
            (W.markingL u∞ v∞ w∞ hL∞ hR∞ aO aL) ∥₁
      marked-left-merely = PT.map
        (subst (finCellHomRel 5 (W.F_L u∞ v∞ w∞ hL∞ hR∞ aL) (W.G_L u∞ v∞ w∞ hL∞ hR∞ aO)) markingL-exact)
        (marked-finite-homotopy 5 (W.F_L u∞ v∞ w∞ hL∞ hR∞ aL) (W.G_L u∞ v∞ w∞ hL∞ hR∞ aO) H_L)

      marked-right-merely :
        ∥ finCellHomRel 5 (W.F_R u∞ v∞ w∞ hL∞ hR∞ aR) (W.G_R u∞ v∞ w∞ hL∞ hR∞ aO)
            (W.markingR u∞ v∞ w∞ hL∞ hR∞ aO aR) ∥₁
      marked-right-merely = PT.map
        (subst (finCellHomRel 5 (W.F_R u∞ v∞ w∞ hL∞ hR∞ aR) (W.G_R u∞ v∞ w∞ hL∞ hR∞ aO)) markingR-exact)
        (marked-finite-homotopy 5 (W.F_R u∞ v∞ w∞ hL∞ hR∞ aR) (W.G_R u∞ v∞ w∞ hL∞ hR∞ aO) H_R)

    -- Three approximation witnesses and two marked homotopies are
    -- eliminated jointly into a proposition. No infinite choice is used.
    finite-span6-merely : ∥ W.FiniteSpan6 u∞ v∞ w∞ hL∞ hR∞ ∥₁
    finite-span6-merely =
      PT.rec squash₁ (λ aO →
      PT.rec squash₁ (λ aL →
      PT.rec squash₁ (λ aR →
      PT.rec squash₁ (λ hL →
      PT.map (λ hR → record
        { aO = aO ; aL = aL ; aR = aR ; H_L = hL ; H_R = hR })
        (marked-right-merely aO aL aR))
        (marked-left-merely aO aL aR))
        (CWmap→finCellMap Cs Ct w∞ 6))
        (CWmap→finCellMap Bs Bt v∞ 6))
        (CWmap→finCellMap Xs Xt u∞ 6)
