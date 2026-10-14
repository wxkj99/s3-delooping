{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Interpret.Done where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Foundations.Univalence using (ua; ua→; ua-gluePath; pathToEquiv)
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc)
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Sum using (_⊎_) renaming (inl to inj₁; inr to inj₂)
import Cubical.Data.Int as Z
open import Cubical.HITs.Pushout.Base using (Pushout; inl; inr; push)
open import Cubical.HITs.EilenbergMacLane1.Base using (EM₁)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (rUnitₖ)
open import Cubical.Functions.Fibration using (fiberEquiv)
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Interpret.Short as Short
open import DeloopS3.Cert.Interpret.Short public using
  (ShortCase; octa; icosa; exponentOf; DescendedAdapter; SmallSpanCompletion)
open import DeloopS3.Cert.Interpret.Syntax using (twoGenerators)
open import DeloopS3.Cert.Interpret.Terminal using (mul-zero)
import DeloopS3.Cert.Input.Model as Model
import DeloopS3.Cert.Input.Orbits as Orbits
import DeloopS3.Cert.Input.Initial.Assembly as Initial
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
import DeloopS3.Seifert.MarkedSeifert.Final as Final
import DeloopS3.Seifert.MarkedSeifert.FinalDone as FinalDone
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
open import DeloopS3.Seifert.TwistedBundle.Base using (λA)
import DeloopS3.Seifert.TwistedBundle.SmallChart as SmallChart
open import DeloopS3.Cover.Cosets using (CosetFamily)
import DeloopS3.Sphere.TruncationCartesian as Cartesian

-- Both endpoint comparisons retain the whole pushout span.  In particular,
-- the rose, Kind, finite-position and literal wedge models are not silently
-- identified by a presentation of their fundamental groups.
private
  state : ℕ → ℕ → Ch.State
  state q e = Ch.state twoGenerators
    (Ch.face 0 2 (P.pos 1) (P.fwd 1 ∷ []) (P.pos 0) ∷
     Ch.face 1 q (P.pos 1) (P.fwd 2 ∷ []) (P.pos 0) ∷
     Ch.face 2 e (P.pos 1 P.-z P.pos e)
       (P.bwd 2 ∷ P.bwd 1 ∷ []) (P.pos 0) ∷ [])

  kind : Fin 3 → Ch.Kind
  kind fzero = Ch.A
  kind (fsuc fzero) = Ch.B
  kind (fsuc (fsuc fzero)) = Ch.C
  kind (fsuc (fsuc (fsuc ())))

  position : Ch.Kind → Fin 3
  position Ch.A = fzero
  position Ch.B = fsuc fzero
  position Ch.C = fsuc (fsuc fzero)

  kind-position : (k : Ch.Kind) → kind (position k) ≡ k
  kind-position Ch.A = refl
  kind-position Ch.B = refl
  kind-position Ch.C = refl

  position-kind : (i : Fin 3) → position (kind i) ≡ i
  position-kind fzero = refl
  position-kind (fsuc fzero) = refl
  position-kind (fsuc (fsuc fzero)) = refl
  position-kind (fsuc (fsuc (fsuc ())))

  indexEquiv : Fin 3 ≃ Ch.Kind
  indexEquiv = isoToEquiv (iso kind position kind-position position-kind)

  order : ℕ → ℕ → Ch.Kind → ℕ
  order q e Ch.A = 2
  order q e Ch.B = q
  order q e Ch.C = e

  weight : ℕ → Ch.Kind → Z.ℤ
  weight e Ch.A = Z.pos 1
  weight e Ch.B = Z.pos 1
  weight e Ch.C = Z.pos 1 Z.- Z.pos e

  KindSpan : ℕ → ℕ → R.Span ℓ-zero ℓ-zero ℓ-zero
  R.Span.O (KindSpan q e) = Ch.Kind × R.T²
  R.Span.L (KindSpan q e) = Model.Γ × R.C
  R.Span.R (KindSpan q e) = Ch.Kind × R.C
  R.Span.left (KindSpan q e) (k , u , t) =
    R.wordCircle twoGenerators (Ch.kindWord k) u , t
  R.Span.right (KindSpan q e) (k , z) =
    k , Model.row (weight e k) (order q e k) z

  abstract
    zero-winding : (u t : R.C) → t R.+C R.mulC (Z.pos 0) u ≡ t
    zero-winding u t = cong (t R.+C_) (mul-zero u)
      ∙ rUnitₖ {G = ℤAbGroup} 1 t

  positionsToKinds : (q e : ℕ)
    → R.SpanEquiv (R.diagram (state q e)) (KindSpan q e)
  R.SpanEquiv.overlapEquiv (positionsToKinds q e) =
    ≃-× indexEquiv (idEquiv R.T²)
  R.SpanEquiv.leftVertex (positionsToKinds q e) = idEquiv (Model.Γ × R.C)
  R.SpanEquiv.rightVertex (positionsToKinds q e) =
    ≃-× indexEquiv (idEquiv R.C)
  R.SpanEquiv.leftSquare (positionsToKinds q e) (fzero , u , t) =
    ΣPathP (refl , zero-winding u t)
  R.SpanEquiv.leftSquare (positionsToKinds q e) (fsuc fzero , u , t) =
    ΣPathP (refl , zero-winding u t)
  R.SpanEquiv.leftSquare (positionsToKinds q e) (fsuc (fsuc fzero) , u , t) =
    ΣPathP (refl , zero-winding u t)
  R.SpanEquiv.leftSquare (positionsToKinds q e) (fsuc (fsuc (fsuc ())) , z)
  R.SpanEquiv.rightSquare (positionsToKinds q e) (fzero , z) = refl
  R.SpanEquiv.rightSquare (positionsToKinds q e) (fsuc fzero , z) = refl
  R.SpanEquiv.rightSquare (positionsToKinds q e) (fsuc (fsuc fzero) , u , t) =
    cong (λ s → Ch.C , Model.row s e (u , t))
      (R.int-subtract (P.pos 1) (P.pos e))
  R.SpanEquiv.rightSquare (positionsToKinds q e) (fsuc (fsuc (fsuc ())) , z)

  LiteralSpan : ℕ → R.Span ℓ-zero ℓ-zero ℓ-zero
  R.Span.O (LiteralSpan e) = (R.T² ⊎ R.T²) ⊎ R.T²
  R.Span.L (LiteralSpan e) = Literal.Core
  R.Span.R (LiteralSpan e) = (R.C ⊎ R.C) ⊎ R.C
  R.Span.left (LiteralSpan e) = Literal.Seifert.allLeft (Z.pos 2) (Z.pos 2) (Z.pos e)
  R.Span.right (LiteralSpan e) = Literal.Seifert.allRight (Z.pos 2) (Z.pos 2) (Z.pos e)

  literalToKinds : (e : ℕ) → R.SpanEquiv (LiteralSpan e) (KindSpan 2 e)
  R.SpanEquiv.overlapEquiv (literalToKinds e) = Model.tripleIndex R.T²
  R.SpanEquiv.leftVertex (literalToKinds e) =
    ≃-× Model.originalGraphEquiv (idEquiv R.C)
  R.SpanEquiv.rightVertex (literalToKinds e) = Model.tripleIndex R.C
  R.SpanEquiv.leftSquare (literalToKinds e) (inj₁ (inj₁ (u , t))) =
    cong (λ x → x , t) (Model.original-boundary-square Ch.A u)
  R.SpanEquiv.leftSquare (literalToKinds e) (inj₁ (inj₂ (u , t))) =
    cong (λ x → x , t) (Model.original-boundary-square Ch.B u)
  R.SpanEquiv.leftSquare (literalToKinds e) (inj₂ (u , t)) =
    cong (λ x → x , t) (Model.original-boundary-square Ch.C u)
  R.SpanEquiv.rightSquare (literalToKinds e) (inj₁ (inj₁ z)) = refl
  R.SpanEquiv.rightSquare (literalToKinds e) (inj₁ (inj₂ z)) = refl
  R.SpanEquiv.rightSquare (literalToKinds e) (inj₂ z) = refl

abstract
  standard-to-marked : (e : ℕ) → Short.M22e e ≃ Final.M22e (Z.pos e)
  standard-to-marked e = compEquiv
    {A = Short.M22e e} {B = R.Total (KindSpan 2 e)}
    {C = Final.M22e (Z.pos e)}
    (R.spanEquiv (positionsToKinds 2 e))
    (invEquiv (R.spanEquiv (literalToKinds e)))

  small-squares : (e : Z.ℤ) → SmallSpanCompletion e
  SmallSpanCompletion.left-square (small-squares e) =
    Short.SmallSpanMaps.left-source-β e ∙ Final.SmallSpan.left-square e
      ∙ sym (Short.SmallSpanMaps.left-target-β e)
  SmallSpanCompletion.right-square (small-squares e) =
    Short.SmallSpanMaps.right-source-β e ∙ Final.SmallSpan.right-square e
      ∙ sym (Short.SmallSpanMaps.right-target-β e)

  seifert-to-small : (e : ℕ)
    → Short.M22e e ≃ Pushout λA (SmallChart.Filling.rowShift (Z.pos e))
  seifert-to-small e = compEquiv
    {A = Short.M22e e} {B = Final.M22e (Z.pos e)}
    {C = Final.SmallSpan.SmallFill (Z.pos e)}
    (standard-to-marked e)
    (compEquiv {A = Final.M22e (Z.pos e)} {B = Bundle.Mₑ (Z.pos e)}
      {C = Final.SmallSpan.SmallFill (Z.pos e)}
      (FinalDone.M22e≃Mₑ (Z.pos e)) (Final.SmallSpan.flattenSmall (Z.pos e)))

descended : (c : ShortCase) → DescendedAdapter (exponentOf c)
DescendedAdapter.seifert-to-small (descended c) = seifert-to-small (exponentOf c)
DescendedAdapter.small-squares (descended c) = small-squares (Z.pos (exponentOf c))

-- Model.M_G is Kind-indexed; Short.M_G is finite-position-indexed.
-- Transport the classifier AND its dependent charts along one span path.
-- This avoids assuming that either model is definitionally the other,
-- and avoids inventing a new cover unrelated to Model.ρ-M.
private
  abstract
    span-path : {D E : R.Span ℓ-zero ℓ-zero ℓ-zero}
      → R.SpanEquiv D E → D ≡ E
    R.Span.O (span-path e i) = ua (R.SpanEquiv.overlapEquiv e) i
    R.Span.L (span-path e i) = ua (R.SpanEquiv.leftVertex e) i
    R.Span.R (span-path e i) = ua (R.SpanEquiv.rightVertex e) i
    R.Span.left (span-path {D} {E} e i) =
      ua→ {e = R.SpanEquiv.overlapEquiv e}
        {B = λ j → ua (R.SpanEquiv.leftVertex e) j}
        {f₀ = R.Span.left D} {f₁ = R.Span.left E}
        (λ z → ua-gluePath (R.SpanEquiv.leftVertex e)
          (R.SpanEquiv.leftSquare e z)) i
    R.Span.right (span-path {D} {E} e i) =
      ua→ {e = R.SpanEquiv.overlapEquiv e}
        {B = λ j → ua (R.SpanEquiv.rightVertex e) j}
        {f₀ = R.Span.right D} {f₁ = R.Span.right E}
        (λ z → ua-gluePath (R.SpanEquiv.rightVertex e)
          (R.SpanEquiv.rightSquare e z)) i

    kind-model-right : (c : ShortCase) (z : Ch.Kind × R.T²)
      → R.Span.right (KindSpan 3 (Short.originalExponent c)) z
        ≡ R.Span.right (Model.BaseSpan c) z
    kind-model-right octa (Ch.A , z) = refl
    kind-model-right octa (Ch.B , z) = refl
    kind-model-right octa (Ch.C , z) = refl
    kind-model-right icosa (Ch.A , z) = refl
    kind-model-right icosa (Ch.B , z) = refl
    kind-model-right icosa (Ch.C , z) = refl

    kind-model-path : (c : ShortCase)
      → KindSpan 3 (Short.originalExponent c) ≡ Model.BaseSpan c
    R.Span.O (kind-model-path c i) = Ch.Kind × R.T²
    R.Span.L (kind-model-path c i) = Model.Γ × R.C
    R.Span.R (kind-model-path c i) = Ch.Kind × R.C
    R.Span.left (kind-model-path c i) = R.Span.left (Model.BaseSpan c)
    R.Span.right (kind-model-path c i) z = kind-model-right c z i

    base-span-path : (c : ShortCase)
      → R.diagram (Short.originalState c) ≡ Model.BaseSpan c
    base-span-path c = span-path (positionsToKinds 3 (Short.originalExponent c))
      ∙ kind-model-path c

  liftedSpan : (D : R.Span ℓ-zero ℓ-zero ℓ-zero)
    → (R.Total D → Type₀) → R.Span ℓ-zero ℓ-zero ℓ-zero
  R.Span.O (liftedSpan D Q) = Σ (R.Span.O D) (λ z → Q (inl (R.Span.left D z)))
  R.Span.L (liftedSpan D Q) = Σ (R.Span.L D) (Q ∘ inl)
  R.Span.R (liftedSpan D Q) = Σ (R.Span.R D) (Q ∘ inr)
  R.Span.left (liftedSpan D Q) (z , q) = R.Span.left D z , q
  R.Span.right (liftedSpan D Q) (z , q) = R.Span.right D z , subst Q (push z) q

  InputPackage : ShortCase → R.Span ℓ-zero ℓ-zero ℓ-zero → Type₁
  InputPackage c D = Σ[ ρ ∈ (R.Total D → EM₁ (Short.Δ c)) ]
    Short.InitialSpanCharts (Ch.initialState (Short.certOf c))
      (liftedSpan D (λ m → CosetFamily (Short.j c) (ρ m) .fst))

  abstract
    assembly-input : (c : ShortCase)
      → InputPackage c (R.diagram (Short.originalState c))
    assembly-input c = subst (InputPackage c) (sym (base-span-path c))
      (Model.ρ-M c , Initial.initial-charts c)

    assembly-input-path : (c : ShortCase)
      → PathP (λ i → InputPackage c (base-span-path c (~ i)))
        (Model.ρ-M c , Initial.initial-charts c) (assembly-input c)
    assembly-input-path c = subst-filler (InputPackage c) (sym (base-span-path c))
      (Model.ρ-M c , Initial.initial-charts c)

  assembly-ρ : (c : ShortCase) → Short.M_G c → EM₁ (Short.Δ c)
  assembly-ρ c = assembly-input c .fst

  assembly-charts : (c : ShortCase) → Short.InitialCharts c (assembly-ρ c)
  assembly-charts c = assembly-input c .snd

  module Assembled = Short.Assembly assembly-ρ Orbits.short-input assembly-charts descended

-- The public endpoints are the checked input module's actual Kind model,
-- not Short.M_G, nor the literal wedge pushout M-original. The latter is
-- separately compared with this M_G by Model.originalTotalEquiv.
open import DeloopS3.Cert.Input.Model public using (M_G; A_G; Q; ρ-M)

private
  abstract
    cover-total-path : (c : ShortCase)
      → Short.A_G c (assembly-ρ c) ≡ A_G c
    cover-total-path c i = Σ (R.Total (base-span-path c i))
      (λ m → CosetFamily (Short.j c) (assembly-input-path c (~ i) .fst m) .fst)

abstract
  short-total : (c : ShortCase) → Bundle.Mₑ (Z.pos (exponentOf c)) ≃ A_G c
  short-total c = compEquiv
    {A = Bundle.Mₑ (Z.pos (exponentOf c))}
    {B = Short.A_G c (assembly-ρ c)} {C = A_G c}
    (Assembled.short-total c) (pathToEquiv (cover-total-path c))

p : (c : ShortCase) → Bundle.Mₑ (Z.pos (exponentOf c)) → M_G c
p c = fst ∘ equivFun (short-total c)

abstract
  p-fibres : (c : ShortCase) (m : M_G c) → fiber (p c) m ≃ Q c m
  p-fibres c m = compEquiv
    {A = fiber (p c) m} {B = fiber (fst {B = Q c}) m} {C = Q c m}
    (Σ-cong-equiv-fst {B = λ t → fst t ≡ m} (short-total c))
    (fiberEquiv (Q c) m)

  p-is-cover : (c : ShortCase) (m : M_G c) → isSet (fiber (p c) m)
  p-is-cover c m = isOfHLevelRespectEquiv 2 (invEquiv (p-fibres c m))
    (CosetFamily (Short.j c) (ρ-M c m) .snd)

  B-cartesian : (c : ShortCase)
    → Cartesian.CartSquare (p c) (Cartesian.τ₁-map (p c))
      Cartesian.η₁ Cartesian.η₁ (Cartesian.trunc₁-naturality (p c))
  B-cartesian c = Cartesian.trunc₁-cover-cartesian (p c) (p-is-cover c)

  B-unit-fibers : (c : ShortCase)
    (z : Cartesian.τ₁ (Bundle.Mₑ (Z.pos (exponentOf c))))
    → fiber (Cartesian.η₁ {A = Bundle.Mₑ (Z.pos (exponentOf c))}) z
      ≃ fiber (Cartesian.η₁ {A = M_G c}) (Cartesian.τ₁-map (p c) z)
  B-unit-fibers c = Cartesian.trunc₁-cover-unit-fibers (p c) (p-is-cover c)

-- Item (B), downstream form: for G = O (c = octa, e = 4) and
-- G = I (c = icosa, e = 3), p : M_e → M_G is a covering. Its fibres
-- are the coset sets Q (respectively 3 and 10 sheets), by p-fibres;
-- the naturality square for 1-truncation is cartesian, by B-cartesian.
-- B-unit-fibers is the resulting equivalence of the truncation-unit fibres.
