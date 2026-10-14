{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Model where

-- Concrete input vocabulary and the original Seifert pushout, not the bundle.
-- InitialCharts specializes Short.InitialSpanCharts at the Kind-indexed flat span.
-- originalTotalEquiv compares the rose/Kind model M_G with Definition.M 2 3 r;
-- ρ-original gives the classifier by explicit constructor clauses.
open import DeloopS3.Cert.Input.Model.Vocabulary public
open import DeloopS3.Cert.Input.Model.Groups public using
  (gen-order; gen-weight; gen-product; gen-c-inverses; genElement-table; genTable-valid)
open import DeloopS3.Cert.Input.Model.Torus using (module BasedTorus)
open import DeloopS3.Cert.Input.Model.Finite public using
  (act-a-inverse; act-b-inverse; firstSheet-value; repTable; repTable-valid; repElement-table; shortInput-orbit-start;
   repTable-member-icosa; repElement-decode-octa; repElement-decode-icosa)
open import DeloopS3.Cert.Input.Model.OriginalGraph public using
  (originalGraphEquiv; originalToRose; original-boundary-square; original-boundary-base; originalAttach; originalAttach-base)
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.SumFin using (fzero; fsuc)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group.Base using (GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; distrℤ·)
open import Cubical.HITs.EilenbergMacLane1.Base
open import Cubical.HITs.Pushout.Base using (inl; inr; push)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (cong₂+₁)
open import DeloopS3.Groups.Bmap using (Bmap)
open import DeloopS3.Cover.Cosets using (CosetFamily)
open import DeloopS3.Cover.MarkedDescent.Family using (module FamilyFlattening)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Cover.Orientation.CircleModel as Circle

row : Z.ℤ → ℕ → R.T² → R.C
row s n (u , t) = R.mulC s u R.+C R.mulC (Z.pos n) t

BaseSpan : ShortCase → R.Span ℓ-zero ℓ-zero ℓ-zero
R.Span.L (BaseSpan c) = Γ × R.C
R.Span.O (BaseSpan c) = Ch.Kind × R.T²
R.Span.R (BaseSpan c) = Ch.Kind × R.C
R.Span.left (BaseSpan c) (k , u , t) = R.wordCircle twoGenerators (Ch.kindWord k) u , t
R.Span.right (BaseSpan c) (k , z) = k , row (localWeight c k) (localOrder c k) z

M_G : ShortCase → Type₀
M_G c = R.Total (BaseSpan c)

graphMark : (c : ShortCase) → Γ → EM₁ (Δ c)
graphMark c R.root = embase
graphMark c (R.petal fzero i) = emloop (letterElement c a+) i
graphMark c (R.petal (fsuc fzero) i) = emloop (letterElement c b+) i
graphMark c (R.petal (fsuc (fsuc ())) i)

coreHom : (c : ShortCase) → Ch.Kind → GroupHom ℤGroup (Δ c)
coreHom c k = (λ z → z ℤ[ Δ c ]· genElement c k) , makeIsGroupHom (distrℤ· (Δ c) (genElement c k))
coreMark : (c : ShortCase) → Ch.Kind → R.C → EM₁ (Δ c)
coreMark c k = Bmap (coreHom c k)

graphMark-base : (c : ShortCase) → graphMark c R.root ≡ embase
graphMark-base c = refl
coreMark-base : (c : ShortCase) (k : Ch.Kind) → coreMark c k R.0C ≡ embase
coreMark-base c k = refl
row-base : (s : Z.ℤ) (n : ℕ) → row s n (R.0C , R.0C) ≡ R.0C
row-base s n = refl

boundaryMark : (c : ShortCase) → Ch.Kind → R.C → EM₁ (Δ c)
boundaryMark c k u = graphMark c (R.wordCircle twoGenerators (Ch.kindWord k) u)
boundaryMark-base : (c : ShortCase) (k : Ch.Kind) → boundaryMark c k R.0C ≡ embase
boundaryMark-base c k = refl

abstract
  coreMark-loop : (c : ShortCase) (k : Ch.Kind) (z : Z.ℤ)
    → cong (coreMark c k) (emloop z) ≡ emloop (z ℤ[ Δ c ]· genElement c k)
  coreMark-loop c k z = refl

  row-u-loop : (s : Z.ℤ) (n : ℕ)
    → cong (λ u → row s n (u , R.0C)) Circle.hC ≡ emloop s
  row-u-loop s n = cong₂+₁ {G = ℤAbGroup} (emloop (s Z.· Z.pos 1)) refl
    ∙ sym (rUnit (emloop (s Z.· Z.pos 1))) ∙ cong emloop (Z.·IdR s)

  row-t-loop : (s : Z.ℤ) (n : ℕ)
    → cong (λ t → row s n (R.0C , t)) Circle.hC ≡ emloop (Z.pos n)
  row-t-loop s n = cong emloop (Z.·IdR (Z.pos n))

  marked-word : (c : ShortCase) (k : Ch.Kind)
    → cong (graphMark c) (R.roseWord twoGenerators (Ch.kindWord k)) ≡ emloop (genElement c k)
  marked-word c Ch.A = R.eval-cong (graphMark c) (R.loopAt twoGenerators) (Ch.kindWord Ch.A)
    ∙ sym (rUnit (emloop (letterElement c a+)))
  marked-word c Ch.B = R.eval-cong (graphMark c) (R.loopAt twoGenerators) (Ch.kindWord Ch.B)
    ∙ sym (rUnit (emloop (letterElement c b+)))
  marked-word c Ch.C = R.eval-cong (graphMark c) (R.loopAt twoGenerators) (Ch.kindWord Ch.C)
    ∙ cong (sym (emloop (letterElement c b+)) ∙_) (sym (rUnit (sym (emloop (letterElement c a+)))))
    ∙ cong₂ _∙_ (sym (emloop-sym (Δ c) (letterElement c b+)))
        (sym (emloop-sym (Δ c) (letterElement c a+)))
    ∙ sym (emloop-comp (Δ c) (letterElement c b-) (letterElement c a-))
    ∙ cong emloop (sym (gen-c-inverses c))

  boundaryMark-loop : (c : ShortCase) (k : Ch.Kind)
    → cong (boundaryMark c k) Circle.hC ≡ emloop (genElement c k)
  boundaryMark-loop c k = cong (cong (graphMark c)) (R.wordCircle-loop twoGenerators (Ch.kindWord k))
    ∙ marked-word c k

  classifier-u-square : (c : ShortCase) (k : Ch.Kind)
    → cong (boundaryMark c k) Circle.hC
      ≡ cong (λ u → coreMark c k (row (localWeight c k) (localOrder c k) (u , R.0C))) Circle.hC
  classifier-u-square c k = boundaryMark-loop c k ∙ sym
    (cong (cong (coreMark c k)) (row-u-loop (localWeight c k) (localOrder c k))
     ∙ coreMark-loop c k (localWeight c k) ∙ cong emloop (gen-weight c k))

  classifier-t-square : (c : ShortCase) (k : Ch.Kind)
    → refl {x = embase {Group = Δ c}}
      ≡ cong (λ t → coreMark c k (row (localWeight c k) (localOrder c k) (R.0C , t))) Circle.hC
  classifier-t-square c k = sym
    (cong (cong (coreMark c k)) (row-t-loop (localWeight c k) (localOrder c k))
     ∙ coreMark-loop c k (Z.pos (localOrder c k))
     ∙ cong emloop (gen-order c k) ∙ emloop-1g (Δ c))

module ClassifierSeam (c : ShortCase) (k : Ch.Kind) = BasedTorus emsquash
  (λ z → boundaryMark c k (z .fst))
  (λ z → coreMark c k (row (localWeight c k) (localOrder c k) z)) refl
  (λ i j → classifier-u-square c k j i)
  (λ i j → classifier-t-square c k j i)

classifier-seam : (c : ShortCase) (k : Ch.Kind) (u t : R.C)
  → boundaryMark c k u ≡ coreMark c k (row (localWeight c k) (localOrder c k) (u , t))
classifier-seam c k u t = ClassifierSeam.seam c k (u , t)

abstract
  classifier-seam-base : (c : ShortCase) (k : Ch.Kind)
    → classifier-seam c k R.0C R.0C ≡ refl
  classifier-seam-base c k = ClassifierSeam.seam-base c k

ρ-M : (c : ShortCase) → M_G c → EM₁ (Δ c)
ρ-M c (inl (x , t)) = graphMark c x
ρ-M c (inr (k , u)) = coreMark c k u
ρ-M c (push (k , u , t) i) = classifier-seam c k u t i

classifier-left : (c : ShortCase) (x : Γ) (t : R.C)
  → ρ-M c (inl (x , t)) ≡ graphMark c x
classifier-left c x t = refl
classifier-right : (c : ShortCase) (k : Ch.Kind) (u : R.C)
  → ρ-M c (inr (k , u)) ≡ coreMark c k u
classifier-right c k u = refl

Q : (c : ShortCase) → M_G c → Type₀
Q c m = CosetFamily (j c) (ρ-M c m) .fst
A_G : ShortCase → Type₀
A_G c = Σ (M_G c) (Q c)

module Flat (c : ShortCase) = FamilyFlattening
  (R.Span.left (BaseSpan c)) (R.Span.right (BaseSpan c)) (Q c)

FlatSpan : ShortCase → R.Span ℓ-zero ℓ-zero ℓ-zero
R.Span.L (FlatSpan c) = Σ (R.Span.L (BaseSpan c)) (λ x → Q c (inl x))
R.Span.O (FlatSpan c) = Σ (R.Span.O (BaseSpan c)) (λ z → Q c (inl (R.Span.left (BaseSpan c) z)))
R.Span.R (FlatSpan c) = Σ (R.Span.R (BaseSpan c)) (λ y → Q c (inr y))
R.Span.left (FlatSpan c) (z , q) = R.Span.left (BaseSpan c) z , q
R.Span.right (FlatSpan c) (z , q) = R.Span.right (BaseSpan c) z , subst (Q c) (push z) q

InitialCharts : ShortCase → Type₁
InitialCharts c = Short.InitialSpanCharts (S₀ c) (FlatSpan c)
module InitialCharts = Short.InitialSpanCharts

-- BaseSpan presents Definition.M 2 3 r, not M22e or a descended bundle.
open import Cubical.Foundations.Isomorphism using (iso; isoToEquiv)
open import Cubical.Data.Sum using (_⊎_) renaming (inl to inj₁; inr to inj₂)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Original

tripleIndex : (X : Type₀) → ((X ⊎ X) ⊎ X) ≃ (Ch.Kind × X)
tripleIndex X = isoToEquiv (iso forward backward sec ret)
  where
  forward : (X ⊎ X) ⊎ X → Ch.Kind × X
  forward (inj₁ (inj₁ x)) = Ch.A , x
  forward (inj₁ (inj₂ x)) = Ch.B , x
  forward (inj₂ x) = Ch.C , x
  backward : Ch.Kind × X → (X ⊎ X) ⊎ X
  backward (Ch.A , x) = inj₁ (inj₁ x)
  backward (Ch.B , x) = inj₁ (inj₂ x)
  backward (Ch.C , x) = inj₂ x
  sec : (z : Ch.Kind × X) → forward (backward z) ≡ z
  sec (Ch.A , x) = refl
  sec (Ch.B , x) = refl
  sec (Ch.C , x) = refl
  ret : (z : (X ⊎ X) ⊎ X) → backward (forward z) ≡ z
  ret (inj₁ (inj₁ x)) = refl
  ret (inj₁ (inj₂ x)) = refl
  ret (inj₂ x) = refl

M-original : ShortCase → Type₀
M-original c = Original.M (Z.pos 2) (Z.pos 3) (Z.pos (localOrder c Ch.C))

OriginalSpan : ShortCase → R.Span ℓ-zero ℓ-zero ℓ-zero
R.Span.O (OriginalSpan c) = (R.T² ⊎ R.T²) ⊎ R.T²
R.Span.L (OriginalSpan c) = Original.Core
R.Span.R (OriginalSpan c) = (R.C ⊎ R.C) ⊎ R.C
R.Span.left (OriginalSpan c) = Original.Seifert.allLeft
  (Z.pos 2) (Z.pos 3) (Z.pos (localOrder c Ch.C))
R.Span.right (OriginalSpan c) = Original.Seifert.allRight
  (Z.pos 2) (Z.pos 3) (Z.pos (localOrder c Ch.C))

originalSpanEquiv : (c : ShortCase) → R.SpanEquiv (OriginalSpan c) (BaseSpan c)
R.SpanEquiv.overlapEquiv (originalSpanEquiv c) = tripleIndex R.T²
R.SpanEquiv.leftVertex (originalSpanEquiv c) = ≃-× originalGraphEquiv (idEquiv R.C)
R.SpanEquiv.rightVertex (originalSpanEquiv c) = tripleIndex R.C
R.SpanEquiv.leftSquare (originalSpanEquiv c) (inj₁ (inj₁ (u , t))) =
  cong (λ x → x , t) (original-boundary-square Ch.A u)
R.SpanEquiv.leftSquare (originalSpanEquiv c) (inj₁ (inj₂ (u , t))) =
  cong (λ x → x , t) (original-boundary-square Ch.B u)
R.SpanEquiv.leftSquare (originalSpanEquiv c) (inj₂ (u , t)) =
  cong (λ x → x , t) (original-boundary-square Ch.C u)
R.SpanEquiv.rightSquare (originalSpanEquiv c) (inj₁ (inj₁ z)) = refl
R.SpanEquiv.rightSquare (originalSpanEquiv c) (inj₁ (inj₂ z)) = refl
R.SpanEquiv.rightSquare (originalSpanEquiv octa) (inj₂ z) = refl
R.SpanEquiv.rightSquare (originalSpanEquiv icosa) (inj₂ z) = refl

abstract
  originalTotalEquiv : (c : ShortCase) → M-original c ≃ M_G c
  originalTotalEquiv c = R.SpanMap.spanEquiv (originalSpanEquiv c)

-- Also expose a classifier directly on the literal wedge pushout, with
-- constructor clauses (not merely a map hidden behind an equivalence).
originalGraphMark : (c : ShortCase) → Original.P → EM₁ (Δ c)
originalGraphMark c x = graphMark c (originalToRose x)

original-seam : (c : ShortCase) (k : Ch.Kind) (u t : R.C)
  → originalGraphMark c (originalAttach k u)
    ≡ coreMark c k (row (localWeight c k) (localOrder c k) (u , t))
original-seam c k u t = cong (graphMark c) (original-boundary-square k u)
  ∙ classifier-seam c k u t

abstract
  original-seam-base : (c : ShortCase) (k : Ch.Kind)
    → original-seam c k R.0C R.0C ≡ cong (graphMark c) (originalAttach-base k)
  original-seam-base c k = cong₂ _∙_
    (cong (cong (graphMark c)) (original-boundary-base k))
    (classifier-seam-base c k) ∙ sym (rUnit (cong (graphMark c) (originalAttach-base k)))

ρ-original : (c : ShortCase) → M-original c → EM₁ (Δ c)
ρ-original c (inl (x , t)) = originalGraphMark c x
ρ-original c (inr (inj₁ (inj₁ u))) = coreMark c Ch.A u
ρ-original c (inr (inj₁ (inj₂ u))) = coreMark c Ch.B u
ρ-original c (inr (inj₂ u)) = coreMark c Ch.C u
ρ-original c (push (inj₁ (inj₁ (u , t))) i) = original-seam c Ch.A u t i
ρ-original c (push (inj₁ (inj₂ (u , t))) i) = original-seam c Ch.B u t i
ρ-original octa (push (inj₂ (u , t)) i) = original-seam octa Ch.C u t i
ρ-original icosa (push (inj₂ (u , t)) i) = original-seam icosa Ch.C u t i

abstract
  original-seam-normalized : (c : ShortCase) (k : Ch.Kind)
    → sym (cong (graphMark c) (originalAttach-base k)) ∙ original-seam c k R.0C R.0C ≡ refl
  original-seam-normalized c k = cong (sym (cong (graphMark c) (originalAttach-base k)) ∙_)
    (original-seam-base c k) ∙ lCancel (cong (graphMark c) (originalAttach-base k))

open import DeloopS3.Move.CancelMinimalCore using (EquivOver)

abstract
  coreMark-positive : (c : ShortCase) (k : Ch.Kind)
    → cong (coreMark c k) Circle.hC ≡ emloop (genElement c k)
  coreMark-positive c k = coreMark-loop c k (Z.pos 1)
    ∙ cong emloop (GroupStr.·IdR (Δ c .snd) (genElement c k))

  classifier-push : (c : ShortCase) (k : Ch.Kind) (u t : R.C)
    → cong (ρ-M c) (push (k , u , t)) ≡ classifier-seam c k u t
  classifier-push c k u t = refl

  flatten-total : (c : ShortCase) → R.Total (FlatSpan c) ≃ A_G c
  flatten-total c = Flat.flatten c

  flatten-over : (c : ShortCase) → EquivOver (Flat.projection c) (fst {B = Q c})
  flatten-over c = Flat.over c

  originalTotalEquiv-left : (c : ShortCase) (x : Original.P) (t : R.C)
    → equivFun (originalTotalEquiv c) (inl (x , t)) ≡ inl (originalToRose x , t)
  originalTotalEquiv-left c x t = R.SpanMap.spanEquiv-inl (originalSpanEquiv c) (x , t)

  originalTotalEquiv-right : (c : ShortCase) (x : (R.C ⊎ R.C) ⊎ R.C)
    → equivFun (originalTotalEquiv c) (inr x) ≡ inr (equivFun (tripleIndex R.C) x)
  originalTotalEquiv-right c x = R.SpanMap.spanEquiv-inr (originalSpanEquiv c) x

-- The shared endpoint-chart record specialized to FlatSpan.
initialChartSpan : (c : ShortCase) → InitialCharts c
  → R.SpanEquiv (R.diagram (S₀ c)) (FlatSpan c)
initialChartSpan c charts = record
  { overlapEquiv = InitialCharts.overlapChart charts
  ; leftVertex = InitialCharts.leftChart charts
  ; rightVertex = InitialCharts.rightChart charts
  ; leftSquare = InitialCharts.leftSquare charts
  ; rightSquare = InitialCharts.rightSquare charts }
