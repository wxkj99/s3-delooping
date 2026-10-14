{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.TargetLiteral where

-- The actual Definition.M 2 3 n endpoint, not a presentation complex.
-- The pointing and both inverse laws are retained by πIso.  These
-- exports make the passage between the literal and rose/Kind models
-- explicit; the tree-path generation argument is performed in the
-- latter only to avoid duplicating the wedge-to-rose constructor proof.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (pos)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
  using (GroupEquiv→GroupHom; invGroupEquiv)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·)
open import Cubical.Homotopy.Group.Base using (πGr; πIso)
open import Cubical.HITs.Pushout.Base using (inl)
import Cubical.HITs.PropositionalTruncation as PT
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Original
import DeloopS3.Cert.Interpret.Realization as R
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Input.Model as Model
open import DeloopS3.Bridge.SpanPi1.TargetLoops
open import DeloopS3.Bridge.SpanPi1.TargetWords
open import DeloopS3.Bridge.SpanPi1.TargetNormal
import DeloopS3.Bridge.SpanPi1.WordAlgebra as WA

literalBase : (c : ShortCase) → Model.M-original c
literalBase c = inl (Original.p₀ , R.0C)

abstract
  literal-point : (c : ShortCase)
    → equivFun (Model.originalTotalEquiv c) (literalBase c) ≡ m₀ c
  literal-point c = Model.originalTotalEquiv-left c Original.p₀ R.0C

literalG : ShortCase → Group₀
literalG c = πGr 0 (Model.M-original c , literalBase c)

literal-to-modelπ : (c : ShortCase) → GroupEquiv (literalG c) (G c)
literal-to-modelπ c = πIso
  (Model.originalTotalEquiv c , literal-point c) 0

model-to-literalπ : (c : ShortCase) → GroupHom (G c) (literalG c)
model-to-literalπ c = GroupEquiv→GroupHom (invGroupEquiv (literal-to-modelπ c))

literal-x literal-y literal-z literal-h : (c : ShortCase) → fst (literalG c)
literal-x c = fst (model-to-literalπ c) (x c)
literal-y c = fst (model-to-literalπ c) (y c)
literal-z c = fst (model-to-literalπ c) (z c)
literal-h c = fst (model-to-literalπ c) (h c)

record LiteralTargetGenerated (c : ShortCase) : Type₀ where
  field
    generated : (u : fst (literalG c))
      → Membership.Generated (literalG c) (literal-x c) (literal-y c) u
    square-fibre : WA.Words.square (literalG c) (literal-x c) ≡ literal-h c
    cube-fibre : WA.Words.cube (literalG c) (literal-y c) ≡ literal-h c
    third-word : literal-z c ≡ WA.Words.z (literalG c) (literal-x c) (literal-y c)
    third-power : (pos (Model.localOrder c Ch.C) ℤ[ literalG c ]· literal-z c) ≡ literal-h c

abstract
  literal-target-generated : (c : ShortCase) → LiteralTargetGenerated c
  LiteralTargetGenerated.generated (literal-target-generated c) u = PT.map
    (λ { (v , p) → v ,
      sym (map-eval (G c) (literalG c) (x c) (y c) (model-to-literalπ c) v)
      ∙ cong (fst (model-to-literalπ c)) p ∙ retEq (fst (literal-to-modelπ c)) u })
    (TargetGenerated.generated (target-generated c) (fst (fst (literal-to-modelπ c)) u))
  LiteralTargetGenerated.square-fibre (literal-target-generated c) =
    sym (HomWords.map-square (G c) (literalG c) (model-to-literalπ c) (x c))
    ∙ cong (fst (model-to-literalπ c)) (TargetGenerated.square-fibre (target-generated c))
  LiteralTargetGenerated.cube-fibre (literal-target-generated c) =
    sym (HomWords.map-cube (G c) (literalG c) (model-to-literalπ c) (y c))
    ∙ cong (fst (model-to-literalπ c)) (TargetGenerated.cube-fibre (target-generated c))
  LiteralTargetGenerated.third-word (literal-target-generated c) =
    cong (fst (model-to-literalπ c)) (TargetGenerated.third-word (target-generated c))
    ∙ HomWords.map-z (G c) (literalG c) (model-to-literalπ c) (x c) (y c)
  LiteralTargetGenerated.third-power (literal-target-generated c) =
    sym (homPresℤ· (model-to-literalπ c) (z c) (pos (Model.localOrder c Ch.C)))
    ∙ cong (fst (model-to-literalπ c)) (TargetGenerated.third-power (target-generated c))
