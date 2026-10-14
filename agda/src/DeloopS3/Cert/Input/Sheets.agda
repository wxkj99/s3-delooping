{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Sheets where

-- Actual right-coset sheets, in the
-- certificate representative order, with all four signed actions.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin using (isSetFin)
open import Cubical.Algebra.Group.Base using (GroupStr)
open import Cubical.HITs.EilenbergMacLane1.Base using (embase; emloop)
open import DeloopS3.Cover.Cosets
open import DeloopS3.Cert.Input.Model.Vocabulary
open import DeloopS3.Cert.Input.Sheets.NormalForm public using
  (pack; normalForm; normalForm-pack)
open import DeloopS3.Cert.Input.Sheets.Action public using (action-witness)
open import DeloopS3.Cert.Input.Sheets.Quotient using (module FromNormalForm)

record SheetData (c : ShortCase) : Type₀ where
  field
    e : Sh c ≃ CosetFamily (j c) embase .fst
    at-rep : (i : Sh c)
      → equivFun e i ≡ cosetPoint (j c) (repElement c i)
    square : (i : Sh c) (t : BaseLetter)
      → subst (λ b → CosetFamily (j c) b .fst)
          (emloop (letterElement c t)) (equivFun e i)
      ≡ equivFun e (actFin (certOf c) (rawChecks c) t i)

private
  module Sheets (c : ShortCase) = FromNormalForm (H c) (Δ c) (j c)
    (Sh c) isSetFin (repElement c) (normalForm c) (normalForm-pack c)

abstract
  -- Positive base-loop transport is right multiplication, also for
  -- the group elements interpreting the two negative letters.
  representative-square : (c : ShortCase) (i : Sh c) (t : BaseLetter)
    → subst (λ b → CosetFamily (j c) b .fst) (emloop (letterElement c t))
        (cosetPoint (j c) (repElement c i))
      ≡ cosetPoint (j c) (repElement c (actFin (certOf c) (rawChecks c) t i))
  representative-square c i t = cosetPoint-action (j c) (repElement c i) (letterElement c t)
    ∙ RightCosets.point-respects (j c)
      (GroupStr._·_ (Δ c .snd) (repElement c i) (letterElement c t))
      (repElement c (actFin (certOf c) (rawChecks c) t i)) (action-witness c i t)

sheet-data : (c : ShortCase) → SheetData c
SheetData.e (sheet-data c) = Sheets.sheets≃fiber c
SheetData.at-rep (sheet-data c) = Sheets.sheets-at-rep c
SheetData.square (sheet-data c) = representative-square c
