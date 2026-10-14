{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsFinal where

-- Unconditional actual boundary columns. The circle-model reflection sign
-- is supplied by the actual torus homology theorem.
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsProof.Statements public
  using (ColumnEquations ; RawBoundaryColumnsStatement)
  renaming (BoundaryColumnsStatement to SealedBoundaryColumnsStatement)
import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumns as Base
import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryColumnsFromTorus as Torus
open import DeloopS3.Bridge.DegreeSpan.TorusReflectionH2 using
  (torus-reflection-H₂-neg)

abstract
  reflection-H₂ : Torus.TorusReflectionH₂
  reflection-H₂ = torus-reflection-H₂-neg

  boundary-columns : RawBoundaryColumnsStatement
  boundary-columns = Torus.boundary-columns reflection-H₂

  boundary-columns-sealed : SealedBoundaryColumnsStatement
  boundary-columns-sealed = Torus.boundary-columns-sealed reflection-H₂

  base-seifert-boundary-columns : Base.BoundaryColumns
  base-seifert-boundary-columns = Torus.base-seifert-boundary-columns reflection-H₂
