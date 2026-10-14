{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Raw where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing.Instances.Int
import DeloopS3.Bridge.Profile.H1Data.RawPolynomial as RP
private module Poly = RP.Polynomial ℤCommRing
open import DeloopS3.Bridge.SeifertChains.Matrices
open import DeloopS3.Bridge.Profile.H1Data.Cokernel
open import DeloopS3.Bridge.Profile.H1Data.Linear

B : (q n : ℤ) → AbGroupHom ℤ² ℤ²
B q n = matrix (pos 2) (pos 2 Z.- n) (Z.- q) n

projection : AbGroupHom vertex₁ ℤ²
fst projection ((a , b) , h , x , y , z) =
  a Z.+ pos 2 Z.· h Z.+ x Z.+ z , b Z.+ y Z.- z
snd projection = makeIsGroupHom Poly.project-add

inclusion : AbGroupHom ℤ² vertex₁
fst inclusion (x , y) = (pos 0 , pos 0) , pos 0 , x , y , pos 0
snd inclusion = makeIsGroupHom λ _ _ → refl

columns : AbGroupHom ℤ⁶ ℤ²
fst columns ((u₁ , u₂ , u₃) , (h₁ , h₂ , h₃)) = h₂ , h₃ Z.- u₃
snd columns = makeIsGroupHom Poly.column-add

lift-columns : (n : ℤ) → AbGroupHom ℤ² ℤ⁶
fst (lift-columns n) (s , t) =
  ((Z.- (n Z.· t)) , (Z.- (n Z.· t)) , (Z.- (n Z.· t))) ,
  ((Z.- s) Z.+ (n Z.- pos 1) Z.· t) , s , ((pos 1 Z.- n) Z.· t)
snd (lift-columns n) = makeIsGroupHom (Poly.lift-add n)

correction-vector : fst vertex₁ → fst ℤ⁶
correction-vector ((a , b) , h , x , y , z) =
  (a Z.- z , b Z.- z , Z.- z) , (h Z.+ z) , pos 0 , Z.- z

abstract
  projection-square : (q n : ℤ) (u : fst ℤ⁶)
    → fst (B q n) (fst columns u) ≡ fst projection (fst (Araw (pos 2) q n) u)
  projection-square = Poly.project-square

  inclusion-square : (q n : ℤ) (v : fst ℤ²)
    → fst (Araw (pos 2) q n) (fst (lift-columns n) v) ≡ fst inclusion (fst (B q n) v)
  inclusion-square = Poly.include-square

  projection-inclusion : (v : fst ℤ²) → fst projection (fst inclusion v) ≡ v
  projection-inclusion = Poly.project-include

  raw-correction : (q n : ℤ) (v : fst vertex₁)
    → fst (Araw (pos 2) q n) (correction-vector v)
      ≡ AbGroupStr._+_ (snd vertex₁) v
        (AbGroupStr.-_ (snd vertex₁) (fst inclusion (fst projection v)))
  raw-correction = Poly.raw-correct

  -- Four unit cancellations. These are cokernels of the stated integer
  -- matrices, not an assertion identifying a space's cellular homology.
  Araw-cokernel-reduction : (q n : ℤ)
    → GroupIso (Coker (Araw (pos 2) q n)) (Coker (B q n))
  Araw-cokernel-reduction q n = coker-reduction
    (Araw (pos 2) q n) (B q n) projection inclusion columns (lift-columns n)
    (projection-square q n) (inclusion-square q n) projection-inclusion
    correction-vector (raw-correction q n)
