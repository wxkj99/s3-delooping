{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Linear where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.CommRing
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver
open import DeloopS3.Bridge.SeifertChains.Matrices using (ℤ²)
open import DeloopS3.Bridge.Profile.H1Data.Cokernel

module Polynomial {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  abstract
    linear-add : (a b x y z w : fst R)
      → a · (x + z) + b · (y + w) ≡ (a · x + b · y) + (a · z + b · w)
    linear-add _ _ _ _ _ _ = solve! R
    inverse-one : (a b c d x y : fst R)
      → a · (d · x - b · y) + b · ((- c) · x + a · y) ≡ (a · d - b · c) · x
    inverse-one _ _ _ _ _ _ = solve! R
    inverse-two : (a b c d x y : fst R)
      → c · (d · x - b · y) + d · ((- c) · x + a · y) ≡ (a · d - b · c) · y
    inverse-two _ _ _ _ _ _ = solve! R
    inverse-three : (a b c d x y : fst R)
      → d · (a · x + b · y) - b · (c · x + d · y) ≡ (a · d - b · c) · x
    inverse-three _ _ _ _ _ _ = solve! R
    inverse-four : (a b c d x y : fst R)
      → (- c) · (a · x + b · y) + a · (c · x + d · y) ≡ (a · d - b · c) · y
    inverse-four _ _ _ _ _ _ = solve! R
    negative-factor : (a x : fst R) → (- a) · x ≡ - (a · x)
    negative-factor _ _ = solve! R

private module P = Polynomial ℤCommRing

matrix : (a b c d : ℤ) → AbGroupHom ℤ² ℤ²
fst (matrix a b c d) (x , y) = a Z.· x Z.+ b Z.· y , c Z.· x Z.+ d Z.· y
snd (matrix a b c d) = makeIsGroupHom λ (x , y) (z , w) →
  ΣPathP (P.linear-add a b x y z w , P.linear-add c d x y z w)

unimodular : (a b c d : ℤ) → a Z.· d Z.- b Z.· c ≡ pos 1
  → GroupIso (AbGroup→Group ℤ²) (AbGroup→Group ℤ²)
Iso.fun (fst (unimodular a b c d det)) = fst (matrix a b c d)
Iso.inv (fst (unimodular a b c d det)) = fst (matrix d (Z.- b) (Z.- c) a)
Iso.sec (fst (unimodular a b c d det)) (x , y) = ΣPathP
  (cong (λ t → a Z.· (d Z.· x Z.+ t) Z.+ b Z.· ((Z.- c) Z.· x Z.+ a Z.· y)) (P.negative-factor b y)
    ∙ P.inverse-one a b c d x y ∙ cong (Z._· x) det ∙ Z.·IdL x ,
   cong (λ t → c Z.· (d Z.· x Z.+ t) Z.+ d Z.· ((Z.- c) Z.· x Z.+ a Z.· y)) (P.negative-factor b y)
    ∙ P.inverse-two a b c d x y ∙ cong (Z._· y) det ∙ Z.·IdL y)
Iso.ret (fst (unimodular a b c d det)) (x , y) = ΣPathP
  (cong (d Z.· (a Z.· x Z.+ b Z.· y) Z.+_) (P.negative-factor b (c Z.· x Z.+ d Z.· y))
    ∙ P.inverse-three a b c d x y ∙ cong (Z._· x) det ∙ Z.·IdL x ,
   P.inverse-four a b c d x y ∙ cong (Z._· y) det ∙ Z.·IdL y)
snd (unimodular a b c d det) = snd (matrix a b c d)

abstract
  coker-unimodular : (f g : AbGroupHom ℤ² ℤ²)
    (u v : GroupIso (AbGroup→Group ℤ²) (AbGroup→Group ℤ²))
    → ((x : fst ℤ²) → Iso.fun (fst u) (fst f (Iso.fun (fst v) x)) ≡ fst g x)
    → GroupIso (Coker f) (Coker g)
  coker-unimodular f g u v square = invGroupIso
    (Hom/ImIso g f v (invGroupIso u) (λ x →
      sym (Iso.ret (fst u) (fst f (Iso.fun (fst v) x)))
      ∙ cong (Iso.inv (fst u)) (square x)))
