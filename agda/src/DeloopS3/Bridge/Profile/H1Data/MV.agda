{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.MV where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.Group.IsomorphismTheorems
open import Cubical.Algebra.AbGroup
open import Cubical.CW.Homology.Base using (H̃ᶜʷAb)
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.DMCExactness.Groups using (exact-composite)
open import DeloopS3.Bridge.SeifertChains.Matrices
open import DeloopS3.Bridge.Profile.H1Data.Cokernel

abstract
  exact-cokernel : {A B : AbGroup ℓ-zero} {P : Group₀}
    (f : AbGroupHom A B) (v : GroupHom (AbGroup→Group B) P)
    → Exact₃ f v → isSurjective v → GroupEquiv P (Coker f)
  exact-cokernel {A} {B} {P} f v ex onto = invGroupEquiv (GroupIso→GroupEquiv
    (compGroupIso quotient-change (compGroupIso (invGroupIso (isoThm1 v)) (surjImIso v onto))))
    where
    module B = AbGroupStr (snd B)
    quotient-change : GroupIso (Coker f) (AbGroup→Group B / kerNormalSubgroup v)
    quotient-change = Hom/Iso idGroupIso
      (λ a b → invEq (ex (a B.+ B.- b)))
      (λ a b → equivFun (ex (a B.+ B.- b)))

  -- Injectivity of the H0 map is the correct inner-span tail condition.
  -- It is NOT a vanishing hypothesis on H0 of the three tori.
  exact-onto-before-mono : {B P A D : Group₀}
    (v : GroupHom B P) (d : GroupHom P A) (t : GroupHom A D)
    → Exact₃ v d → Exact₃ d t → isInjective t → isSurjective v
  exact-onto-before-mono v d t ex₁ ex₂ mono p =
    equivFun (ex₁ p) (mono (fst d p) (exact-composite {u = d} {v = t} ex₂ p))

  geometric-H₁-cokernel : (S L R M : CW₀)
    (f : fst S → fst L) (g : fst S → fst R)
    (les : GeometricPushoutLES S L R f g M)
    (q n : ℤ)
    (eS : GroupEquiv (H̃ᶜʷ S 1) (AbGroup→Group ℤ⁶))
    (eV : GroupEquiv (DirProd (H̃ᶜʷ L 1) (H̃ᶜʷ R 1)) (AbGroup→Group vertex₁))
    → ((a : fst (H̃ᶜʷ S 1)) →
      fst (Araw (pos 2) q n) (equivFun (fst eS) a)
        ≡ equivFun (fst eV) (fst (SpanSequenceData.source-map (snd les) 1) a))
    → isInjective (SpanSequenceData.source-map (snd les) 0)
    → GroupEquiv (H̃ᶜʷ M 1) (Coker (Araw (pos 2) q n))
  geometric-H₁-cokernel S L R M f g les q n eS eV square mono =
    compGroupEquiv (exact-cokernel {A = H̃ᶜʷAb S 0}
      {B = dirProdAb (H̃ᶜʷAb L 0) (H̃ᶜʷAb R 0)}
      (Seq.source-map 1) (Seq.sum-map 1) (Seq.exact-target 1 (3 , refl))
      (exact-onto-before-mono (Seq.sum-map 1) (Seq.boundary 0) (Seq.source-map 0)
        (Seq.exact-total 0 (4 , refl)) (Seq.exact-source 0 (4 , refl)) mono))
      (GroupIso→GroupEquiv (Hom/ImIso (Seq.source-map 1) (Araw (pos 2) q n)
        (GroupEquiv→GroupIso eS) (GroupEquiv→GroupIso eV) square))
    where
    module Seq = SpanSequenceData (snd les)
