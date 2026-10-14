{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Geometric where

-- The geometric pushout LES and its map-compatible homology data.
-- Algebraic exactness is transported along the specified comparison.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
open import Cubical.CW.Base using (CWskel ; realise)
open import Cubical.CW.ChainComplex using (CW-AugChainComplex)
open import Cubical.HITs.Pushout using (Pushout ; inl ; inr)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃ ; cellular-map)
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.CellularPushout.Algebra
open import DeloopS3.Bridge.DMCExactness.Maps
open import DeloopS3.Bridge.DMCExactness.Exactness
open import DeloopS3.Bridge.DMCExactness.Transport

actual-source : (A B C : CW₀) (f : fst A → fst B) (g : fst A → fst C)
  (n : ℕ) → fst (H̃ᶜʷ A n) → fst (DirProd (H̃ᶜʷ B n) (H̃ᶜʷ C n))
actual-source A B C f g n a = fst (cellular-map A B n f) a ,
  GroupStr.inv (snd (H̃ᶜʷ C n)) (fst (cellular-map A C n g) a)

actual-sum : (A B C : CW₀) (f : fst A → fst B) (g : fst A → fst C)
  (P : CW₀) → fst P ≡ Pushout f g → (n : ℕ)
  → fst (DirProd (H̃ᶜʷ B n) (H̃ᶜʷ C n)) → fst (H̃ᶜʷ P n)
actual-sum A B C f g P p n (b , c) = GroupStr._·_ (snd (H̃ᶜʷ P n))
  (fst (cellular-map B P n (transport (sym p) ∘ inl)) b)
  (fst (cellular-map C P n (transport (sym p) ∘ inr)) c)

-- Factor all record elaboration through abstract GROUP FAMILIES, as in
-- CofibreSequenceData. Instantiating a record directly with H̃ᶜʷ causes
-- expensive cellular-approximation normalization during elaboration.
record SpanSequenceData (HA HB HC HP : ℕ → Group₀)
  (source : (n : ℕ) → fst (HA n) → fst (DirProd (HB n) (HC n)))
  (vertices : (n : ℕ) → fst (DirProd (HB n) (HC n)) → fst (HP n)) : Type where
  field
    source-map : (n : ℕ) → GroupHom (HA n) (DirProd (HB n) (HC n))
    sum-map : (n : ℕ) → GroupHom (DirProd (HB n) (HC n)) (HP n)
    source-agrees : (n : ℕ) (a : fst (HA n)) → fst (source-map n) a ≡ source n a
    sum-agrees : (n : ℕ) (x : fst (DirProd (HB n) (HC n))) → fst (sum-map n) x ≡ vertices n x
    boundary : (n : ℕ) → GroupHom (HP (suc n)) (HA n)
    exact-total : (n : ℕ) → n < 5 → Exact₃ (sum-map (suc n)) (boundary n)
    exact-source : (n : ℕ) → n < 5 → Exact₃ (boundary n) (source-map n)
    exact-target : (n : ℕ) → n < 5 → Exact₃ (source-map n) (sum-map n)

-- Separate from the unconditional CHAIN-COMPLEX record in LES.agda.
GeometricPushoutLES : (A B C : CW₀) (f : fst A → fst B) (g : fst A → fst C)
  (P : CW₀) → Type₁
GeometricPushoutLES A B C f g P = Σ[ p ∈ (fst P ≡ Pushout f g) ]
  SpanSequenceData (H̃ᶜʷ A) (H̃ᶜʷ B) (H̃ᶜʷ C) (H̃ᶜʷ P)
    (actual-source A B C f g) (actual-sum A B C f g P p)

