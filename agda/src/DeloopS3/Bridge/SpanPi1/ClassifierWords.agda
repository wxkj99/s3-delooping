{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.ClassifierWords where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (pos)
open import Cubical.Data.SumFin using (fzero; fsuc)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.HITs.Pushout.Base using (inl)
open import Cubical.HITs.EilenbergMacLane1.Base
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Model
import DeloopS3.Cover.Cosets as Cosets
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Bridge.SpanPi1.TargetLoops
import DeloopS3.Bridge.SpanPi1.Character as Character
open import DeloopS3.Bridge.SpanPi1.CharacterTables using (Term; X; Y; _⊗_; inverse; eval)
open Short using (ShortCase; octa; icosa)

-- Literal rose words y x y⁻¹ and v x v⁻¹ in M_G representing the rooted
-- reflection petals.
wordLoop : (c : ShortCase) → Term → m₀ c ≡ m₀ c
wordLoop c X i = inl (R.petal fzero i , R.0C)
wordLoop c Y i = inl (R.petal (fsuc fzero) i , R.0C)
wordLoop c (u ⊗ v) = wordLoop c u ∙ wordLoop c v
wordLoop c (inverse u) = sym (wordLoop c u)

caseCore : ShortCase → Ch.Kind
caseCore octa = Ch.C
caseCore icosa = Ch.B

abstract
  classifier-word : (c : ShortCase) (t : Term)
    → cong (Model.ρ-M c) (wordLoop c t)
      ≡ emloop (eval (Short.Δ c) (Short.generator-a c) (Short.generator-b c) t)
  classifier-word c X = refl
  classifier-word c Y = refl
  classifier-word c (u ⊗ v) = cong-∙ (Model.ρ-M c) (wordLoop c u) (wordLoop c v)
    ∙ cong₂ _∙_ (classifier-word c u) (classifier-word c v)
    ∙ sym (emloop-comp (Short.Δ c) _ _)
  classifier-word c (inverse u) = cong sym (classifier-word c u)
    ∙ sym (emloop-sym (Short.Δ c) _)

  classifier-core : (c : ShortCase) (k : Ch.Kind)
    → cong (Model.ρ-M c) (coreLoop c k) ≡ emloop (Model.genElement c k)
  classifier-core c k = cong-∙∙ (Model.ρ-M c) (coreEdge c k)
      (cong (coreCircle c k) hC) (sym (coreEdge c k))
    ∙ cong₂ (λ s t → s ∙∙ t ∙∙ sym s) (Model.classifier-seam-base c k)
      (Model.coreMark-loop c k (pos 1)
        ∙ cong emloop (GroupStr.·IdR (snd (Short.Δ c)) (Model.genElement c k)))
    ∙ sym (rUnit (emloop (Model.genElement c k)))

  inclusion-hom : (c : ShortCase) (d : fst (Short.H c))
    → fst (Character.inclusion c) d ≡ fst (Cosets.hom (Short.j c)) d
  inclusion-hom octa d = refl
  inclusion-hom icosa d = refl

  A-inverse : (c : ShortCase)
    → GroupStr.inv (snd (Short.Δ c)) (Model.genElement c Ch.A) ≡ Model.genElement c Ch.A
  A-inverse c = sym (GroupTheory.invUniqueR (Short.Δ c)
    (cong (GroupStr._·_ (snd (Short.Δ c)) (Model.genElement c Ch.A))
      (sym (GroupStr.·IdR (snd (Short.Δ c)) (Model.genElement c Ch.A)))
      ∙ Model.gen-order c Ch.A))

  rotation-core-element : (c : ShortCase)
    → Model.genElement c (caseCore c) ≡ Character.rotationDownstairs c
  rotation-core-element octa = Model.gen-c-inverses octa
    ∙ cong (GroupStr._·_ (snd (Short.Δ octa))
        (GroupStr.inv (snd (Short.Δ octa)) (Short.generator-b octa))) (A-inverse octa)
  rotation-core-element icosa = refl
