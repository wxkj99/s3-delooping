{-# OPTIONS --safe --cubical #-}
module DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.WordPaths where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Data.Sigma using (_,_)
open import Cubical.Data.Int using (ℤ; ·IdR)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.HITs.S1.Base using (base; loop)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
  using (lUnitₖ; rUnitₖ)
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²; mulC; _+C_)
open import DeloopS3.Move.CancelLoopCell using (circleMap)
open import DeloopS3.Cover.Orientation.CircleModel
  using (hC; circleToC; CToCircle; circle-section)
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (row)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

torus-base : T²
torus-base = 0C , 0C

torus-u torus-h : torus-base ≡ torus-base
torus-u i = hC i , 0C
torus-h i = 0C , hC i

core-base : Literal.Core
core-base = Literal.p₀ , 0C

core-incl : Literal.P → Literal.Core
core-incl w = w , 0C

core-a core-b core-h : core-base ≡ core-base
core-a = cong core-incl Literal.a
core-b = cong core-incl Literal.b
core-h i = Literal.p₀ , hC i

core-base₂ : Literal.Core
core-base₂ = Literal.d₂ 0C , 0C

core-edge : core-base ≡ core-base₂
core-edge = cong core-incl Literal.edge

core-fibre : (w : Literal.P) → Path Literal.Core (w , 0C) (w , 0C)
core-fibre w i = w , hC i

abstract
  row-base : (s n : ℤ) → row s n torus-base ≡ 0C
  row-base s n = refl

  row-u : (s n : ℤ) → cong (row s n) torus-u ≡ emloop {Group = ℤGroup} s
  row-u s n =
    (λ j i → rUnitₖ {G = ℤAbGroup} 1 (mulC s (hC i)) j)
    ∙ cong (emloop {Group = ℤGroup}) (·IdR s)

  row-h : (s n : ℤ) → cong (row s n) torus-h ≡ emloop {Group = ℤGroup} n
  row-h s n = cong (emloop {Group = ℤGroup}) (·IdR n)

  boundary₁-u : cong Literal.boundary₁ torus-u ≡ core-a
  boundary₁-u = refl

  boundary₁-h : cong Literal.boundary₁ torus-h ≡ core-h
  boundary₁-h = refl

  boundary₂-u-conjugate :
    ((core-edge ∙ cong Literal.boundary₂ torus-u) ∙ sym core-edge) ≡ core-b
  boundary₂-u-conjugate = sym
    (cong-∙ core-incl (Literal.edge ∙ cong Literal.d₂ hC) (sym Literal.edge)
     ∙ cong (λ (p : core-base ≡ core-base₂) → p ∙ sym core-edge)
         (cong-∙ core-incl Literal.edge (cong Literal.d₂ hC)))

  boundary₂-h : cong Literal.boundary₂ torus-h ≡ core-fibre (Literal.d₂ 0C)
  boundary₂-h = refl

  d₃-loop : cong Literal.d₃ hC ≡ sym (Literal.a ∙ Literal.b)
  d₃-loop =
    cong (cong {x = base} {y = base} (circleMap (sym (Literal.a ∙ Literal.b))))
      (λ j i → circle-section (loop i) j)

  boundary₃-u : cong Literal.boundary₃ torus-u ≡ sym (core-a ∙ core-b)
  boundary₃-u =
    cong (cong {x = Literal.p₀} {y = Literal.p₀} core-incl) d₃-loop
    ∙ cong (λ (p : core-base ≡ core-base) → sym p)
        (cong-∙ core-incl Literal.a Literal.b)

  boundary₃-h : cong Literal.boundary₃ torus-h ≡ core-h
  boundary₃-h = refl
