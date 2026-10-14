{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.TargetVertexGeneration where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc)
open import Cubical.HITs.Pushout.Base using (inl)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emloop-comp)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Bouquet.Base as B
import Cubical.HITs.Bouquet.FundamentalGroupProof as BP
import Cubical.HITs.FreeGroupoid as FG
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·; rUnitℤ·ℤ)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Homotopy.EilenbergMacLane.Properties using (ΩEM₁Iso)
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Model
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Bridge.SpanPi1.TargetLoops
open import DeloopS3.Bridge.SpanPi1.TargetRelations
open import DeloopS3.Bridge.SpanPi1.TargetWords

roseTo : Model.Γ → B.Bouquet (Fin 2)
roseTo R.root = B.base
roseTo (R.petal k i) = B.loop k i
roseFrom : B.Bouquet (Fin 2) → Model.Γ
roseFrom B.base = R.root
roseFrom (B.loop k i) = R.petal k i
roseRet : (v : Model.Γ) → roseFrom (roseTo v) ≡ v
roseRet R.root = refl
roseRet (R.petal k i) = refl

module Vertices (c : ShortCase) where
  open Membership (G c) (x c) (y c) public

  GenPath : (m₀ c ≡ m₀ c) → Type₀
  GenPath p = Generated ST.∣ p ∣₂

  abstract
    gen-h : Generated (h c)
    gen-h = subst Generated (x²=h c) (product gen-x gen-x)

    gen-core : (k : Ch.Kind) → Generated (coreClass c k)
    gen-core Ch.A = gen-x
    gen-core Ch.B = gen-y
    gen-core Ch.C = subst Generated (sym (z=y⁻¹x c)) (product (invert gen-y) gen-x)

    core-power-generated : (k : Ch.Kind) (n : ℤ) → Generated (corePower c k n)
    core-power-generated k n = subst Generated
      (sym (cong (corePower c k) (sym (rUnitℤ·ℤ n))
        ∙ homPresℤ· (corePowerHom c k) (pos 1) n))
      (power n (gen-core k))

    core-loop-generated : (k : Ch.Kind) (p : R.0C ≡ R.0C)
      → GenPath (coreEdge c k ∙∙ cong (coreCircle c k) p ∙∙ sym (coreEdge c k))
    core-loop-generated k p = subst GenPath
      (cong (λ q → coreEdge c k ∙∙ cong (coreCircle c k) q ∙∙ sym (coreEdge c k))
        (Iso.ret (ΩEM₁Iso ℤGroup) p))
      (core-power-generated k (Iso.fun (ΩEM₁Iso ℤGroup) p))

    petal-generated : (k : Fin 2) → GenPath (cong (graphIncl c) (R.petal k))
    petal-generated fzero = subst Generated
      (sym (seam-u c Ch.A)
        ∙ cong ST.∣_∣₂ (cong (cong (graphIncl c)) (sym (rUnit (R.petal fzero))))) gen-x
    petal-generated (fsuc fzero) = subst Generated
      (sym (seam-u c Ch.B)
        ∙ cong ST.∣_∣₂ (cong (cong (graphIncl c)) (sym (rUnit (R.petal (fsuc fzero)))))) gen-y
    petal-generated (fsuc (fsuc ()))

    bouquet-generated : (v : FG.FreeGroupoid (Fin 2))
      → GenPath (cong (λ a → graphIncl c (roseFrom a)) (BP.looping v))
    bouquet-generated = FG.elimProp (λ _ → PT.squash₁) petal-generated
      (λ u v pu pv → subst GenPath (sym (cong-∙ (λ a → graphIncl c (roseFrom a))
        (BP.looping u) (BP.looping v))) (product pu pv))
      one (λ _ → invert)

    graph-loop-generated : (p : Path Model.Γ R.root R.root)
      → GenPath (cong (graphIncl c) p)
    graph-loop-generated p = subst GenPath
      (cong (cong (λ a → graphIncl c (roseFrom a))) (BP.decodeEncode B.base (cong roseTo p))
        ∙ cong (cong (graphIncl c)) (λ j i → roseRet (p i) j))
      (bouquet-generated (BP.winding (cong roseTo p)))

  leftIncl : Model.Γ × R.C → Model.M_G c
  leftIncl = inl
  fibreCircle : R.C → Model.M_G c
  fibreCircle t = leftIncl (R.root , t)

  fibrePower : ℤ → fst (G c)
  fibrePower n = ST.∣ cong fibreCircle (emloop n) ∣₂

  fibrePowerHom : GroupHom ℤGroup (G c)
  fibrePowerHom = fibrePower , makeIsGroupHom (λ n m → cong ST.∣_∣₂
    (cong (cong fibreCircle)
      (emloop-comp ℤGroup n m)
     ∙ cong-∙ fibreCircle (emloop n) (emloop m)))

  abstract
    fibre-loop-generated : (p : R.0C ≡ R.0C)
      → GenPath (λ i → inl (R.root , p i))
    fibre-loop-generated p = subst Generated
      (sym (cong fibrePower (sym (rUnitℤ·ℤ n)) ∙ homPresℤ· fibrePowerHom (pos 1) n)
       ∙ cong (λ q → ST.∣ cong fibreCircle q ∣₂)
          (Iso.ret (ΩEM₁Iso ℤGroup) p)) (power n gen-h)
      where
      n : ℤ
      n = Iso.fun (ΩEM₁Iso ℤGroup) p

    left-loop-generated : (p : Path (Model.Γ × R.C) (R.root , R.0C) (R.root , R.0C))
      → GenPath (cong leftIncl p)
    left-loop-generated p = subst GenPath
      (sym (cong-∙ leftIncl
        (λ i → fst (p i) , R.0C) (λ i → R.root , snd (p i)))
       ∙ cong (cong leftIncl)
         (sym (cong₂Funct (λ u v → fst u , snd v) p p)))
      (product (graph-loop-generated (cong fst p)) (fibre-loop-generated (cong snd p)))
