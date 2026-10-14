{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.TargetRelations where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos)
import Cubical.Data.Int as Z
open import Cubical.HITs.Pushout.Base using (inl; push)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emloop-comp)
import Cubical.HITs.SetTruncation as ST
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom; compGroupHom)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Homotopy.Group.Base using (πGr; πHom)
open import DeloopS3.Cert.Interpret.Short using (ShortCase; octa; icosa)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Model
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Bridge.SpanPi1.TargetLoops
import DeloopS3.Bridge.SpanPi1.WordAlgebra as WA

-- The elementary square calculation retains the tree edge explicitly.
abstract
  square-conjugate : ∀ {ℓ} {X : Type ℓ} {a b : X}
    (p : a ≡ a) (q : b ≡ b) (e : a ≡ b)
    → PathP (λ j → e j ≡ e j) p q
    → p ≡ (e ∙∙ q ∙∙ sym e)
  square-conjugate p q e sq = rUnit p ∙ λ j →
    (λ i → e (i ∧ j)) ∙∙ sq j ∙∙ (λ i → e (~ i ∧ j))

integerCircle : GroupHom ℤGroup (πGr 0 (R.C , R.0C))
integerCircle = (λ n → ST.∣ emloop n ∣₂) , makeIsGroupHom
  (λ n m → cong ST.∣_∣₂ (emloop-comp ℤGroup n m))

corePowerHom : (c : ShortCase) (k : Ch.Kind) → GroupHom ℤGroup (G c)
corePowerHom c k = compGroupHom integerCircle
  (πHom 0 (coreCircle c k , sym (coreEdge c k)))

corePower : (c : ShortCase) → Ch.Kind → ℤ → fst (G c)
corePower c k = fst (corePowerHom c k)

graphIncl : (c : ShortCase) → Model.Γ → Model.M_G c
graphIncl c v = inl (v , R.0C)

graphClass : (c : ShortCase) → Ch.Kind → fst (G c)
graphClass c k = ST.∣ cong (graphIncl c) (R.roseWord Model.twoGenerators (Ch.kindWord k)) ∣₂

abstract
  seam-u : (c : ShortCase) (k : Ch.Kind)
    → graphClass c k ≡ corePower c k (Model.localWeight c k)
  seam-u c k = cong ST.∣_∣₂
    (cong (cong (graphIncl c)) (sym (R.wordCircle-loop Model.twoGenerators (Ch.kindWord k)))
     ∙ square-conjugate _ _ (coreEdge c k)
       (λ j i → push (k , hC i , R.0C) j)
     ∙ cong (λ l → coreEdge c k ∙∙ cong (coreCircle c k) l ∙∙ sym (coreEdge c k))
       (Model.row-u-loop (Model.localWeight c k) (Model.localOrder c k)))

  seam-t : (c : ShortCase) (k : Ch.Kind)
    → h c ≡ corePower c k (pos (Model.localOrder c k))
  seam-t c k = cong ST.∣_∣₂
    (square-conjugate _ _ (coreEdge c k)
       (λ j i → push (k , R.0C , hC i) j)
     ∙ cong (λ l → coreEdge c k ∙∙ cong (coreCircle c k) l ∙∙ sym (coreEdge c k))
       (Model.row-t-loop (Model.localWeight c k) (Model.localOrder c k)))

  corePower-add : (c : ShortCase) (k : Ch.Kind) (a b : ℤ)
    → corePower c k (a Z.+ b)
      ≡ GroupStr._·_ (snd (G c)) (corePower c k a) (corePower c k b)
  corePower-add c k = IsGroupHom.pres· (snd (corePowerHom c k))

  corePower-two : (c : ShortCase) (k : Ch.Kind)
    → corePower c k (pos 2) ≡ WA.Words.square (G c) (coreClass c k)
  corePower-two c k = corePower-add c k (pos 1) (pos 1)

  corePower-three : (c : ShortCase) (k : Ch.Kind)
    → corePower c k (pos 3) ≡ WA.Words.cube (G c) (coreClass c k)
  corePower-three c k = corePower-add c k (pos 2) (pos 1)
    ∙ cong (λ u → GroupStr._·_ (snd (G c)) u (coreClass c k)) (corePower-two c k)

  corePower-five : (c : ShortCase) (k : Ch.Kind)
    → corePower c k (pos 5) ≡ WA.Words.fifth (G c) (coreClass c k)
  corePower-five c k = corePower-add c k (pos 2) (pos 3)
    ∙ cong₂ (GroupStr._·_ (snd (G c))) (corePower-two c k) (corePower-three c k)

  x²=h : (c : ShortCase) → WA.Words.square (G c) (x c) ≡ h c
  x²=h c = sym (corePower-two c Ch.A) ∙ sym (seam-t c Ch.A)

  y³=h : (c : ShortCase) → WA.Words.cube (G c) (y c) ≡ h c
  y³=h c = sym (corePower-three c Ch.B) ∙ sym (seam-t c Ch.B)

  x²=y³ : (c : ShortCase) → WA.Words.square (G c) (x c) ≡ WA.Words.cube (G c) (y c)
  x²=y³ c = x²=h c ∙ sym (y³=h c)

abstract
  graph-C : (c : ShortCase)
    → graphClass c Ch.C ≡ GroupStr._·_ (snd (G c))
        (GroupStr.inv (snd (G c)) (graphClass c Ch.B))
        (GroupStr.inv (snd (G c)) (graphClass c Ch.A))
  graph-C c = cong ST.∣_∣₂
    (cong (cong (graphIncl c))
      (cong (sym b ∙_) (sym (rUnit (sym a)))
       ∙ cong₂ _∙_ (cong sym (rUnit b)) (cong sym (rUnit a)))
     ∙ cong-∙ (graphIncl c) (sym (b ∙ refl)) (sym (a ∙ refl)))
    where
    a b : Path Model.Γ R.root R.root
    a = R.loopAt Model.twoGenerators 1
    b = R.loopAt Model.twoGenerators 2

  weight-plus-order : (c : ShortCase)
    → Model.localWeight c Ch.C Z.+ pos (Model.localOrder c Ch.C) ≡ pos 1
  weight-plus-order octa = refl
  weight-plus-order icosa = refl

  z=y⁻¹x : (c : ShortCase) → z c ≡ WA.Words.z (G c) (x c) (y c)
  z=y⁻¹x c =
    sym (cong (corePower c Ch.C) (weight-plus-order c))
    ∙ corePower-add c Ch.C (Model.localWeight c Ch.C) (pos (Model.localOrder c Ch.C))
    ∙ cong₂ _·_ (sym (seam-u c Ch.C)) (sym (seam-t c Ch.C))
    ∙ cong₂ _·_ (graph-C c ∙ cong₂ (λ a b → inv a · inv b) (seam-u c Ch.B) (seam-u c Ch.A))
        (sym (x²=h c))
    ∙ sym (·Assoc (inv (y c)) (inv (x c)) (x c · x c))
    ∙ cong (inv (y c) ·_)
        (·Assoc (inv (x c)) (x c) (x c)
         ∙ cong (_· x c) (·InvL (x c)) ∙ ·IdL (x c))
    where open GroupStr (snd (G c))

  z⁴=h : WA.Words.square (G octa) (WA.Words.square (G octa) (z octa)) ≡ h octa
  z⁴=h = sym
    (corePower-add octa Ch.C (pos 2) (pos 2)
     ∙ cong₂ (GroupStr._·_ (snd (G octa)))
       (corePower-two octa Ch.C) (corePower-two octa Ch.C))
    ∙ sym (seam-t octa Ch.C)

  z⁵=h : WA.Words.fifth (G icosa) (z icosa) ≡ h icosa
  z⁵=h = sym (corePower-five icosa Ch.C) ∙ sym (seam-t icosa Ch.C)

  x²=z⁵ : WA.Words.square (G icosa) (x icosa)
    ≡ WA.Words.fifth (G icosa) (WA.Words.z (G icosa) (x icosa) (y icosa))
  x²=z⁵ = x²=h icosa ∙ sym z⁵=h ∙ cong (WA.Words.fifth (G icosa)) (z=y⁻¹x icosa)
