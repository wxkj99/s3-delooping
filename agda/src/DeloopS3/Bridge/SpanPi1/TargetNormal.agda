{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.TargetNormal where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·; rUnitℤ·ℤ)
open import DeloopS3.Cert.Interpret.Short using (ShortCase; octa; icosa)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Input.Model as Model
open import DeloopS3.Bridge.SpanPi1.TargetLoops
open import DeloopS3.Bridge.SpanPi1.TargetRelations
open import DeloopS3.Bridge.SpanPi1.TargetWords
open import DeloopS3.Bridge.SpanPi1.TargetGeneration
import DeloopS3.Bridge.SpanPi1.WordAlgebra as WA

-- Generation AND relations of the actual fundamental group.  This is
-- not an assumed presentation, a replacement group, or a normal-closure
-- hypothesis.  All fields are inhabited below by the actual HIT proofs.
record TargetGenerated (c : ShortCase) : Type₀ where
  field
    generated : (u : fst (G c)) → Membership.Generated (G c) (x c) (y c) u
    square-fibre : WA.Words.square (G c) (x c) ≡ h c
    cube-fibre : WA.Words.cube (G c) (y c) ≡ h c
    third-word : z c ≡ WA.Words.z (G c) (x c) (y c)
    third-power : (pos (Model.localOrder c Ch.C) ℤ[ G c ]· z c) ≡ h c

abstract
  target-generated : (c : ShortCase) → TargetGenerated c
  TargetGenerated.generated (target-generated c) = Generation.generated c
  TargetGenerated.square-fibre (target-generated c) = x²=h c
  TargetGenerated.cube-fibre (target-generated c) = y³=h c
  TargetGenerated.third-word (target-generated c) = z=y⁻¹x c
  TargetGenerated.third-power (target-generated c) =
    sym (cong (corePower c Ch.C) (sym (rUnitℤ·ℤ n))
      ∙ homPresℤ· (corePowerHom c Ch.C) (pos 1) n)
    ∙ sym (seam-t c Ch.C)
    where
    n : ℤ
    n = pos (Model.localOrder c Ch.C)

module HomWords (K L : Group₀) (f : GroupHom K L) where
  private
    module K = GroupStr (snd K)
    module L = GroupStr (snd L)
    module WK = WA.Words K
    module WL = WA.Words L
    F = fst f
  abstract
    map-square : (a : fst K) → F (WK.square a) ≡ WL.square (F a)
    map-square a = IsGroupHom.pres· (snd f) a a
    map-cube : (a : fst K) → F (WK.cube a) ≡ WL.cube (F a)
    map-cube a = IsGroupHom.pres· (snd f) _ a
      ∙ cong (L._· F a) (map-square a)
    map-fifth : (a : fst K) → F (WK.fifth a) ≡ WL.fifth (F a)
    map-fifth a = IsGroupHom.pres· (snd f) _ _
      ∙ cong₂ L._·_ (map-square a) (map-cube a)
    map-z : (a b : fst K) → F (WK.z a b) ≡ WL.z (F a) (F b)
    map-z a b = IsGroupHom.pres· (snd f) _ a
      ∙ cong (L._· F a) (IsGroupHom.presinv (snd f) b)

abstract
  target-generators-killed : (c : ShortCase) (L : Group₀) (f : GroupHom (G c) L)
    → fst f (w c) ≡ GroupStr.1g (snd L)
    → (fst f (x c) ≡ GroupStr.1g (snd L)) × (fst f (y c) ≡ GroupStr.1g (snd L))
  target-generators-killed octa L f kw = W.O-kill (fst f (x octa)) (fst f (y octa)) rel
    (W.O-word _ _ rel ∙ sym (HW.map-z (x octa) (y octa))
      ∙ cong (fst f) (sym (z=y⁻¹x octa)) ∙ kw)
    where
    module W = WA.Words L
    module HW = HomWords (G octa) L f
    rel : W.square (fst f (x octa)) ≡ W.cube (fst f (y octa))
    rel = sym (HW.map-square (x octa)) ∙ cong (fst f) (x²=y³ octa) ∙ HW.map-cube (y octa)
  target-generators-killed icosa L f kw = W.I-kill (fst f (x icosa)) (fst f (y icosa)) rel₂ rel₅
    (W.I-word _ _ rel₅ ∙ kw)
    where
    module W = WA.Words L
    module HW = HomWords (G icosa) L f
    rel₂ : W.square (fst f (x icosa)) ≡ W.cube (fst f (y icosa))
    rel₂ = sym (HW.map-square (x icosa)) ∙ cong (fst f) (x²=y³ icosa) ∙ HW.map-cube (y icosa)
    rel₅ : W.square (fst f (x icosa)) ≡ W.fifth (W.z (fst f (x icosa)) (fst f (y icosa)))
    rel₅ = sym (HW.map-square (x icosa)) ∙ cong (fst f) x²=z⁵
      ∙ HW.map-fifth (WA.Words.z (G icosa) (x icosa) (y icosa))
      ∙ cong W.fifth (HW.map-z (x icosa) (y icosa))

  target-normal-generation : (c : ShortCase) (L : Group₀) (f : GroupHom (G c) L)
    → fst f (w c) ≡ GroupStr.1g (snd L)
    → (u : fst (G c)) → fst f u ≡ GroupStr.1g (snd L)
  target-normal-generation c L f kw u = Membership.kill (G c) (x c) (y c) L f
    (fst killed) (snd killed) u (TargetGenerated.generated (target-generated c) u)
    where
    killed : (fst f (x c) ≡ GroupStr.1g (snd L)) × (fst f (y c) ≡ GroupStr.1g (snd L))
    killed = target-generators-killed c L f kw
