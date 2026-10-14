{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.SourceCharacter.Klein where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·; rUnitℤ·ℤ)
open import Cubical.HITs.S1.Base
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Move.CancelMinimal using (C; 0C)
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Bridge.SpanPi1.Seam using (Π)
open import DeloopS3.Bridge.SpanPi1.Fibre using (module Map)
open import DeloopS3.Bridge.SpanPi1.FibreGenerator using (module CircleFibre)
open import DeloopS3.Bridge.SpanPi1.Character using (KleinNF)
import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus as M
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary using (based; based-comp; based-refl)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.FilledLoops using (based-sym)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third using (cong-based)
import DeloopS3.Bridge.SpanPi1.SourceCharacter.Algebra as Algebra

abstract
  based-unbased : ∀ {ℓ} {X : Type ℓ} {a b : X} (p : a ≡ b) (l : b ≡ b)
    → based p ((p ∙ l) ∙ sym p) ≡ l
  based-unbased {b = b} p = J (λ a q → (l : b ≡ b)
    → based (sym q) ((sym q ∙ l) ∙ sym (sym q)) ≡ l)
    (λ l → based-refl ((refl ∙ l) ∙ refl)
      ∙ cong (_∙ refl) (sym (lUnit l)) ∙ sym (rUnit l)) (sym p)

module NegativeCircle where
  P : Group₀
  P = Π S¹ base
  generator : fst P
  generator = ST.∣ sym loop ∣₂
  power : ℤ → fst P
  power n = ST.∣ cong invLooper (intLoop n) ∣₂

  abstract
    powerHom : GroupHom ℤGroup P
    powerHom = power , makeIsGroupHom (λ a b → cong ST.∣_∣₂
      (cong (cong invLooper) (sym (intLoop-hom a b))
        ∙ cong-∙ invLooper (intLoop a) (intLoop b)))
    power-one : power (pos 1) ≡ generator
    power-one = cong ST.∣_∣₂ (cong (cong invLooper) (sym (lUnit loop)))
    power-is-power : (n : ℤ) → power n ≡ (n ℤ[ P ]· generator)
    power-is-power n = cong power (sym (rUnitℤ·ℤ n))
      ∙ homPresℤ· powerHom (pos 1) n ∙ cong (λ z → n ℤ[ P ]· z) power-one
    generated : (u : fst P) → PT.∥ Σ[ n ∈ ℤ ] u ≡ (n ℤ[ P ]· generator) ∥₁
    generated = ST.elim (λ _ → isProp→isSet PT.squash₁) λ s →
      PT.∣ winding (cong invLooper s) ,
        sym (cong ST.∣_∣₂
          (cong (cong invLooper) (Iso.ret ΩS¹Isoℤ (cong invLooper s))
            ∙ (λ i j → invInvolutive (s j) i)))
        ∙ power-is-power (winding (cong invLooper s)) ∣₁

point : M.Kinv
point = base , 0C
P : Group₀
P = Π M.Kinv point
rLoop jLoop : point ≡ point
rLoop = cong M.fibre hC
jLoop = based M.klein-base M.j
r j : fst P
r = ST.∣ rLoop ∣₂
j = ST.∣ jLoop ∣₂
projection : GroupHom P NegativeCircle.P
projection = Map.mapπ fst point , makeIsGroupHom
  (ST.elim2 (λ _ _ → isProp→isSet (ST.squash₂ _ _))
    (λ s t → cong ST.∣_∣₂ (cong-∙ fst s t)))

module F = CircleFibre (fst {B = M.Dinv}) base
  (fiberProjEquiv S¹ M.Dinv base)

abstract
  r-mark : based M.klein-base M.r ≡ rLoop
  r-mark = cong (based M.klein-base) M.r-as-fibre
    ∙ based-unbased M.klein-base rLoop

  j-projects : fst projection j ≡ NegativeCircle.generator
  j-projects = cong ST.∣_∣₂
    (cong-based fst M.klein-base M.j ∙ M.j-baseProjection)

  kernel-generated : (u : fst P) → fst projection u ≡ GroupStr.1g (snd NegativeCircle.P)
    → PT.∥ Σ[ n ∈ ℤ ] (n ℤ[ P ]· r) ≡ u ∥₁
  kernel-generated = F.kernel-generated

  quotient-generated : (u : fst NegativeCircle.P)
    → PT.∥ Σ[ n ∈ ℤ ] u ≡ (n ℤ[ NegativeCircle.P ]· fst projection j) ∥₁
  quotient-generated u = PT.map (λ { (n , p) → n ,
    p ∙ cong (λ z → n ℤ[ NegativeCircle.P ]· z) (sym j-projects) })
    (NegativeCircle.generated u)

  generated : KleinNF P r j
  generated = Algebra.CyclicExtension.generated P NegativeCircle.P projection r j
    kernel-generated quotient-generated

  inversion-loop : jLoop ∙ rLoop ≡ sym rLoop ∙ jLoop
  inversion-loop = cong (jLoop ∙_) (sym r-mark)
    ∙ sym (based-comp M.klein-base M.j M.r)
    ∙ cong (based M.klein-base) M.κ
    ∙ based-comp M.klein-base (sym M.r) M.j
    ∙ cong (_∙ jLoop) (based-sym M.klein-base M.r ∙ cong sym r-mark)

  inversion : GroupStr._·_ (snd P) j r ≡ GroupStr._·_ (snd P) (GroupStr.inv (snd P) r) j
  inversion = cong ST.∣_∣₂ inversion-loop
