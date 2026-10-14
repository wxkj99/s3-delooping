{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.SpanPi1.RP2Pi1 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Bool using (Bool; false; true; notEquiv; isSetBool)
open import Cubical.Data.Fin using (Fin; Iso-Bool-Fin2; Fin-fst-≡)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.NatMinusOne
open import Cubical.Algebra.Group.Base using (Group₀; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupEquiv)
open import Cubical.Algebra.Group.Instances.IntMod
  using (ℤGroup/_; pres0→GroupIsoℤ/2)
open import Cubical.HITs.Pushout.Base using (inl; inr; push)
open import Cubical.HITs.RPn.Base using (cov⁻¹; TotalCov≃Sn)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.Homotopy.Connected using (isConnected; isConnectedRetractFromIso)
open import Cubical.Homotopy.Group.Base using (πGr; πIso)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetTruncation as ST
open import DeloopS3.Sphere.RP2UnitFiber
  using (RP²; rpBase; S²≃S2; q-fiber)
open import DeloopS3.Cover.CircleOrbit using (residue)
open import DeloopS3.Seifert.TwistedBundle.Torsor using (frame; frame-self)
import DeloopS3.Seifert.TwistedBundle.Base as B
import DeloopS3.Seifert.TwistedBundle.Chart as Ch
open import DeloopS3.Bridge.SpanPi1.RP2Pi1.UniversalCover

C₂ : Group₀
C₂ = ℤGroup/ 2

one₂ : C₂ .fst
one₂ = residue 1 .fst (pos 1)

private
  F : RP² → Type₀
  F b = cov⁻¹ 2 b .fst

  abstract
    setF : (b : RP²) → isSet (F b)
    setF b = PT.rec isPropIsSet
      (λ e → isOfHLevelRetractFromIso 2 (equivToIso e) isSetBool)
      (cov⁻¹ 2 b .snd)

    cover-connected : isConnected 3 (Σ RP² F)
    cover-connected = isConnectedRetractFromIso 3
      (equivToIso (compEquiv (TotalCov≃Sn 2) (invEquiv S²≃S2)))
      (sphereConnected 2)

  -- The library BoolGroup has unit true. Here false means zero, so use
  -- the opposite Boolean enumeration, without identifying the groups.
  bool≃Fin2 : Bool ≃ Fin 2
  bool≃Fin2 = compEquiv notEquiv (isoToEquiv Iso-Bool-Fin2)

-- An actual equivalence requires an actual sheet, not a merely chosen
-- path to the base point. The frame sends that sheet to false/zero.
module Based (b : RP²) (a : F b) where
  private
    module U = SimplyConnectedCover F setF cover-connected b a

  encode : (b ≡ b) → C₂ .fst
  encode p = bool≃Fin2 .fst (frame (cov⁻¹ 2 b) a .fst (subst F p a))

  carrierEquiv : (πGr 0 (RP² , b) .fst) ≃ C₂ .fst
  carrierEquiv = compEquiv (U.pathEquiv b)
    (compEquiv (frame (cov⁻¹ 2 b) a) bool≃Fin2)

  abstract
    zero-mark : carrierEquiv .fst ST.∣ refl ∣₂ ≡ GroupStr.1g (C₂ .snd)
    zero-mark = cong (bool≃Fin2 .fst)
      (cong (frame (cov⁻¹ 2 b) a .fst) (transportRefl a)
       ∙ frame-self (cov⁻¹ 2 b) a)

  equivalence : GroupEquiv (πGr 0 (RP² , b)) C₂
  equivalence = carrierEquiv , pres0→GroupIsoℤ/2 carrierEquiv zero-mark

-- Both specified base points are handled without choice.
RP²-π₁-cap : GroupEquiv (πGr 0 (RP² , inr tt)) C₂
RP²-π₁-cap = Based.equivalence (inr tt) false

RP²-π₁-rpBase : GroupEquiv (πGr 0 (RP² , rpBase)) C₂
RP²-π₁-rpBase = Based.equivalence rpBase (q-fiber rpBase .fst (north , refl))

abstract
  RP²-cap-paths : (b : RP²) → PT.∥ inr tt ≡ b ∥₁
  RP²-cap-paths (inl x) = PT.rec PT.squash₁
    (λ e → PT.∣ sym (push (x , invEq e false)) ∣₁)
    (cov⁻¹ 1 x .snd)
  RP²-cap-paths (inr _) = PT.∣ refl ∣₁
  RP²-cap-paths (push (x , a) i) = isProp→PathP
    {B = λ j → PT.∥ Path RP² (inr tt) (push (x , a) j) ∥₁}
    (λ _ → PT.squash₁) (RP²-cap-paths (inl x)) PT.∣ refl ∣₁ i

  RP²-π₁ : (b : RP²) → PT.∥ GroupEquiv (πGr 0 (RP² , b)) C₂ ∥₁
  RP²-π₁ b = PT.rec PT.squash₁
    (λ p → PT.∣ subst (λ x → GroupEquiv (πGr 0 (RP² , x)) C₂)
      p RP²-π₁-cap ∣₁) (RP²-cap-paths b)

-- Mark the actual two-edge RP 1 generator at its literal circle vertex.
tBase : RP²
tBase = inl (B.pr₁ Ch.L₀)

RP¹-inclusion : B.R → RP²
RP¹-inclusion = inl

t : tBase ≡ tBase
t = cong RP¹-inclusion Ch.t

RP²-π₁-tBase : GroupEquiv (πGr 0 (RP² , tBase)) C₂
RP²-π₁-tBase = Based.equivalence tBase false

private
  half : Ch.L₀ ≡ Ch.L₁
  half = Ch.E false false ∙ sym (Ch.E true true)

  half-projects : cong B.pr₁ half ≡ Ch.t
  half-projects = cong-∙ B.pr₁ (Ch.E false false) (sym (Ch.E true true))

  t-lift : PathP (λ i → F (t i)) false true
  t-lift = subst (λ p → PathP (λ i → F (inl (p i))) false true)
    half-projects (λ i → half i .snd)

abstract
  RP²-π₁-t : RP²-π₁-tBase .fst .fst ST.∣ t ∣₂ ≡ one₂
  RP²-π₁-t = cong (λ z → bool≃Fin2 .fst (frame (cov⁻¹ 2 tBase) false .fst z))
    (fromPathP t-lift)
    ∙ cong (bool≃Fin2 .fst) (Ch.frame-bool false true)
    ∙ Fin-fst-≡ {n = 2} refl
