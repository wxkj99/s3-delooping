{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.CoverWitnesses where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
open import Cubical.Algebra.Group.Base
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Cert.Input.Model as Model
import DeloopS3.Cover.Cosets as Cosets
open import DeloopS3.Bridge.SpanPi1.Coordinates
open import DeloopS3.Bridge.SpanPi1.TargetLoops using (coreLoop)
open import DeloopS3.Bridge.SpanPi1.ClassifierWords
import DeloopS3.Bridge.SpanPi1.Character as Character
open Short using (ShortCase; octa; icosa)

abstract
  core-class-is-w : (c : ShortCase) → ST.∣ coreLoop c (caseCore c) ∣₂ ≡ w c
  core-class-is-w octa = refl
  core-class-is-w icosa = refl

  rotation-classifier : (c : ShortCase)
    → cong (Model.ρ-M c) (coreLoop c (caseCore c))
      ≡ emloop (fst (Cosets.hom (Short.j c)) (Character.rotation c))
  rotation-classifier c = classifier-core c (caseCore c)
    ∙ cong emloop (rotation-core-element c ∙ Character.rotation-word-image c
      ∙ inclusion-hom c (Character.rotation c))

  reflection-classifier : (c : ShortCase)
    → cong (Model.ρ-M c) (wordLoop c (Character.reflectionTerm c))
      ≡ emloop (fst (Cosets.hom (Short.j c)) (Character.reflection c))
  reflection-classifier c = classifier-word c (Character.reflectionTerm c)
    ∙ cong emloop (Character.reflection-word-image c ∙ inclusion-hom c (Character.reflection c))

  rotation-lift : (c : ShortCase)
    → Σ[ u ∈ fst (K c) ]
      (fst (projectionπ c) u ≡ w c) × (fst (subgroupπ c) u ≡ Character.rotation c)
  rotation-lift c = u , (p ∙ core-class-is-w c) , s
    where
    lifted : Σ[ u ∈ fst (K c) ]
      (fst (projectionπ c) u ≡ ST.∣ coreLoop c (caseCore c) ∣₂)
      × (fst (subgroupπ c) u ≡ Character.rotation c)
    lifted = classifier-class-lift c (coreLoop c (caseCore c)) (Character.rotation c)
      (rotation-classifier c)
    u : fst (K c)
    u = lifted .fst
    p : fst (projectionπ c) u ≡ ST.∣ coreLoop c (caseCore c) ∣₂
    p = lifted .snd .fst
    s : fst (subgroupπ c) u ≡ Character.rotation c
    s = lifted .snd .snd

  reflection-lift : (c : ShortCase)
    → Σ[ u ∈ fst (K c) ] fst (subgroupπ c) u ≡ Character.reflection c
  reflection-lift c = lifted .fst , lifted .snd .snd
    where
    lifted : Σ[ u ∈ fst (K c) ]
      (fst (projectionπ c) u ≡ ST.∣ wordLoop c (Character.reflectionTerm c) ∣₂)
      × (fst (subgroupπ c) u ≡ Character.reflection c)
    lifted = classifier-class-lift c (wordLoop c (Character.reflectionTerm c))
      (Character.reflection c) (reflection-classifier c)

  normal-core-lift : (c : ShortCase)
    → Σ[ u ∈ fst (K c) ] (fst (projectionπ c) u ≡ w c)
      × (fst (Character.rotationCharacter c) (fst (subgroupπ c) u) ≡ zero₂)
  normal-core-lift c = rotation-lift c .fst , rotation-lift c .snd .fst ,
    (cong (fst (Character.rotationCharacter c)) (rotation-lift c .snd .snd)
      ∙ Character.rotationCharacter-rotation c)

  subgroup-image-nonabelian : (c : ShortCase) → Character.NonabelianImage (subgroupπ c)
  subgroup-image-nonabelian c = PT.∣ rotation-lift c .fst , reflection-lift c .fst , noncomm ∣₁
    where
    module H = GroupStr (snd (Short.H c))
    r s : fst (Short.H c)
    r = fst (subgroupπ c) (rotation-lift c .fst)
    s = fst (subgroupπ c) (reflection-lift c .fst)
    noncomm : r H.· s ≡ s H.· r → ⊥
    noncomm eq = Character.rotation-reflection-noncommute c
      (sym (cong₂ H._·_ (rotation-lift c .snd .snd) (reflection-lift c .snd))
        ∙ eq ∙ cong₂ H._·_ (reflection-lift c .snd) (rotation-lift c .snd .snd))
