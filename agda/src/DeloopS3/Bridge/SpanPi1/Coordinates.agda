{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.Coordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom; GroupEquiv→GroupHom)
open import Cubical.Homotopy.Group.Base using (πHom)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)
import Cubical.HITs.SetTruncation as ST
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Cert.Input.Model as Model
import DeloopS3.Bridge.OriginalSpan as OS
import DeloopS3.Cover.Cosets as Cosets
open import DeloopS3.Bridge.SpanPi1.Seam using (Π; πHom-loop)
open import DeloopS3.Bridge.SpanPi1.ClassifierLift public
open import DeloopS3.Bridge.SpanPi1.TargetLoops public using (G; w)
open import DeloopS3.Bridge.SpanPi1.EMEncode using (encodeHom; encodeHom-loop)
open import DeloopS3.Bridge.SpanPi1.CharacterPairs public using (C₂; zero₂; one₂)
open Short using (ShortCase)

K : ShortCase → Group₀
K c = Π (Model.A_G c) (a₀ c)

qCover : (c : ShortCase) → Model.A_G c → OS.R
qCover c = OS.q c ∘ invEq (OS.sourceCoverEquiv c)

projectionπ : (c : ShortCase) → GroupHom (K c) (G c)
projectionπ c = πHom 0 (fst , refl)

subgroupπ : (c : ShortCase) → GroupHom (K c) (Short.H c)
subgroupπ c = compGroupHom (πHom 0 (σ c , refl)) (encodeHom (Short.H c))

qCoverπ : (c : ShortCase)
  → GroupEquiv (Π OS.R (qCover c (a₀ c))) C₂ → GroupHom (K c) C₂
qCoverπ c rp = compGroupHom (πHom 0 (qCover c , refl)) (GroupEquiv→GroupHom rp)

abstract
  subgroupπ-loop : (c : ShortCase) (L : a₀ c ≡ a₀ c)
    → fst (subgroupπ c) ST.∣ L ∣₂ ≡ Cosets.loopCode (Short.H c) (cong (σ c) L)
  subgroupπ-loop c L = cong (fst (encodeHom (Short.H c))) (πHom-loop (σ c) (a₀ c) L)
    ∙ encodeHom-loop (Short.H c) (cong (σ c) L)

  classifier-class-lift : (c : ShortCase)
    (l : m₀ c ≡ m₀ c) (d : fst (Short.H c))
    → cong (Model.ρ-M c) l ≡ emloop (fst (Cosets.hom (Short.j c)) d)
    → Σ[ u ∈ fst (K c) ]
        (fst (projectionπ c) u ≡ ST.∣ l ∣₂) × (fst (subgroupπ c) u ≡ d)
  classifier-class-lift c l d eq = ST.∣ lifted .fst ∣₂ ,
    (πHom-loop fst (a₀ c) (lifted .fst) ∙ cong ST.∣_∣₂ (lifted .snd .fst)) ,
    (subgroupπ-loop c (lifted .fst)
      ∙ cong (Cosets.loopCode (Short.H c)) (lifted .snd .snd)
      ∙ Cosets.loopCode-loop (Short.H c) d)
    where
    lifted : Σ[ L ∈ (a₀ c ≡ a₀ c) ]
      (cong fst L ≡ l) × (cong (σ c) L ≡ emloop d)
    lifted = classifier-loop-lift c l d eq
