{-# OPTIONS --safe --cubical --guardedness --no-import-sorts --lossy-unification #-}
module DeloopS3.Bridge.Profile.OuterAdapters where

-- Orientation and source-map agreement for the geometric LES on the literal span.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (equivFun)
open import Cubical.Data.Sigma using (ΣPathP; Σ≡Prop)
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Bool using (Bool; false; true)
open import Cubical.Data.Int using (ℤ; pos)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group.Base using (Group₀)
open import Cubical.Algebra.Group.Morphisms using (GroupHom; GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties using
  (compGroupEquiv; isPropIsGroupHom)
open import Cubical.Algebra.Group.DirProd using (DirProd)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup; negEquivℤ)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using
  (CW₀; H̃ᶜʷ; finite≤→isCW)
open import DeloopS3.Bridge.FiniteDim using (pushout-finite≤)
open import DeloopS3.Bridge.DMCExactness.Geometric using
  (SpanSequenceData; actual-source)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging using
  (PushoutLES; finite-pushoutLES-merely)
open import DeloopS3.Bridge.Profile.Facts
import DeloopS3.Bridge.OriginalSpan as OS

private
  abstract
    -- The coordinate and its degree law share an abstract block so that
    -- the coordinate computes here, but never unfolds cellular homology.
    oriented-coordinate : (G : Group₀) → GroupEquiv G ℤGroup
      → Bool → GroupEquiv G ℤGroup
    oriented-coordinate G e false = e
    oriented-coordinate G e true =
      compGroupEquiv {F = G} {G = ℤGroup} {H = ℤGroup} e negEquivℤ

    oriented-degree : (G : Group₀) (e : GroupEquiv G ℤGroup)
      (b : Bool) (N : ℕ) (x : fst G) (y : ℤ)
      → y ≡ signedN b N Z.· equivFun {A = fst G} {B = ℤ} (fst e) x
      → y ≡ pos N Z.· equivFun {A = fst G} {B = ℤ}
          (fst (oriented-coordinate G e b)) x
    oriented-degree G e false N x y degree = degree
    oriented-degree G e true N x y degree = degree
      ∙ sym (Z.-DistL· (pos N) (equivFun (fst e) x))
      ∙ Z.-DistR· (pos N) (equivFun (fst e) x)

    -- All path algebra and homomorphism extensionality is done over
    -- neutral groups, not expanded cellular homology groups.
    group-hom-agrees : (G H : Group₀) (u v : GroupHom G H)
      (h : fst G → fst H)
      → ((x : fst G) → fst u x ≡ h x)
      → ((x : fst G) → fst v x ≡ h x)
      → u ≡ v
    group-hom-agrees G H u v h p q =
      Σ≡Prop (λ _ → isPropIsGroupHom G H)
        (funExt (λ x → p x ∙ sym (q x)))

abstract
  positive-source-coordinate : (facts : ProfileFacts) (c : ShortCase)
    → GroupEquiv (H̃ᶜʷ (ACW c) 3) ℤGroup
  positive-source-coordinate facts c = oriented-coordinate
    (H̃ᶜʷ (ACW c) 3) (ProfileFacts.A-H₃ facts c)
    (ProfileFacts.cover-sign facts c)

  positive-cover-degree : (facts : ProfileFacts) (c : ShortCase)
    (z : fst (H̃ᶜʷ (ACW c) 3))
    → equivFun {A = fst (H̃ᶜʷ (CCW c) 3)} {B = ℤ}
        (fst (ProfileFacts.C-H₃ facts c)) (fst (pH c 3) z)
      ≡ pos (OS.N c) Z.· equivFun {A = fst (H̃ᶜʷ (ACW c) 3)} {B = ℤ}
          (fst (positive-source-coordinate facts c)) z
  positive-cover-degree facts c z = oriented-degree
    (H̃ᶜʷ (ACW c) 3) (ProfileFacts.A-H₃ facts c)
    (ProfileFacts.cover-sign facts c) (OS.N c) z
    (equivFun {A = fst (H̃ᶜʷ (CCW c) 3)} {B = ℤ}
      (fst (ProfileFacts.C-H₃ facts c)) (fst (pH c 3) z))
    (ProfileFacts.cover-degree facts c z)

private
  -- The generated witness and XCW have literally the same underlying X.
  pushoutCW : ShortCase → CW₀
  pushoutCW c = OS.X c , finite≤→isCW
    (pushout-finite≤ (OS.q c) (OS.p c) 3 2 3
      (OS.A-finite c) OS.RP²-finite (OS.C-finite c))

  abstract
    pushoutCW-path : (c : ShortCase) → pushoutCW c ≡ XCW c
    pushoutCW-path c = ΣPathP
      (refl , PT.squash₁ (snd (pushoutCW c)) (snd (XCW c)))

abstract
  spanLES-merely : (c : ShortCase)
    → PT.∥ PushoutLES (ACW c) RCW (CCW c) (OS.q c) (OS.p c) (XCW c) ∥₁
  spanLES-merely c = PT.map
    {A = PushoutLES (ACW c) RCW (CCW c) (OS.q c) (OS.p c) (pushoutCW c)}
    {B = PushoutLES (ACW c) RCW (CCW c) (OS.q c) (OS.p c) (XCW c)}
    (subst {A = CW₀}
      (PushoutLES (ACW c) RCW (CCW c) (OS.q c) (OS.p c))
      (pushoutCW-path c))
    (finite-pushoutLES-merely (ACW c) RCW (CCW c) (OS.q c) (OS.p c)
      3 2 3 (OS.A-finite c) OS.RP²-finite (OS.C-finite c))

  -- The underlying pushout-identification path in les is left untouched.
  span-source-agrees : (c : ShortCase)
    (les : PushoutLES (ACW c) RCW (CCW c) (OS.q c) (OS.p c) (XCW c))
    (k : ℕ) → SpanSequenceData.source-map (snd les) (suc k) ≡ σ c k
  span-source-agrees c les k = group-hom-agrees
    (H̃ᶜʷ (ACW c) (suc k))
    (DirProd (H̃ᶜʷ RCW (suc k)) (H̃ᶜʷ (CCW c) (suc k)))
    (SpanSequenceData.source-map (snd les) (suc k)) (σ c k)
    (actual-source (ACW c) RCW (CCW c) (OS.q c) (OS.p c) (suc k))
    (SpanSequenceData.source-agrees (snd les) (suc k)) (σ-β c k)
