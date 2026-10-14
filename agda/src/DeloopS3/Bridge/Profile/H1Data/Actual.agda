{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Actual where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base using (inr)
import Cubical.HITs.Truncation as TR
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Group.Base using (πGr)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Abelianization.Base using (η)
open import Cubical.Algebra.Group.Abelianization.Properties using (AbelianizationGroup ; elimProp)
open import Cubical.Algebra.AbGroup
open import Cubical.CW.Homology.Base using (H̃ᶜʷAb)
open import DeloopS3.Bridge.Recognition.Notation
open import DeloopS3.Bridge.FiniteDim using (pushout-finite≤)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map)
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.Profile.OuterMV.Groups using (exact-right-surjective)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging using (finite-pushoutLES-merely)
open import DeloopS3.Bridge.Profile.H1Data.Hurewicz
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
import DeloopS3.Bridge.OriginalSpan as OS
import DeloopS3.Bridge.SpanPi1.Target as Pi
import DeloopS3.Bridge.SpanPi1.TargetAssembly as Assembly
open import DeloopS3.Bridge.ComponentHomology.Finite using (RP²CW)

ACW CCW XCW : ShortCase → CW₀
ACW c = OS.A c , finite≤→isCW (OS.A-finite c)
CCW c = OS.C c , finite≤→isCW (OS.C-finite c)
RCW : CW₀
RCW = RP²CW
XCW c = OS.X c , finite≤→isCW
  (pushout-finite≤ (OS.q c) (OS.p c) 3 2 3 (OS.A-finite c) OS.RP²-finite (OS.C-finite c))

abstract
  abelianization-contr : (G : Group₀) → isContr (fst G) → isContr (fst (AbelianizationGroup G))
  abelianization-contr G c = η (fst c) , elimProp G
    (λ _ → GroupStr.is-set (snd (AbelianizationGroup G)) _ _) (λ x → cong η (snd c x))

  simply-connected-H₁-zero-at : (X : CW₀)
    → isConnected 3 (fst X) → (x : fst X) → Hzero X 1
  simply-connected-H₁-zero-at X conn x = isOfHLevelRespectEquiv 0
    (fst (degree1-Hurewicz X (isConnectedSubtr' 1 2 conn) x))
    (abelianization-contr (πGr 0 (fst X , x))
      (isOfHLevelRetractFromIso 0 TR.setTruncTrunc2Iso (isConnectedPath 2 conn x x)))

  -- The actual original pushouts, independently of component H₁ coordinates.
  X-H₁-zero : (c : ShortCase) → Hzero (XCW c) 1
  X-H₁-zero c = simply-connected-H₁-zero-at (XCW c) (Pi.X-simple c) (Assembly.x₀ c)

signed-hom : (A B C : AbGroup ℓ-zero)
  → AbGroupHom A B → AbGroupHom A C
  → GroupHom (AbGroup→Group A) (DirProd (AbGroup→Group B) (AbGroup→Group C))
fst (signed-hom A B C f g) a = fst f a , AbGroupStr.-_ (snd C) (fst g a)
snd (signed-hom A B C f g) = makeIsGroupHom λ a b → ΣPathP
  (IsGroupHom.pres· (snd f) a b , IsGroupHom.pres· (snd (negGroupHom A C g)) a b)

outer-H₁-map : (c : ShortCase)
  → GroupHom (H̃ᶜʷ (ACW c) 1) (DirProd (H̃ᶜʷ RCW 1) (H̃ᶜʷ (CCW c) 1))
outer-H₁-map c = signed-hom (H̃ᶜʷAb (ACW c) 0) (H̃ᶜʷAb RCW 0) (H̃ᶜʷAb (CCW c) 0)
  (cellular-map (ACW c) RCW 1 (OS.q c)) (cellular-map (ACW c) (CCW c) 1 (OS.p c))

abstract
  -- This is (q_*,-p_*) of the LITERAL maps, not a model homomorphism.
  -- The simply-connected theorem already supplies the needed vanishing
  -- at the target of the outer MV source map.
  outer-H₁-onto : (c : ShortCase) → isSurjective (outer-H₁-map c)
  outer-H₁-onto c = PT.rec (isPropΠ (λ _ → PT.squash₁)) fromLES
    (finite-pushoutLES-merely (ACW c) RCW (CCW c) (OS.q c) (OS.p c)
      3 2 3 (OS.A-finite c) OS.RP²-finite (OS.C-finite c))
    where
    fromLES : GeometricPushoutLES (ACW c) RCW (CCW c) (OS.q c) (OS.p c) (XCW c)
      → isSurjective (outer-H₁-map c)
    fromLES les y = PT.map (λ { (x , e) → x , sym (Seq.source-agrees 1 x) ∙ e })
      (exact-right-surjective (Seq.source-map 1) (Seq.sum-map 1)
        (Seq.exact-target 1 (3 , refl)) (X-H₁-zero c) y)
      where
      module Seq = SpanSequenceData (snd les)
