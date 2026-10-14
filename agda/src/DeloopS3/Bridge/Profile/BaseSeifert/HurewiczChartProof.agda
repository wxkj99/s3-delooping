{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.HurewiczChartProof where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
import Cubical.Data.Sum as Sum
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import Cubical.CW.Base using (CWskel ; hasCWskel ; realise)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ)
open import Cubical.CW.Instances.Sn using (Sˢᵏᵉˡ ; Sᶜʷ ; hasCWskelSphere)
open import Cubical.CW.Homology.Base using (H̃ˢᵏᵉˡ→ ; H̃ˢᵏᵉˡ→id)
open import Cubical.CW.Homology.Groups.Sn using (genHₙSⁿ)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.ComponentHomology.ChainTools using
  (chosen-skeleton ; chosen-skeleton-path)
open import DeloopS3.Bridge.ComponentHomology.Circle using
  (circleCW ; C-skeleton ; circle-H₁ ; circle-coordinate ; circle-cell-generator
  ; circle-cell-coordinate ; circle-generator ; circle-generator-is-cell)
open import DeloopS3.Bridge.DegreeSpan.WitnessTransport using
  (witness-comparison ; witness-comparison-action)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.LoopClass using
  (loop-class ; loop-natural)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C ; circleToC ; hC)
open import DeloopS3.Move.CancelMinimal using (C ; 0C)
open import DeloopS3.Move.CancelLoopCell using (circleMap)
open import DeloopS3.Bridge.ComponentHomology.Finite using (graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using (graph×circle-H₁)
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry using (fillingsCW)
open import DeloopS3.Bridge.Profile.BaseSeifert.Coordinates using
  (circles₂ ; module TwoCircles ; module ThreeCircles ; fillings-H₁
  ; fillings-H₁-on-components ; vertices-H₁ ; vertices-H₁-eval)
open import DeloopS3.Bridge.Profile.BaseSeifert.Functor using (map-square)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Generators using (int-ext)
import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Components as Components
import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Assembly as Assembly
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof using (module Actual)

open import DeloopS3.Bridge.SeifertChains.Matrices using (vertex₁)

open IsGroupHom using (pres1)

private
  abstract
    -- A repeated witness contributes no change of cellular coordinates.
    chosen-self : {A : Type} (s : hasCWskel A) (k : ℕ)
      (x : fst (H̃ˢᵏᵉˡ (fst s) k))
      → fst (fst (chosen-skeleton (A , PT.∣ s ∣₁) s k)) x ≡ x
    chosen-self {A} s k x =
      cong (λ e → fst (fst e) x) (chosen-skeleton-path (A , PT.∣ s ∣₁) s k)
      ∙ witness-comparison-action (A , PT.∣ s ∣₁) s k x
      ∙ cong (λ p → transport (λ i → fst (H̃ᶜʷ (A , p i) k)) x)
          (isProp→isSet PT.squash₁ PT.∣ s ∣₁ PT.∣ s ∣₁
            (PT.squash₁ PT.∣ s ∣₁ PT.∣ s ∣₁) refl)
      ∙ transportRefl x

    same-skeleton-image : (S : CWskel ℓ-zero) (A B : Type)
      (eA : A ≃ realise S) (eB : B ≃ realise S) (k : ℕ)
      (f : A → B)
      → (fst eB ∘ f ∘ invEq eA) ≡ (λ x → x)
      → (x : fst (H̃ˢᵏᵉˡ S k))
      → fst (cellular-map (A , PT.∣ S , eA ∣₁)
          (B , PT.∣ S , eB ∣₁) k f) x ≡ x
    same-skeleton-image S A B eA eB k f p x =
      cong (λ h → fst h x)
        (cellular-map-agrees (A , PT.∣ S , eA ∣₁)
          (B , PT.∣ S , eB ∣₁) k f)
      ∙ cong (λ g → fst (H̃ˢᵏᵉˡ→ {C = S} {D = S} k g) x) p
      ∙ cong (λ h → fst h x) (H̃ˢᵏᵉˡ→id k)

    positive-circle-map : circleMap hC ≡ circleToC
    positive-circle-map = funExt λ
      { base → refl
      ; (loop i) → refl }

    circle-realization-id :
      (fst (snd C-skeleton) ∘ circleToC ∘ invEq (snd (hasCWskelSphere 1)))
        ≡ (λ x → x)
    circle-realization-id = funExt λ x →
      cong (fst (snd (hasCWskelSphere 1)))
        (retEq S¹≃C (invEq (snd (hasCWskelSphere 1)) x))
      ∙ secEq (snd (hasCWskelSphere 1)) x

    circle-loop-raw : loop-class circleCW 0C hC ≡ genHₙSⁿ 0
    circle-loop-raw =
      cong (λ f → fst (cellular-map (Sᶜʷ 1) circleCW 1 f) (genHₙSⁿ 0))
        positive-circle-map
      ∙ same-skeleton-image (Sˢᵏᵉˡ 1) S¹ C
          (snd (hasCWskelSphere 1)) (snd C-skeleton) 1 circleToC
          circle-realization-id (genHₙSⁿ 0)

abstract
  circle-loop-is-cell : loop-class circleCW 0C hC ≡ circle-cell-generator
  circle-loop-is-cell =
    sym (retEq (fst (chosen-skeleton circleCW C-skeleton 1))
      (loop-class circleCW 0C hC))
    ∙ cong (invEq (fst (chosen-skeleton circleCW C-skeleton 1)))
        (chosen-self C-skeleton 1 (loop-class circleCW 0C hC) ∙ circle-loop-raw)

  circle-loop-coordinate : circle-coordinate (loop-class circleCW 0C hC) ≡ pos 1
  circle-loop-coordinate = cong circle-coordinate circle-loop-is-cell
    ∙ circle-cell-coordinate

  circle-loop-is-generator : loop-class circleCW 0C hC ≡ circle-generator
  circle-loop-is-generator = circle-loop-is-cell ∙ sym circle-generator-is-cell

  circle-generator-image : (X : CW₀) (f : C → fst X)
    → fst (cellular-map circleCW X 1 f) circle-generator
      ≡ loop-class X (f 0C) (cong f hC)
  circle-generator-image X f =
    cong (fst (cellular-map circleCW X 1 f)) (sym circle-loop-is-generator)
    ∙ loop-natural circleCW X f 0C hC

  circle-integer-coordinate : (n : ℤ)
    → circle-coordinate (fst Components.circle-integer n) ≡ n
  circle-integer-coordinate = int-ext ℤGroup
    (compGroupHom {F = ℤGroup} {G = H̃ᶜʷ circleCW 1} {H = ℤGroup}
      Components.circle-integer
      (GroupEquiv→GroupHom {G = H̃ᶜʷ circleCW 1} {H = ℤGroup} circle-H₁))
    (idGroupHom {G = ℤGroup}) circle-loop-coordinate

private
  -- Only the canonical sum beta and the unit laws are used here.
  module Merge (G H K : Group₀) (L : GroupHom G K) (R : GroupHom H K)
    (merge : fst G × fst H → fst K)
    (beta : (x : fst G) (y : fst H)
      → merge (x , y) ≡ GroupStr._·_ (snd K) (fst L x) (fst R y)) where
    abstract
      left : (x : fst G) → merge (x , GroupStr.1g (snd H)) ≡ fst L x
      left x = beta x (GroupStr.1g (snd H))
        ∙ cong (GroupStr._·_ (snd K) (fst L x)) (pres1 (snd R))
        ∙ GroupStr.·IdR (snd K) (fst L x)

      right : (y : fst H) → merge (GroupStr.1g (snd G) , y) ≡ fst R y
      right y = beta (GroupStr.1g (snd G)) y
        ∙ cong (λ x → GroupStr._·_ (snd K) x (fst R y)) (pres1 (snd L))
        ∙ GroupStr.·IdL (snd K) (fst R y)

  module TwoBeta = Merge (H̃ᶜʷ circleCW 1) (H̃ᶜʷ circleCW 1) (H̃ᶜʷ circles₂ 1)
    (cellular-map circleCW circles₂ 1 Sum.inl)
    (cellular-map circleCW circles₂ 1 Sum.inr)
    (equivFun (fst (TwoCircles.sum-equiv 0 (3 , refl))))
    (TwoCircles.sum-equiv-eval 0 (3 , refl))

  module ThreeBeta = Merge (H̃ᶜʷ circles₂ 1) (H̃ᶜʷ circleCW 1) (H̃ᶜʷ fillingsCW 1)
    (cellular-map circles₂ fillingsCW 1 Sum.inl)
    (cellular-map circleCW fillingsCW 1 Sum.inr)
    (equivFun (fst (ThreeCircles.sum-equiv 0 (3 , refl))))
    (ThreeCircles.sum-equiv-eval 0 (3 , refl))

  circle-zero : fst (H̃ᶜʷ circleCW 1)
  circle-zero = GroupStr.1g (snd (H̃ᶜʷ circleCW 1))

  merge-circles : (x y z : fst (H̃ᶜʷ circleCW 1)) → fst (H̃ᶜʷ fillingsCW 1)
  merge-circles x y z = equivFun (fst (ThreeCircles.sum-equiv 0 (3 , refl)))
    (equivFun (fst (TwoCircles.sum-equiv 0 (3 , refl))) (x , y) , z)

  abstract
    merge-circle-1 : (x : fst (H̃ᶜʷ circleCW 1))
      → merge-circles x circle-zero circle-zero
        ≡ fst (cellular-map circleCW fillingsCW 1 Components.c1) x
    merge-circle-1 x =
      ThreeBeta.left (equivFun (fst (TwoCircles.sum-equiv 0 (3 , refl))) (x , circle-zero))
      ∙ cong (fst (cellular-map circles₂ fillingsCW 1 Sum.inl)) (TwoBeta.left x)
      ∙ map-square circleCW circles₂ fillingsCW 1 Sum.inl Sum.inl Components.c1 refl x

    merge-circle-2 : (x : fst (H̃ᶜʷ circleCW 1))
      → merge-circles circle-zero x circle-zero
        ≡ fst (cellular-map circleCW fillingsCW 1 Components.c2) x
    merge-circle-2 x =
      ThreeBeta.left (equivFun (fst (TwoCircles.sum-equiv 0 (3 , refl))) (circle-zero , x))
      ∙ cong (fst (cellular-map circles₂ fillingsCW 1 Sum.inl)) (TwoBeta.right x)
      ∙ map-square circleCW circles₂ fillingsCW 1 Sum.inr Sum.inl Components.c2 refl x

    merge-circle-3 : (x : fst (H̃ᶜʷ circleCW 1))
      → merge-circles circle-zero circle-zero x
        ≡ fst (cellular-map circleCW fillingsCW 1 Components.c3) x
    merge-circle-3 x =
      cong (λ y → equivFun (fst (ThreeCircles.sum-equiv 0 (3 , refl))) (y , x))
        (TwoBeta.left circle-zero ∙ pres1 (snd (cellular-map circleCW circles₂ 1 Sum.inl)))
      ∙ ThreeBeta.right x

    circle-zero-coordinate : circle-coordinate circle-zero ≡ pos 0
    circle-zero-coordinate = pres1 (snd circle-H₁)

    graph-zero-coordinate :
      equivFun (fst graph×circle-H₁) (GroupStr.1g (snd (H̃ᶜʷ graph×circleCW 1)))
        ≡ (λ _ → pos 0)
    graph-zero-coordinate = pres1
      {A = fst (H̃ᶜʷ graph×circleCW 1)} {B = Fin 3 → ℤ}
      {M = snd (H̃ᶜʷ graph×circleCW 1)}
      {f = equivFun (fst graph×circle-H₁)}
      {N = snd (AbGroup→Group ℤ[Fin 3 ])} (snd graph×circle-H₁)

    filling-vertex-coordinate : (r : fst (H̃ᶜʷ fillingsCW 1))
      → equivFun (fst vertices-H₁) (GroupStr.1g (snd (H̃ᶜʷ graph×circleCW 1)) , r)
        ≡ ((pos 0 , pos 0) , pos 0 , equivFun (fst fillings-H₁) r)
    filling-vertex-coordinate r =
      vertices-H₁-eval (GroupStr.1g (snd (H̃ᶜʷ graph×circleCW 1))) r
      ∙ cong {A = Fin 3 → ℤ} {B = λ _ → fst vertex₁} (λ (f : Fin 3 → ℤ) →
          ((f (fsuc fzero) , f (fsuc (fsuc fzero))) , f fzero , equivFun (fst fillings-H₁) r))
          graph-zero-coordinate

abstract
  filling-inclusion-1 : (x : fst (H̃ᶜʷ circleCW 1))
    → equivFun (fst fillings-H₁) (fst (cellular-map circleCW fillingsCW 1 Components.c1) x)
      ≡ (circle-coordinate x , pos 0 , pos 0)
  filling-inclusion-1 x =
    cong {A = fst (H̃ᶜʷ fillingsCW 1)} {B = λ _ → ℤ × ℤ × ℤ}
      (equivFun (fst fillings-H₁)) (sym (merge-circle-1 x))
    ∙ fillings-H₁-on-components x circle-zero circle-zero
    ∙ (λ i → circle-coordinate x , circle-zero-coordinate i , circle-zero-coordinate i)

  filling-inclusion-2 : (x : fst (H̃ᶜʷ circleCW 1))
    → equivFun (fst fillings-H₁) (fst (cellular-map circleCW fillingsCW 1 Components.c2) x)
      ≡ (pos 0 , circle-coordinate x , pos 0)
  filling-inclusion-2 x =
    cong {A = fst (H̃ᶜʷ fillingsCW 1)} {B = λ _ → ℤ × ℤ × ℤ}
      (equivFun (fst fillings-H₁)) (sym (merge-circle-2 x))
    ∙ fillings-H₁-on-components circle-zero x circle-zero
    ∙ (λ i → circle-zero-coordinate i , circle-coordinate x , circle-zero-coordinate i)

  filling-inclusion-3 : (x : fst (H̃ᶜʷ circleCW 1))
    → equivFun (fst fillings-H₁) (fst (cellular-map circleCW fillingsCW 1 Components.c3) x)
      ≡ (pos 0 , pos 0 , circle-coordinate x)
  filling-inclusion-3 x =
    cong {A = fst (H̃ᶜʷ fillingsCW 1)} {B = λ _ → ℤ × ℤ × ℤ}
      (equivFun (fst fillings-H₁)) (sym (merge-circle-3 x))
    ∙ fillings-H₁-on-components circle-zero circle-zero x
    ∙ (λ i → circle-zero-coordinate i , circle-zero-coordinate i , circle-coordinate x)

  fillings-integer-1 : (n : ℤ)
    → equivFun (fst fillings-H₁) (fst Components.filling1-integer n) ≡ (n , pos 0 , pos 0)
  fillings-integer-1 n = filling-inclusion-1 (fst Components.circle-integer n)
    ∙ cong {A = ℤ} {B = λ _ → ℤ × ℤ × ℤ} (λ z → z , pos 0 , pos 0) (circle-integer-coordinate n)

  fillings-integer-2 : (n : ℤ)
    → equivFun (fst fillings-H₁) (fst Components.filling2-integer n) ≡ (pos 0 , n , pos 0)
  fillings-integer-2 n = filling-inclusion-2 (fst Components.circle-integer n)
    ∙ cong {A = ℤ} {B = λ _ → ℤ × ℤ × ℤ} (λ z → pos 0 , z , pos 0) (circle-integer-coordinate n)

  fillings-integer-3 : (n : ℤ)
    → equivFun (fst fillings-H₁) (fst Components.filling3-integer n) ≡ (pos 0 , pos 0 , n)
  fillings-integer-3 n = filling-inclusion-3 (fst Components.circle-integer n)
    ∙ cong {A = ℤ} {B = λ _ → ℤ × ℤ × ℤ} (λ z → pos 0 , pos 0 , z) (circle-integer-coordinate n)

  filling-1-coordinate : (n : ℤ)
    → fst Actual.filling-coordinate (fst Components.filling1-integer n) ≡ fst Assembly.ic1 n
  filling-1-coordinate n = filling-vertex-coordinate (fst Components.filling1-integer n)
    ∙ cong {A = ℤ × ℤ × ℤ} {B = λ _ → fst vertex₁} (λ (cs : ℤ × ℤ × ℤ) → (pos 0 , pos 0) , pos 0 , cs) (fillings-integer-1 n)

  filling-2-coordinate : (n : ℤ)
    → fst Actual.filling-coordinate (fst Components.filling2-integer n) ≡ fst Assembly.ic2 n
  filling-2-coordinate n = filling-vertex-coordinate (fst Components.filling2-integer n)
    ∙ cong {A = ℤ × ℤ × ℤ} {B = λ _ → fst vertex₁} (λ (cs : ℤ × ℤ × ℤ) → (pos 0 , pos 0) , pos 0 , cs) (fillings-integer-2 n)

  filling-3-coordinate : (n : ℤ)
    → fst Actual.filling-coordinate (fst Components.filling3-integer n) ≡ fst Assembly.ic3 n
  filling-3-coordinate n = filling-vertex-coordinate (fst Components.filling3-integer n)
    ∙ cong {A = ℤ × ℤ × ℤ} {B = λ _ → fst vertex₁} (λ (cs : ℤ × ℤ × ℤ) → (pos 0 , pos 0) , pos 0 , cs) (fillings-integer-3 n)
