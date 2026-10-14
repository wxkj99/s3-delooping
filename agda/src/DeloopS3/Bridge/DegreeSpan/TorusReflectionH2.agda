{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TorusReflectionH2 where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (invEq ; retEq ; secEq)
open import Cubical.Foundations.HLevels using (isGroupoidΣ)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc ; isContrFin1)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_ ; ΣPathP)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.HITs.Pushout using (Pushout ; cofib ; inl ; inr ; push)
open import Cubical.HITs.Wedge using (⋁↪)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop ; emloop-sym ; emsquash)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.CW.Map using (realiseCellMap)
open import Cubical.CW.Instances.SphereBouquetMap using (hasCWskelSphereBouquet/)
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T² ; mulC)
open import DeloopS3.Cover.Orientation.CircleModel using
  (circleToC ; CToCircle ; circle-retraction)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using
  (module RoseProduct ; torus-skeleton)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts using (module Chart)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts using
  (meridian-chart ; fibre-chart ; torus-chart)
open import DeloopS3.Bridge.Profile.BaseSeifert.BoundaryMarkedComparison using
  (original-torus-concrete)
open import DeloopS3.Bridge.DegreeSpan.ProjectH2Sparse using
  (cell-attaching ; cell-attachment)
open import DeloopS3.Bridge.DegreeSpan.ProjectH2Realization using
  (module CircleAttachment ; cell-inclusion)
import DeloopS3.Bridge.DegreeSpan.ReflectedAttachment as R
import DeloopS3.Bridge.DegreeSpan.TorusReflectionCell as RC
open import DeloopS3.Bridge.DegreeSpan.Coefficients using (module TorusMultiplier)

module RP = RoseProduct 1

r : T² → T²
r = TorusMultiplier.actual (negsuc 0)

r' : T² → T²
r' (u , t) = circleToC (R.reflection (CToCircle u)) , t

-- This comparison uses the actual circle loop, not a degree classification.
abstract
  circle-reflection-mul : (s : S¹)
    → circleToC (R.reflection s) ≡ mulC (negsuc 0) (circleToC s)
  circle-reflection-mul base = refl
  circle-reflection-mul (loop i) j = sym (emloop-sym ℤGroup (pos 1)) j i

  r'-r : r' ≡ r
  r'-r = funExt λ (u , t) → ΣPathP
    (circle-reflection-mul (CToCircle u)
      ∙ cong (mulC (negsuc 0)) (circle-retraction u) , refl)

private
  -- The ordering of the bouquet is fibre, then first factor.
  read-petal : Fin 2 → S¹ → T²
  read-petal (zero , _) s = 0C , circleToC s
  read-petal (suc zero , _) s = circleToC s , 0C
  read-petal (suc (suc n) , ()) s

  read-spoke : (k : Fin 2) → (0C , 0C) ≡ read-petal k base
  read-spoke (zero , _) = refl
  read-spoke (suc zero , _) = refl
  read-spoke (suc (suc n) , ())

  read : RC.B → T²
  read (inl tt) = 0C , 0C
  read (inr (k , s)) = read-petal k s
  read (push k i) = read-spoke k i

  product : Chart.Product 1 → T²
  product (a , b) = fst meridian-chart a , fst fibre-chart b

  abstract
    read-shift : (x : RP.Rose)
      → read (RC.shift x) ≡ (circleToC (pickPetal fzero x) , 0C)
    read-shift (inl tt) = refl
    read-shift (inr ((zero , tt) , s)) = refl
    read-shift (inr ((suc n , ()) , s))
    read-shift (push (zero , tt) i) = refl
    read-shift (push (suc n , ()) i)

    read-T : (w : RP.Wedge) → read (RC.T w) ≡ product (⋁↪ w)
    read-T (inl a) = read-shift (fst RP.suspension-chart a)
    read-T (inr b) = refl
    read-T (push tt i) = refl

    read-target : (w : RP.Wedge)
      → read (fst RP.target-chart w) ≡ product (⋁↪ w)
    read-target w = cong read (funExt⁻ RC.target-agrees w) ∙ read-T w

    lower-chart : (x : RC.B) → fst torus-chart (inr x) ≡ read x
    lower-chart x = cong product (Chart.on-edge 1 x)
      ∙ sym (read-target (invEq RP.target-chart x))
      ∙ cong read (secEq RP.target-chart x)

    read-reflection : (x : RC.B) → read (RC.L x) ≡ r (read x)
    read-reflection (inl tt) = refl
    read-reflection (inr ((zero , tt) , s)) =
      refl
    read-reflection (inr ((suc zero , tt) , s)) =
      ΣPathP (circle-reflection-mul s , refl)
    read-reflection (inr ((suc (suc n) , ()) , s))
    read-reflection (push (zero , tt) i) = refl
    read-reflection (push (suc zero , tt) i) = refl
    read-reflection (push (suc (suc n) , ()) i)

    lower-marked : (x : RC.B)
      → fst torus-chart (inr (RC.L x)) ≡ r (fst torus-chart (inr x))
    lower-marked x = lower-chart (RC.L x) ∙ read-reflection x
      ∙ sym (cong r (lower-chart x))

-- The attachment extension takes place in C × C, a groupoid.  Its centre
-- paths and circle-anchor coherence are supplied by CircleAttachment.
module RealizationStage where
  private
    F G : Pushout (cell-attaching 1) fst → T²
    F = fst torus-chart ∘ RC.reflectedTop ∘ invEq (cell-attachment 1)
    G = r ∘ fst torus-chart ∘ invEq (cell-attachment 1)

    abstract
      on-lower : (x : RC.B) → F (inl x) ≡ G (inl x)
      on-lower x =
        cong (fst torus-chart) (sym (RC.Stage.comm x))
        ∙ cong (fst torus-chart) (cell-inclusion 1 (RC.L x))
        ∙ lower-marked x
        ∙ sym (cong (r ∘ fst torus-chart) (cell-inclusion 1 x))

  abstract
    top-marked : (z : cofib RP.attaching)
      → fst torus-chart (RC.reflectedTop z) ≡ r (fst torus-chart z)
    top-marked z =
      sym (cong (fst torus-chart ∘ RC.reflectedTop) (retEq (cell-attachment 1) z))
      ∙ CircleAttachment.homotopy (cell-attaching 1)
          (isGroupoidΣ emsquash (λ _ → emsquash)) F G on-lower
          (fst (cell-attachment 1) z)
      ∙ cong (r ∘ fst torus-chart) (retEq (cell-attachment 1) z)

abstract
  reflected-marked-agreement :
    realiseCellMap RC.reflectedCellular ∘ fst (snd torus-skeleton)
      ≡ fst (snd torus-skeleton) ∘ r
  reflected-marked-agreement = funExt λ a →
    cong (realiseCellMap RC.reflectedCellular) (funExt⁻ original-torus-concrete a)
    ∙ RC.reflectedCellular-realise-top (invEq torus-chart a)
    ∙ cong (fst (snd (hasCWskelSphereBouquet/ RP.attaching)))
        (sym (retEq torus-chart (RC.reflectedTop (invEq torus-chart a)))
          ∙ cong (invEq torus-chart)
              (RealizationStage.top-marked (invEq torus-chart a)
                ∙ cong r (secEq torus-chart a)))
    ∙ sym (funExt⁻ original-torus-concrete (r a))

  reflected-marked-agreement' :
    realiseCellMap RC.reflectedCellular ∘ fst (snd torus-skeleton)
      ≡ fst (snd torus-skeleton) ∘ r'
  reflected-marked-agreement' = reflected-marked-agreement
    ∙ cong (λ f → fst (snd torus-skeleton) ∘ f) (sym r'-r)

open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using
  (ℤ[Fin_] ; ℤFinGenerator ; agreeOnℤFinGenerator→≡ ; isGeneratorℤFinGenerator')
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.SphereBouquet.Degree using (bouquetDegree)
open import Cubical.HITs.Sn.Degree using (degree)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology using
  (module TorusProduct ; torus-square-coordinate)
open import DeloopS3.Bridge.CellularPushout.Cellular using (cellular-coefficients)
import DeloopS3.Bridge.DegreeSpan.MarkedNaturality.Proof as Marked
open import DeloopS3.Bridge.DegreeSpan.TorusMultiplierH2 using (TorusMultiplierH₂Scalar)

negate-coefficients : GroupHom (AbGroup→Group ℤ[Fin 1 ]) (AbGroup→Group ℤ[Fin 1 ])
fst negate-coefficients v k = Z.- v k
snd negate-coefficients = makeIsGroupHom λ v w → funExt λ k → Z.-Dist+ (v k) (w k)

-- The unique generator controls the entire homomorphism, not just the
-- fundamental class.  Keep this algebra generic before using the actual CW.
abstract
  rank-one-negation : (q : SphereBouquet 2 (Fin 1) → SphereBouquet 2 (Fin 1))
    → degree 2 (λ s → pickPetal fzero (q (inr (fzero , s)))) ≡ negsuc 0
    → bouquetDegree q ≡ negate-coefficients
  rank-one-negation q sign = agreeOnℤFinGenerator→≡
    {ϕ = bouquetDegree q} {ψ = negate-coefficients}
    λ k → funExt λ b →
      sym (isGeneratorℤFinGenerator'
        (λ t → degree 2 (λ s → pickPetal b (q (inr (t , s))))) k)
      ∙ cong₂ (λ b' k' → degree 2 (λ s → pickPetal b' (q (inr (k' , s)))))
          (sym (snd isContrFin1 b)) (sym (snd isContrFin1 k))
      ∙ sign
      ∙ sym (cong Z.-_ (cong₂ ℤFinGenerator
          (sym (snd isContrFin1 k)) (sym (snd isContrFin1 b))))

  reflected-coefficients : cellular-coefficients RC.reflectedCellular 2
    ≡ negate-coefficients
  reflected-coefficients = rank-one-negation RC.actualBouquetQuotient
    RC.reflectedCellular-degree

  reflected-H₂-neg : (z : fst (H̃ᶜʷ torusCW 2))
    → torus-square-coordinate
        (fst (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2 r) z)
      ≡ Z.- torus-square-coordinate z
  reflected-H₂-neg z =
    cong (λ v → v fzero)
      (Marked.marked-square-coordinate-natural 1 1 torusCW torusCW
        (snd torus-skeleton) (snd torus-skeleton) r RC.reflectedCellular
        reflected-marked-agreement z)
    ∙ cong (λ (d : GroupHom (AbGroup→Group ℤ[Fin 1 ]) (AbGroup→Group ℤ[Fin 1 ]))
        → fst d (TorusProduct.square-coordinate z) fzero) reflected-coefficients

  torus-multiplier-H₂-neg : TorusMultiplierH₂Scalar (negsuc 0)
  torus-multiplier-H₂-neg = reflected-H₂-neg

  -- Exact circle-model reflection required by the boundary assembly.
  torus-reflection-H₂-neg : (z : fst (H̃ᶜʷ torusCW 2))
    → torus-square-coordinate
        (fst (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2 r') z)
      ≡ Z.- torus-square-coordinate z
  torus-reflection-H₂-neg z =
    cong (λ (f : T² → T²) → torus-square-coordinate
      (fst (H̃ᶜʷ→ {C = torusCW} {D = torusCW} 2 f) z)) r'-r
    ∙ reflected-H₂-neg z
