{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Seifert.MarkedSeifert.WRelJR where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (pos)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop-comp)
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Move.CancelMinimal using (C; 0C; mulC)
open import DeloopS3.Cover.Orientation.CircleModel using (circleToC; S¹≃C; hC)
import DeloopS3.Seifert.MarkedSeifert.WEquiv as Checked
import DeloopS3.Seifert.MarkedSeifert.WInterface as Interface
import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Concrete as Concrete
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Cubical.HITs.Pushout.Base
open import DeloopS3.Move.CancelLoopCell using
  (module CircleUP; module PushoutUP; circleMap; powerEquiv; minus)
open import DeloopS3.Seifert.MarkedSeifert.WInterface using (W; RelJR; vertex; j; r; relation)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Edge using (WHit; double; LoopSquare)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.NielsenMapping using (module MappingJR)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Boundary using
  (squareToConjugate; conjugateSquare)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.HITEquiv using (RelJR≃Kinv)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus using (isGroupoidKinv)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary using
  (based; based-refl; based-comp; based-square)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.FilledLoops using
  (square-based; based-sym)

-- A parameter-free presentation has judgmentally trivial constant transport.
-- The adapter to the library's parameterized Pushout is constructorwise.
data Native : Type₀ where
  left right : S¹ → Native
  glue : (s : S¹) → left (double s) ≡ right (double s)

native : WHit → Native
native (inl s) = left s
native (inr s) = right s
native (push s i) = glue s i

unnative : Native → WHit
unnative (left s) = inl s
unnative (right s) = inr s
unnative (glue s i) = push s i

abstract
  native-section : native ∘ unnative ≡ idfun Native
  native-section k (left s) = left s
  native-section k (right s) = right s
  native-section k (glue s i) = glue s i

  native-retraction : unnative ∘ native ≡ idfun WHit
  native-retraction k (inl s) = inl s
  native-retraction k (inr s) = inr s
  native-retraction k (push s i) = push s i

  nativeEquiv : WHit ≃ Native
  nativeEquiv = isoToEquiv (iso native unnative
    (funExt⁻ native-section) (funExt⁻ native-retraction))

-- Perform the circle equivalences in the extension direction.
-- Their maps are then literal recursors, so doubling computes on the nose.
-- Insert the centre (a,refl) of the connecting-edge singleton, retaining its
-- entire square. Reindex y = j · r⁻¹. The resulting equivalence has as its
-- forward function the explicit extension below, so its computation does
-- not depend on a naturality identification for Edge.Mapping.WMapping.
module Extension where
  private
    X : Type₀
    X = Native
    ℓ : Level
    ℓ = ℓ-zero
  Loops : Type ℓ
  Loops = Σ[ a ∈ X ] (a ≡ a)

  XY : Type ℓ
  XY = Σ[ a ∈ X ] Σ[ x ∈ (a ≡ a) ] Σ[ y ∈ (a ≡ a) ]
    (x ∙ x ≡ y ∙ y)

  Edge : Type ℓ
  Edge = Σ[ ax ∈ Loops ] Σ[ by ∈ Loops ]
    Σ[ γ ∈ (ax .fst ≡ by .fst) ]
      LoopSquare (ax .snd ∙ ax .snd) (by .snd ∙ by .snd) γ

  EdgeFirst : Type ℓ
  EdgeFirst = Σ[ a ∈ X ] Σ[ x ∈ (a ≡ a) ]
    Σ[ bγ ∈ (Σ[ b ∈ X ] (a ≡ b)) ] Σ[ y ∈ (bγ .fst ≡ bγ .fst) ]
      LoopSquare (x ∙ x) (y ∙ y) (bγ .snd)

  circle : Loops → S¹ → X
  circle = CircleUP.extend (λ _ → X)

  extend : MappingJR.JRData X → WHit → X
  extend (a , p , q , s) (inl z) = circle (a , p) z
  extend (a , p , q , s) (inr z) = circle (a , p ∙ sym q) z
  extend (a , p , q , s) (push base i) = a
  extend (a , p , q , s) (push (loop k) i) = s i k

  abstract
    circleEquiv : Loops ≃ (S¹ → X)
    circleEquiv = invEquiv (CircleUP.circleUP (λ _ → X))

    seam : (ax by : Loops)
      → (Σ[ γ ∈ (ax .fst ≡ by .fst) ]
          LoopSquare (ax .snd ∙ ax .snd) (by .snd ∙ by .snd) γ)
      ≃ ((s : S¹) → circle ax (double s) ≡ circle by (double s))
    seam ax by = invEquiv
      (CircleUP.circleUP (λ s → circle ax (double s) ≡ circle by (double s)))

    edgeToCocone : Edge ≃ PushoutUP.Cocone double double X
    edgeToCocone = compEquiv
      (Σ-cong-equiv-snd λ ax → Σ-cong-equiv-snd λ by → seam ax by)
      (compEquiv
        (Σ-cong-equiv-snd λ ax → Σ-cong-equiv-fst
          {B = λ g → (s : S¹) → circle ax (double s) ≡ g (double s)} circleEquiv)
        (Σ-cong-equiv-fst
          {B = λ f → Σ[ g ∈ (S¹ → X) ] ((s : S¹) → f (double s) ≡ g (double s))}
          circleEquiv))

    reorder : EdgeFirst ≃ Edge
    reorder = isoToEquiv (iso
      (λ { (a , x , (b , γ) , y , s) → (a , x) , (b , y) , γ , s })
      (λ { ((a , x) , (b , y) , γ , s) → a , x , (b , γ) , y , s })
      (λ _ → refl) (λ _ → refl))

    insertEdge : XY ≃ EdgeFirst
    insertEdge = Σ-cong-equiv-snd λ a → Σ-cong-equiv-snd λ x →
      compEquiv
        (Σ-cong-equiv-snd λ y → isoToEquiv (iso
          (λ q i k → q k i) (λ q i k → q k i)
          (λ _ → refl) (λ _ → refl)))
        (invEquiv (Σ-contractFst (isContrSingl a)))

    nielsen : MappingJR.JRData X ≃ XY
    nielsen = Σ-cong-equiv-snd λ a → Σ-cong-equiv-snd λ p →
      Σ-cong-equiv-fst {B = λ y → p ∙ p ≡ y ∙ y}
        (compEquiv (powerEquiv a minus) (compPathlEquiv p))

    equivalence : MappingJR.JRData X ≃ (WHit → X)
    equivalence = compEquiv nielsen
      (compEquiv insertEdge (compEquiv reorder
        (compEquiv edgeToCocone (invEquiv (PushoutUP.pushoutUP double double X)))))

    computation : equivalence .fst ≡ extend
    computation k (a , p , q , s) (inl z) = circle (a , p) z
    computation k (a , p , q , s) (inr z) = circle (a , p ∙ sym q) z
    computation k (a , p , q , s) (push base i) = a
    computation k (a , p , q , s) (push (loop t) i) = s i t

    extensionEquiv : MappingJR.JRData X ≃ (WHit → X)
    extensionEquiv = extend , subst isEquiv computation (equivalence .snd)

    extension-map : extensionEquiv .fst ≡ extend
    extension-map = refl

-- Only ordinary HIT recursion is needed for the inverse. Its commutation
-- with the displayed extension is constructorwise, INCLUDING the 2-cell.
recJR : MappingJR.JRData Native → RelJR → Native
recJR (a , p , q , s) vertex = a
recJR (a , p , q , s) (j i) = p i
recJR (a , p , q , s) (r i) = q i
recJR (a , p , q , s) (relation i k) = s i k

hitToRel : WHit → RelJR
hitToRel (inl z) = circleMap j z
hitToRel (inr z) = circleMap (j ∙ sym r) z
hitToRel (push base i) = vertex
hitToRel (push (loop k) i) = relation i k

rec-extend : (d : MappingJR.JRData Native)
  → recJR d ∘ hitToRel ≡ Extension.extend d
rec-extend (a , p , q , s) = funExt hom
  where
  psq : Square {A = Native} refl refl p p
  psq i k = p i
  ysq : Square {A = Native} refl refl (p ∙ sym q) (p ∙ sym q)
  ysq i k = (p ∙ sym q) i
  cube : Cube (psq ∙v' psq) (ysq ∙v' ysq)
    (λ i k → a) (λ i k → a) s s
  cube = sym (∙v≡∙v' psq psq) ◁ (λ i t k → s i t)
    ▷ ∙v≡∙v' ysq ysq
  hom : (z : WHit) → recJR (a , p , q , s) (hitToRel z)
    ≡ Extension.extend (a , p , q , s) z
  hom (inl base) = refl
  hom (inl (loop i)) = refl
  hom (inr base) = refl
  hom (inr (loop i)) = refl
  hom (push base i) = refl
  hom (push (loop i) t) k = cube t i k

private
  inverseData : MappingJR.JRData Native
  inverseData = invEq Extension.extensionEquiv native

relToNative : RelJR → Native
relToNative = recJR inverseData

relToHit : RelJR → WHit
relToHit = unnative ∘ relToNative

abstract
  native-retract : relToNative ∘ hitToRel ≡ native
  native-retract = rec-extend inverseData
    ∙ sym (cong (λ f → f inverseData) Extension.extension-map)
    ∙ secEq Extension.extensionEquiv native

  hit-retraction : relToHit ∘ hitToRel ≡ idfun WHit
  hit-retraction = cong (unnative ∘_) native-retract ∙ native-retraction

  isGroupoidRelJR : isGroupoid RelJR
  isGroupoidRelJR = isOfHLevelRespectEquiv 3 (invEquiv RelJR≃Kinv) isGroupoidKinv

  isGroupoidWHit : isGroupoid WHit
  isGroupoidWHit = isGroupoidRetract hitToRel relToHit
    (funExt⁻ hit-retraction) isGroupoidRelJR

abstract
  isGroupoidNative : isGroupoid Native
  isGroupoidNative = isOfHLevelRespectEquiv 3 nativeEquiv isGroupoidWHit

-- Once groupoidness has been DERIVED from the retained-cell retraction,
-- the remaining homotopies need only their point, loop and base-seam data.
module GroupoidExt {ℓ : Level} (X : Type ℓ) (gpd : isGroupoid X) where
  pushoutExt : (f g : WHit → X)
    (hl : (s : S¹) → f (inl s) ≡ g (inl s))
    (hr : (s : S¹) → f (inr s) ≡ g (inr s))
    (seam₀ : PathP (λ i → f (push base i) ≡ g (push base i)) (hl base) (hr base))
    → f ≡ g
  pushoutExt f g hl hr seam₀ = funExt hom
    where
    Seam : S¹ → Type ℓ
    Seam s = PathP (λ i → f (push s i) ≡ g (push s i))
      (hl (double s)) (hr (double s))
    seamProp : (s : S¹) → isProp (Seam s)
    seamProp s = isOfHLevelPathP' 1 (gpd (f (push s i1)) (g (push s i1)))
      (hl (double s)) (hr (double s))
    seam : (s : S¹) → Seam s
    seam base = seam₀
    seam (loop i) = isProp→PathP (λ i → seamProp (loop i)) seam₀ seam₀ i
    hom : (z : WHit) → f z ≡ g z
    hom (inl s) = hl s
    hom (inr s) = hr s
    hom (push s i) = seam s i

  relExt : (f g : RelJR → X) (p : f vertex ≡ g vertex)
    (pj : PathP (λ i → f (j i) ≡ g (j i)) p p)
    (pr : PathP (λ i → f (r i) ≡ g (r i)) p p)
    → f ≡ g
  relExt f g p pj pr = funExt hom
    where
    B : RelJR → Type ℓ
    B z = f z ≡ g z
    jj : PathP (λ i → B ((j ∙ j) i)) p p
    jj = compPathP' {B = B} pj pj
    jr : PathP (λ i → B ((j ∙ sym r) i)) p p
    jr = compPathP' {B = B} pj (symP pr)
    jrjr : PathP (λ i → B (((j ∙ sym r) ∙ (j ∙ sym r)) i)) p p
    jrjr = compPathP' {B = B} jr jr
    cell : SquareP (λ i k → B (relation i k)) jj jrjr (λ _ → p) (λ _ → p)
    cell = isSet→SquareP (λ i k → gpd (f (relation i k)) (g (relation i k)))
      jj jrjr (λ _ → p) (λ _ → p)
    hom : (z : RelJR) → B z
    hom vertex = p
    hom (j i) = pj i
    hom (r i) = pr i
    hom (relation i k) = cell i k

private
  n₀ : Native
  n₀ = left base
  γ : left base ≡ right base
  γ = glue base
  xn : n₀ ≡ n₀
  xn = cong left loop
  yn : n₀ ≡ n₀
  yn = (γ ∙ cong right loop) ∙ sym γ
  rn : n₀ ≡ n₀
  rn = sym yn ∙ xn

  cancel-left : {ℓ : Level} {X : Type ℓ} {a : X} (p q : a ≡ a)
    → p ∙ (sym p ∙ q) ≡ q
  cancel-left p q = assoc p (sym p) q
    ∙ cong (_∙ q) (rCancel p) ∙ sym (lUnit q)
  cancel-right : {ℓ : Level} {X : Type ℓ} {a : X} (p q : a ≡ a)
    → (p ∙ sym q) ∙ q ≡ p
  cancel-right p q = sym (assoc p (sym q) q)
    ∙ cong (p ∙_) (lCancel q) ∙ sym (rUnit p)

  native-solved : xn ∙ sym rn ≡ yn
  native-solved = cong (xn ∙_) (symDistr (sym yn) xn) ∙ cancel-left xn yn

  native-relation : xn ∙ xn ≡ yn ∙ yn
  native-relation = sym (cong-∙ left loop loop)
    ∙ squareToConjugate (cong left (loop ∙ loop)) γ (cong right (loop ∙ loop))
      (λ i k → glue (loop i) k)
    ∙ cong (λ p → (γ ∙ p) ∙ sym γ) (cong-∙ right loop loop)
    ∙ conjugateSquare γ (cong right loop)

  explicitData : MappingJR.JRData Native
  explicitData = n₀ , xn , rn , native-relation
    ∙ cong₂ _∙_ (sym native-solved) (sym native-solved)

explicitInverse : RelJR → Native
explicitInverse = recJR explicitData

private
  forwardNative : Native → RelJR
  forwardNative = hitToRel ∘ unnative

  leftRet : (s : S¹) → explicitInverse (hitToRel (inl s)) ≡ native (inl s)
  leftRet base = refl
  leftRet (loop i) = refl

  rightSquare : Square γ γ (xn ∙ sym rn) (cong right loop)
  rightSquare = subst (λ p → Square γ γ p (cong right loop)) (sym native-solved)
    (compPath→Square
      (sym (assoc (γ ∙ cong right loop) (sym γ) γ)
        ∙ cong ((γ ∙ cong right loop) ∙_) (lCancel γ)
        ∙ sym (rUnit (γ ∙ cong right loop))))

  rightRet : (s : S¹) → explicitInverse (hitToRel (inr s)) ≡ native (inr s)
  rightRet base = γ
  rightRet (loop i) = rightSquare i

  native-y : cong forwardNative yn ≡ j ∙ sym r
  native-y = cong-∙ forwardNative (γ ∙ cong right loop) (sym γ)
    ∙ cong (_∙ refl) (cong-∙ forwardNative γ (cong right loop))
    ∙ cong (_∙ refl) (sym (lUnit (j ∙ sym r)))
    ∙ sym (rUnit (j ∙ sym r))

  inverse-r : cong (forwardNative ∘ explicitInverse) r ≡ r
  inverse-r = cong-∙ forwardNative (sym yn) xn
    ∙ cong (_∙ j) (cong sym native-y)
    ∙ cong (_∙ j) (symDistr j (sym r)) ∙ cancel-right r j

abstract
  explicit-retraction : explicitInverse ∘ hitToRel ≡ native
  explicit-retraction = GroupoidExt.pushoutExt Native isGroupoidNative
    (explicitInverse ∘ hitToRel) native leftRet rightRet (λ i k → γ (i ∧ k))

  explicit-section : forwardNative ∘ explicitInverse ≡ idfun RelJR
  explicit-section = GroupoidExt.relExt RelJR isGroupoidRelJR
    (forwardNative ∘ explicitInverse) (idfun RelJR) refl
    (λ i k → j i) (λ i k → inverse-r k i)

  hitEquiv : WHit ≃ RelJR
  hitEquiv = isoToEquiv (iso hitToRel (unnative ∘ explicitInverse)
    (funExt⁻ explicit-section)
    (funExt⁻ (cong (unnative ∘_) explicit-retraction ∙ native-retraction)))

  hitEquiv-map : hitEquiv .fst ≡ hitToRel
  hitEquiv-map = refl

-- Re-expose the standard circle-model equivalence with its actual vertex
-- and seam computations, so its inverse carries the requested markings.
private
  doublingTriangle : (s : S¹)
    → circleToC (double s) ≡ mulC (pos 2) (circleToC s)
  doublingTriangle base = refl
  doublingTriangle (loop i) k = (cong-∙ circleToC loop loop
    ∙ sym (emloop-comp ℤGroup (pos 1) (pos 1))) k i

  chartMap : WHit → W
  chartMap (inl s) = inl (circleToC s)
  chartMap (inr s) = inr (circleToC s)
  chartMap (push s i) =
    ((λ k → inl (doublingTriangle s k)) ∙∙ push (circleToC s)
      ∙∙ (λ k → inr (doublingTriangle s (~ k)))) i

  abstract
    chart : WHit ≃ W
    chart = pushoutEquiv double double (mulC (pos 2)) (mulC (pos 2))
      S¹≃C S¹≃C S¹≃C (funExt doublingTriangle) (funExt doublingTriangle)

    chart-map : chart .fst ≡ chartMap
    chart-map = funExt λ { (inl s) → refl ; (inr s) → refl ; (push s i) → refl }

    chart-ret : (z : WHit) → invEq chart (chartMap z) ≡ z
    chart-ret z = cong (invEq chart) (sym (funExt⁻ chart-map z)) ∙ retEq chart z

  aH : WHit
  aH = inl base
  γH : Path WHit (inl base) (inr base)
  γH = push base
  leftH rightH : S¹ → WHit
  leftH = inl
  rightH = inr
  xH yH : aH ≡ aH
  xH = cong leftH loop
  yH = (γH ∙ cong rightH loop) ∙ sym γH

  chart-seam : cong chartMap γH ≡ Checked.connecting
  chart-seam k i = doubleCompPath-filler refl Checked.connecting refl (~ k) i

  chart-y : cong chartMap yH ≡ Checked.yW
  chart-y = cong-∙ chartMap (γH ∙ cong rightH loop) (sym γH)
    ∙ cong₂ _∙_
      (cong-∙ chartMap γH (cong rightH loop)
        ∙ cong (_∙ cong Checked.rightCircle hC) chart-seam)
      (cong sym chart-seam)

  hit-y : cong hitToRel yH ≡ j ∙ sym r
  hit-y = cong-∙ hitToRel (γH ∙ cong rightH loop) (sym γH)
    ∙ cong (_∙ refl) (cong-∙ hitToRel γH (cong rightH loop))
    ∙ cong (_∙ refl) (sym (lUnit (j ∙ sym r)))
    ∙ sym (rUnit (j ∙ sym r))

WtoRelJR : W → RelJR
WtoRelJR = hitToRel ∘ invEq chart

private
  chart-hom : (z : WHit) → WtoRelJR (chartMap z) ≡ hitToRel z
  chart-hom z = cong hitToRel (chart-ret z)

abstract
  W≃RelJR : W ≃ RelJR
  W≃RelJR = WtoRelJR , subst isEquiv
    (cong (λ f → f ∘ invEq chart) hitEquiv-map)
    (compEquiv (invEquiv chart) hitEquiv .snd)

  W≃RelJR-map : W≃RelJR .fst ≡ WtoRelJR
  W≃RelJR-map = refl

  -- Exactly the parameter types of Concrete.CheckedFromNielsen.
  baseComparison : W≃RelJR .fst Checked.w₀ ≡ vertex
  baseComparison = chart-hom aH

  xComparison : based baseComparison (cong (W≃RelJR .fst) Checked.xW) ≡ j
  xComparison = square-based baseComparison
    (cong WtoRelJR Checked.xW) j (λ i k → chart-hom (xH i) k)

  yComparison : based baseComparison (cong (W≃RelJR .fst) Checked.yW) ≡ j ∙ sym r
  yComparison = cong (based baseComparison ∘ cong WtoRelJR) (sym chart-y)
    ∙ square-based baseComparison (cong (WtoRelJR ∘ chartMap) yH)
        (cong hitToRel yH) (λ i k → chart-hom (yH i) k)
    ∙ hit-y

module WComparisonInstance = Concrete.CheckedFromNielsen
  W≃RelJR baseComparison xComparison yComparison

-- Retains bW, thirdStaged, and all three boundary fields.
WComparison-checked : Interface.WComparison Checked.M22e
WComparison-checked = WComparisonInstance.markedW
