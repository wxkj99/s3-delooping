{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cover.CircleOrbit where

-- Circle-orbit covers. Orbit inputs below are algebraic;
-- neither a cover equivalence nor a boundary naturality theorem is input.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc; snotz)
import Cubical.Data.Nat as N
open import Cubical.Data.Int using (ℤ; pos; negsuc)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Nat.Mod using (<→mod≡id)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗ→<; isProp<ᵗ)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·; rUnitℤ·ℤ)
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Algebra.Group.Base hiding (group)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom; compGroupHom)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup; ℤHom)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_; ℤ→Fin; isHomℤ→Fin)
open import Cubical.Algebra.SymmetricGroup using (SymGroup)
open import Cubical.HITs.EilenbergMacLane1.Base
import Cubical.HITs.EilenbergMacLane1.Properties as EM
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.S1 as S1
open import DeloopS3.Groups.Bmap
open import DeloopS3.Cover.Cosets
import DeloopS3.Cover.DoubleCoset as DC
open DC using (module TotalFaithful)

-- The oriented circle model used for the boundary calculation.
Circle : Type₀
Circle = EM₁ ℤGroup

degree : ℕ → Circle → Circle
degree l = Bmap (ℤHom (pos l))

degree-loop : (l : ℕ) (k : ℤ)
  → cong (degree l) (emloop k) ≡ emloop (pos l Z.· k)
degree-loop l k = refl

positiveMultiple : (l : ℕ) → SubgroupEmbedding ℤGroup ℤGroup
hom (positiveMultiple l) = ℤHom (pos (suc l))
mono (positiveMultiple l) {x} {y} p =
  Z.·lCancel (pos (suc l)) x y p (λ e → snotz (Z.injPos e))

residue : (n : ℕ) → GroupHom ℤGroup (ℤGroup/ suc n)
residue n = ℤ→Fin n , isHomℤ→Fin n

-- A set-valued cover is faithful on paths: the second-coordinate path
-- lies in a set, so any specified square in the base lifts uniquely.
cover-path-ext : {B : Type₀} (F : B → hSet ℓ-zero)
  {u v : Σ[ b ∈ B ] F b .fst} (p q : u ≡ v)
  → cong fst p ≡ cong fst q → p ≡ q
cover-path-ext F p q = ΣSquareSet (λ b → F b .snd)

-- This is the set-family version of the full-faithfulness argument in
-- DoubleCoset. It applies both to C_n and to its inverse image in ℤ.
record OrbitCoverData (C : Group₀) (F : EM₁ C → hSet ℓ-zero) : Type₁ where
  field
    Reps : Type₀
    reps-set : isSet Reps
    start : Reps → F embase .fst
    Stabilizer : Reps → Group₀
    inclusion : (r : Reps) → SubgroupEmbedding (Stabilizer r) C
    fixes : (r : Reps) (k : Stabilizer r .fst)
      → subst (λ b → F b .fst) (emloop (hom (inclusion r) .fst k)) (start r) ≡ start r
    full : (r : Reps) (c : C .fst)
      → subst (λ b → F b .fst) (emloop c) (start r) ≡ start r
      → Σ[ k ∈ Stabilizer r .fst ] hom (inclusion r) .fst k ≡ c
    disjoint : (r s : Reps) (c : C .fst)
      → subst (λ b → F b .fst) (emloop c) (start r) ≡ start s → r ≡ s
    complete : (x : F embase .fst)
      → PT.∥ Σ[ r ∈ Reps ] Σ[ c ∈ C .fst ]
          subst (λ b → F b .fst) (emloop c) (start r) ≡ x ∥₁

module OrbitComparison (C : Group₀) (F : EM₁ C → hSet ℓ-zero)
  (D : OrbitCoverData C F) where
  open OrbitCoverData D

  Source : Type₀
  Source = Σ[ r ∈ Reps ] EM₁ (Stabilizer r)
  Target : Type₀
  Target = Σ[ b ∈ EM₁ C ] F b .fst

  liftSection : (r : Reps) (z : EM₁ (Stabilizer r))
    → F (Bmap (hom (inclusion r)) z) .fst
  liftSection r = EM.elimSet (Stabilizer r)
    (λ z → F (Bmap (hom (inclusion r)) z) .snd)
    (start r) (λ k → toPathP (fixes r k))

  component : (r : Reps) → EM₁ (Stabilizer r) → Target
  component r z = Bmap (hom (inclusion r)) z , liftSection r z
  comparison : Source → Target
  comparison (r , z) = component r z
  projection : Source → EM₁ C
  projection (r , z) = Bmap (hom (inclusion r)) z

  faithful : {u v : Source} (p q : u ≡ v)
    → cong comparison p ≡ cong comparison q → p ≡ q
  faithful p q e = TotalFaithful.inject reps-set
    (λ r → Bmap (hom (inclusion r)))
    (λ r a b → isEmbedding→Inj (Bmap-faithful (inclusion r) _ _) a b)
    p q (cong (cong fst) e)

  path-action : (r s : Reps)
    (p : comparison (r , embase) ≡ comparison (s , embase))
    → subst (λ b → F b .fst) (emloop (loopCode C (cong fst p))) (start r) ≡ start s
  path-action r s p =
    cong (λ q → subst (λ b → F b .fst) q (start r)) (loop-codeLoop C (cong fst p))
    ∙ fromPathP (λ i → p i .snd)

  same-base-lift : (r : Reps)
    (p : comparison (r , embase) ≡ comparison (r , embase))
    → fiber (cong {x = (r , embase)} {y = (r , embase)} comparison) p
  same-base-lift r p = cong (r ,_) (emloop (w .fst)) ,
    cover-path-ext F _ p (cong emloop (w .snd) ∙ loop-codeLoop C (cong fst p))
    where w = full r (loopCode C (cong fst p)) (path-action r r p)

  lift-along : (r s : Reps) → r ≡ s
    → (p : comparison (r , embase) ≡ comparison (s , embase))
    → fiber (cong {x = (r , embase)} {y = (s , embase)} comparison) p
  lift-along r s e = J
    (λ s e → (p : comparison (r , embase) ≡ comparison (s , embase))
      → fiber (cong {x = (r , embase)} {y = (s , embase)} comparison) p)
    (same-base-lift r) e

  base-lift : (r s : Reps)
    (p : comparison (r , embase) ≡ comparison (s , embase))
    → fiber (cong {x = (r , embase)} {y = (s , embase)} comparison) p
  base-lift r s p = lift-along r s
    (disjoint r s (loopCode C (cong fst p)) (path-action r s p)) p

  base-equiv : (r s : Reps)
    → isEquiv (cong {x = (r , embase)} {y = (s , embase)} comparison)
  base-equiv r s = isoToIsEquiv (iso (cong comparison)
    (λ p → base-lift r s p .fst) (λ p → base-lift r s p .snd)
    (λ q → faithful _ q (base-lift r s (cong comparison q) .snd)))

  fully-faithful : isEmbedding comparison
  fully-faithful (r , x) (s , y) = EM.elimProp (Stabilizer r)
    {B = λ x → (y : EM₁ (Stabilizer s))
      → isEquiv (cong {x = (r , x)} {y = (s , y)} comparison)}
    (λ _ → isPropΠ λ _ → isPropIsEquiv _)
    (EM.elimProp (Stabilizer s) (λ _ → isPropIsEquiv _) (base-equiv r s)) x y

  base-surjective : (x : F embase .fst) → PT.∥ fiber comparison (embase , x) ∥₁
  base-surjective x = PT.rec PT.squash₁
    (λ (r , c , p) → PT.∣ (r , embase) ,
      (λ i → emloop c i , toPathP {A = λ j → F (emloop c j) .fst}
        {x = start r} {y = x} p i) ∣₁)
    (complete x)

  surjective : isSurjection comparison
  surjective (b , x) = EM.elimProp C
    {B = λ b → (x : F b .fst) → PT.∥ fiber comparison (b , x) ∥₁}
    (λ _ → isPropΠ λ _ → PT.squash₁) base-surjective b x

  equivalence : Source ≃ Target
  equivalence = comparison , isEmbedding×isSurjection→isEquiv (fully-faithful , surjective)

-- Right actions, matching compEquiv and Cosets.fiber-transport: first c,
-- then d. In particular no inverse is inserted in the positive generator.
module ActionFamily {X : Type₀} (setX : isSet X) (C : Group₀)
  (a : GroupHom C (SymGroup X setX)) where
  actionPath : (c : C .fst) → Path (hSet ℓ-zero) (X , setX) (X , setX)
  actionPath c = TypeOfHLevel≡ 2 (ua (a .fst c))

  family : EM₁ C → hSet ℓ-zero
  family = EM.rec' C (isOfHLevelTypeOfHLevel 2) (X , setX) actionPath
    (λ c d → ΣSquareSet (λ _ → isProp→isSet isPropIsSet)
      (cong ua (IsGroupHom.pres· (a .snd) c d)
       ∙ uaCompEquiv (a .fst c) (a .fst d)
       ∙ sym (cong-∙ fst (actionPath c) (actionPath d))))

  transport-action : (c : C .fst) (x : X)
    → subst (λ b → family b .fst) (emloop c) x ≡ a .fst c .fst x
  transport-action c x = uaβ (a .fst c) x

record FinitePermutation (X : Type₀) : Type₀ where
  field
    size : ℕ
    enumerate : X ≃ Fin size
    setX : isSet X
    permutation : X ≃ X

-- A period (not necessarily the least global period) and specified orbit
-- data. fixed-full says EXACTLY that the ℤ-stabilizer is lℤ. This is a
-- set-level certificate, not a topological input. Both l and d are positive.
record CyclicOrbitData {X : Type₀} (α : FinitePermutation X) : Type₁ where
  open FinitePermutation α
  field
    modulus-1 : ℕ
  Cn : Group₀
  Cn = ℤGroup/ suc modulus-1
  field
    action : GroupHom Cn (SymGroup X setX)
    generator-action : action .fst (residue modulus-1 .fst (pos 1)) ≡ permutation
    Rep : Type₀
    rep-set : isSet Rep
    repr : Rep → X
    length-1 order-1 : Rep → ℕ
    factor : (r : Rep) → suc modulus-1 ≡ suc (length-1 r) N.· suc (order-1 r)
  act : ℤ → X → X
  act k = action .fst (residue modulus-1 .fst k) .fst
  length : Rep → ℕ
  length r = suc (length-1 r)
  field
    fixed-multiple : (r : Rep) (k : ℤ) → act (pos (length r) Z.· k) (repr r) ≡ repr r
    fixed-full : (r : Rep) (k : ℤ) → act k (repr r) ≡ repr r
      → Σ[ m ∈ ℤ ] pos (length r) Z.· m ≡ k
    separate : (r s : Rep) (k : ℤ) → act k (repr r) ≡ repr s → r ≡ s
    cover : (x : X) → PT.∥ Σ[ r ∈ Rep ] Σ[ k ∈ ℤ ] act k (repr r) ≡ x ∥₁

residue-section : (n : ℕ) (c : (ℤGroup/ suc n) .fst)
  → residue n .fst (pos (c .fst)) ≡ c
residue-section n (c , bound) = Σ≡Prop (λ k → isProp<ᵗ {n = k} {m = suc n})
  (<→mod≡id c (suc n) (<ᵗ→< bound))

residue-power : (n : ℕ) (k : ℤ)
  → residue n .fst k ≡ k ℤ[ ℤGroup/ suc n ]· (residue n .fst (pos 1))
residue-power n k = cong (residue n .fst) (sym (rUnitℤ·ℤ k))
  ∙ homPresℤ· (residue n) (pos 1) k

module CircleConstruction {X : Type₀} (α : FinitePermutation X)
  (R : CyclicOrbitData α) where
  open FinitePermutation α
  open CyclicOrbitData R
  module A = ActionFamily setX Cn action
  private
    module C = GroupStr (Cn .snd)
    q = residue modulus-1

  finiteFamily : EM₁ Cn → hSet ℓ-zero
  finiteFamily = A.family
  circleToCyclic : Circle → EM₁ Cn
  circleToCyclic = Bmap q
  circleFamily : Circle → hSet ℓ-zero
  circleFamily z = finiteFamily (circleToCyclic z)

  -- The total space of the pullback family, not a postulated cover model.
  CircleCover : Type₀
  CircleCover = Σ[ z ∈ Circle ] circleFamily z .fst
  CyclicCover : Type₀
  CyclicCover = Σ[ b ∈ EM₁ Cn ] finiteFamily b .fst
  toCyclicCover : CircleCover → CyclicCover
  toCyclicCover (z , x) = circleToCyclic z , x

  -- The actual finite stabilizer subgroup, with its inclusion into C_n.
  module Stabilizer (r : Rep) where
    Carrier : Type₀
    Carrier = Σ[ c ∈ Cn .fst ] action .fst c .fst (repr r) ≡ repr r
    ext : {u v : Carrier} → u .fst ≡ v .fst → u ≡ v
    ext = Σ≡Prop (λ _ → setX _ _)
    unit : Carrier
    unit = C.1g , cong (λ e → e .fst (repr r)) (IsGroupHom.pres1 (action .snd))
    product : Carrier → Carrier → Carrier
    product (c , p) (d , t) = (c C.· d) ,
      cong (λ e → e .fst (repr r)) (IsGroupHom.pres· (action .snd) c d)
      ∙ cong (action .fst d .fst) p ∙ t
    inverse : Carrier → Carrier
    inverse (c , p) = C.inv c ,
      cong (λ e → e .fst (repr r)) (IsGroupHom.presinv (action .snd) c)
      ∙ cong (invEq (action .fst c)) (sym p) ∙ retEq (action .fst c) (repr r)
    group : Group₀
    group = makeGroup-right unit product inverse
      (isSetΣ C.is-set (λ _ → isProp→isSet (setX _ _)))
      (λ u v w → ext (C.·Assoc (u .fst) (v .fst) (w .fst)))
      (λ u → ext (C.·IdR (u .fst)))
      (λ u → ext (C.·InvR (u .fst)))
    inclusion : SubgroupEmbedding group Cn
    hom inclusion = fst , makeIsGroupHom (λ _ _ → refl)
    mono inclusion = ext

    -- This is the marked boundary map ℤ → Stab, not an arbitrary choice
    -- of generator of a cyclic group of the right order.
    boundaryHom : GroupHom ℤGroup group
    boundaryHom .fst k = q .fst (pos (length r) Z.· k) , fixed-multiple r k
    boundaryHom .snd = makeIsGroupHom (λ k l → ext
      (IsGroupHom.pres· (compGroupHom (ℤHom (pos (length r))) q .snd) k l))

    generator : Carrier
    generator = boundaryHom .fst (pos 1)
    generator-mark : generator .fst ≡ q .fst (pos (length r))
    generator-mark = cong (q .fst) (Z.·IdR (pos (length r)))
    generator-power : generator .fst
      ≡ pos (length r) ℤ[ Cn ]· (q .fst (pos 1))
    generator-power = generator-mark ∙ residue-power modulus-1 (pos (length r))

    generated : (s : Carrier) → Σ[ k ∈ ℤ ] boundaryHom .fst k ≡ s
    generated (c , p) = w .fst , ext
      (cong (q .fst) (w .snd) ∙ residue-section modulus-1 c)
      where
      w = fixed-full r (pos (c .fst))
        (cong (λ d → action .fst d .fst (repr r)) (residue-section modulus-1 c) ∙ p)

    generator-powers : (k : ℤ) → boundaryHom .fst k ≡ k ℤ[ group ]· generator
    generator-powers k = cong (boundaryHom .fst) (sym (rUnitℤ·ℤ k))
      ∙ homPresℤ· boundaryHom (pos 1) k

    generated-by-generator : (s : Carrier) → Σ[ k ∈ ℤ ] (k ℤ[ group ]· generator) ≡ s
    generated-by-generator s = w .fst , sym (generator-powers (w .fst)) ∙ w .snd
      where w = generated s

  integerOrbits : OrbitCoverData ℤGroup circleFamily
  OrbitCoverData.Reps integerOrbits = Rep
  OrbitCoverData.reps-set integerOrbits = rep-set
  OrbitCoverData.start integerOrbits = repr
  OrbitCoverData.Stabilizer integerOrbits r = ℤGroup
  OrbitCoverData.inclusion integerOrbits r = positiveMultiple (length-1 r)
  OrbitCoverData.fixes integerOrbits r k =
    A.transport-action (q .fst (pos (length r) Z.· k)) (repr r) ∙ fixed-multiple r k
  OrbitCoverData.full integerOrbits r k p = fixed-full r k
    (sym (A.transport-action (q .fst k) (repr r)) ∙ p)
  OrbitCoverData.disjoint integerOrbits r s k p = separate r s k
    (sym (A.transport-action (q .fst k) (repr r)) ∙ p)
  OrbitCoverData.complete integerOrbits x = PT.map
    (λ (r , k , p) → r , k , A.transport-action (q .fst k) (repr r) ∙ p) (cover x)

  finiteOrbits : OrbitCoverData Cn finiteFamily
  OrbitCoverData.Reps finiteOrbits = Rep
  OrbitCoverData.reps-set finiteOrbits = rep-set
  OrbitCoverData.start finiteOrbits = repr
  OrbitCoverData.Stabilizer finiteOrbits = Stabilizer.group
  OrbitCoverData.inclusion finiteOrbits = Stabilizer.inclusion
  OrbitCoverData.fixes finiteOrbits r (c , p) = A.transport-action c (repr r) ∙ p
  OrbitCoverData.full finiteOrbits r c p =
    (c , sym (A.transport-action c (repr r)) ∙ p) , refl
  OrbitCoverData.disjoint finiteOrbits r s c p = separate r s (pos (c .fst))
    (cong (λ d → action .fst d .fst (repr r)) (residue-section modulus-1 c)
     ∙ sym (A.transport-action c (repr r)) ∙ p)
  OrbitCoverData.complete finiteOrbits x = PT.map
    (λ (r , k , p) → r , q .fst k , A.transport-action (q .fst k) (repr r) ∙ p) (cover x)

  module CircleOrbits = OrbitComparison ℤGroup circleFamily integerOrbits
  module FiniteOrbits = OrbitComparison Cn finiteFamily finiteOrbits

  boundary : CircleOrbits.Source → FiniteOrbits.Source
  boundary (r , z) = r , Bmap (Stabilizer.boundaryHom r) z

  -- Naturality with the ACTUAL finite stabilizer decomposition. The
  -- projected loops agree definitionally; the remaining square is in a
  -- set fibre. Thus the homotopy also retains the positive marking.
  boundary-naturality : (u : CircleOrbits.Source)
    → toCyclicCover (CircleOrbits.comparison u)
      ≡ FiniteOrbits.comparison (boundary u)
  boundary-naturality (r , z) = EM.elimSet ℤGroup
    {B = λ z → toCyclicCover (CircleOrbits.comparison (r , z))
      ≡ FiniteOrbits.comparison (boundary (r , z))}
    (λ _ → isGroupoidΣ emsquash (λ b → isSet→isGroupoid (finiteFamily b .snd)) _ _)
    refl (λ k → ΣSquareSet (λ b → finiteFamily b .snd)
      (λ i j → emloop (q .fst (pos (length r) Z.· k)) i)) z

-- Keep the packaging generic, so checking its fields does not normalize
-- the concrete cyclic action or the stabilizer group laws.
record MarkedCoverComparison {S T V W B C : Type₀}
  (p : S → B) (q : T → B) (m : S → V) (n : T → W)
  (u : V → C) (v : W → C) : Type₀ where
  field
    e : S ≃ T
    projection : (s : S) → q (e .fst s) ≡ p s
    finite-e : V ≃ W
    finite-projection : (z : V) → v (finite-e .fst z) ≡ u z
    component-compatible : (s : S) → n (e .fst s) ≡ finite-e .fst (m s)

CircleCoverComparison : {X : Type₀} (α : FinitePermutation X)
  → CyclicOrbitData α → Type₀
CircleCoverComparison α R = MarkedCoverComparison
  M.CircleOrbits.projection fst M.boundary M.toCyclicCover
  M.FiniteOrbits.projection fst
  where module M = CircleConstruction α R

circleOrbitCover : {X : Type₀} (α : FinitePermutation X)
  → (R : CyclicOrbitData α) → CircleCoverComparison α R
MarkedCoverComparison.e (circleOrbitCover α R) = M.CircleOrbits.equivalence
  where module M = CircleConstruction α R
MarkedCoverComparison.projection (circleOrbitCover α R) s = refl
MarkedCoverComparison.finite-e (circleOrbitCover α R) = M.FiniteOrbits.equivalence
  where module M = CircleConstruction α R
MarkedCoverComparison.finite-projection (circleOrbitCover α R) u = refl
MarkedCoverComparison.component-compatible (circleOrbitCover α R) = M.boundary-naturality
  where module M = CircleConstruction α R

-- The equivalence is oriented: the HIT loop goes to emloop (+1).
HIT→Circle : S1.S¹ → Circle
HIT→Circle = S1.rec embase (emloop (pos 1))
Circle→HIT : Circle → S1.S¹
Circle→HIT = EM.rec' ℤGroup S1.isGroupoidS¹ S1.base S1.intLoop
  (λ k l → sym (S1.intLoop-hom k l))

HIT→Circle-intLoop : (k : ℤ) → cong HIT→Circle (S1.intLoop k) ≡ emloop k
HIT→Circle-intLoop (pos zero) = sym (emloop-1g ℤGroup)
HIT→Circle-intLoop (pos (suc n)) = cong-∙ HIT→Circle (S1.intLoop (pos n)) S1.loop
  ∙ cong (_∙ emloop (pos 1)) (HIT→Circle-intLoop (pos n))
  ∙ sym (emloop-comp ℤGroup (pos n) (pos 1))
HIT→Circle-intLoop (negsuc zero) = sym (emloop-sym ℤGroup (pos 1))
HIT→Circle-intLoop (negsuc (suc n)) =
  cong-∙ HIT→Circle (S1.intLoop (negsuc n)) (sym S1.loop)
  ∙ cong₂ _∙_ (HIT→Circle-intLoop (negsuc n)) (HIT→Circle-intLoop (negsuc zero))
  ∙ sym (emloop-comp ℤGroup (negsuc n) (negsuc zero))

HIT-circle-ret : (x : S1.S¹) → Circle→HIT (HIT→Circle x) ≡ x
HIT-circle-ret S1.base = refl
HIT-circle-ret (S1.loop i) j = sym (lUnit S1.loop) j i

HIT-circle-sec : (z : Circle) → HIT→Circle (Circle→HIT z) ≡ z
HIT-circle-sec = EM.elimSet ℤGroup
  {B = λ z → HIT→Circle (Circle→HIT z) ≡ z}
  (λ _ → emsquash _ _) refl (λ k i j → HIT→Circle-intLoop k j i)

S¹≃Circle : S1.S¹ ≃ Circle
S¹≃Circle = isoToEquiv (iso HIT→Circle Circle→HIT HIT-circle-sec HIT-circle-ret)

positive-degree : (l : ℕ) → cong (degree l ∘ HIT→Circle) S1.loop ≡ emloop (pos l)
positive-degree l = cong emloop (Z.·IdR (pos l))

-- Specialization to the double-coset decomposition. This adapter preserves
-- its representatives, both subgroup maps, and the specified BG seam.
module DoubleCosetCircles {H G : Group₀} (n : ℕ)
  (j : SubgroupEmbedding H G)
  (i : SubgroupEmbedding (ℤGroup/ suc n) G)
  (D : DC.DoubleCosetData j i) where
  private
    Cn = ℤGroup/ suc n
    module G = GroupStr (G .snd)
    module D = DC.DoubleCosetData D
    module P = DC.ComparisonMap j i D
    module Cos = RightCosets j
    q = residue n

  F : EM₁ Cn → hSet ℓ-zero
  F b = CosetFamily j (Bmap (hom i) b)

  finiteOrbits : OrbitCoverData Cn F
  OrbitCoverData.Reps finiteOrbits = D.Rep
  OrbitCoverData.reps-set finiteOrbits = D.rep-set
  OrbitCoverData.start finiteOrbits r = cosetPoint j (D.repr r)
  OrbitCoverData.Stabilizer finiteOrbits = D.Stab
  OrbitCoverData.inclusion finiteOrbits = D.stabC
  OrbitCoverData.fixes finiteOrbits r k =
    cosetPoint-action j (D.repr r) (hom i .fst (hom (D.stabC r) .fst k))
    ∙ Cos.point-respects _ (D.repr r) (D.stabH r .fst k , D.naturality r k)
  OrbitCoverData.full finiteOrbits r c p = w .fst , w .snd .snd
    where
    h = Cos.point-effective (D.repr r G.· hom i .fst c) (D.repr r)
      (sym (cosetPoint-action j (D.repr r) (hom i .fst c)) ∙ p)
    w = D.stab-full r (h .fst) c (h .snd)
  OrbitCoverData.disjoint finiteOrbits r s c p = D.separate r s (h .fst) c (h .snd)
    where
    h = Cos.point-effective (D.repr r G.· hom i .fst c) (D.repr s)
      (sym (cosetPoint-action j (D.repr r) (hom i .fst c)) ∙ p)
  OrbitCoverData.complete finiteOrbits (h , p) = EM.elimProp H
    {B = λ h → (p : Bmap (hom j) h ≡ embase)
      → PT.∥ Σ[ r ∈ D.Rep ] Σ[ c ∈ Cn .fst ]
          subst (λ b → F b .fst) (emloop c) (cosetPoint j (D.repr r)) ≡ (h , p) ∥₁}
    (λ _ → isPropΠ λ _ → PT.squash₁)
    (λ p → PT.map
      (λ (r , a , c , e) → r , c ,
        cosetPoint-action j (D.repr r) (hom i .fst c)
        ∙ Cos.point-respects _ (loopCode G p) (a , e)
        ∙ (λ k → embase , loop-codeLoop G p k)) (D.cover (loopCode G p))) h p

  -- Finite, algebraic markings for the inverse-image stabilizers lℤ.
  -- No equivalence or homotopy of classifying spaces is assumed here.
  record BoundaryData : Type₀ where
    field
      length-1 order-1 : D.Rep → ℕ
      factor : (r : D.Rep) → suc n ≡ suc (length-1 r) N.· suc (order-1 r)
      liftHom : (r : D.Rep) → GroupHom ℤGroup (D.Stab r)
      lift-mark : (r : D.Rep) (k : ℤ)
        → hom (D.stabC r) .fst (liftHom r .fst k)
          ≡ q .fst (pos (suc (length-1 r)) Z.· k)
      full : (r : D.Rep) (s : D.Stab r .fst) (k : ℤ)
        → hom (D.stabC r) .fst s ≡ q .fst k
        → Σ[ m ∈ ℤ ] pos (suc (length-1 r)) Z.· m ≡ k

  module Boundary (B : BoundaryData) where
    open BoundaryData B
    private
      module O = OrbitCoverData finiteOrbits

    circleFamily : Circle → hSet ℓ-zero
    circleFamily z = F (Bmap q z)

    integerOrbits : OrbitCoverData ℤGroup circleFamily
    OrbitCoverData.Reps integerOrbits = D.Rep
    OrbitCoverData.reps-set integerOrbits = D.rep-set
    OrbitCoverData.start integerOrbits = O.start
    OrbitCoverData.Stabilizer integerOrbits r = ℤGroup
    OrbitCoverData.inclusion integerOrbits r = positiveMultiple (length-1 r)
    OrbitCoverData.fixes integerOrbits r k =
      cong (λ c → subst (λ b → F b .fst) (emloop c) (O.start r))
        (sym (lift-mark r k)) ∙ O.fixes r (liftHom r .fst k)
    OrbitCoverData.full integerOrbits r k p =
      full r (w .fst) k (w .snd)
      where w = O.full r (q .fst k) p
    OrbitCoverData.disjoint integerOrbits r s k = O.disjoint r s (q .fst k)
    OrbitCoverData.complete integerOrbits x = PT.map
      (λ (r , c , p) → r , pos (c .fst) ,
        cong (λ d → subst (λ b → F b .fst) (emloop d) (O.start r))
          (residue-section n c) ∙ p) (O.complete x)

    module M = OrbitComparison ℤGroup circleFamily integerOrbits

    circleEquivalence : (D.Rep × Circle) ≃ M.Target
    circleEquivalence = M.equivalence

    degree-projection : (r : D.Rep) (z : Circle)
      → circleEquivalence .fst (r , z) .fst ≡ degree (suc (length-1 r)) z
    degree-projection r z = refl

    boundary : M.Source → P.Source
    boundary (r , z) = r , Bmap (liftHom r) z

    toFinite : M.Target → Σ[ b ∈ EM₁ Cn ] F b .fst
    toFinite (z , x) = Bmap q z , x

    finiteComparison : P.Source → Σ[ b ∈ EM₁ Cn ] F b .fst
    finiteComparison u = P.right u , P.left u , P.seam u

    boundary-naturality : (u : M.Source)
      → toFinite (circleEquivalence .fst u) ≡ finiteComparison (boundary u)
    boundary-naturality (r , z) = EM.elimSet ℤGroup
      {B = λ z → toFinite (M.comparison (r , z)) ≡ finiteComparison (boundary (r , z))}
      (λ _ → isGroupoidΣ emsquash (λ b → isSet→isGroupoid (F b .snd)) _ _)
      refl (λ k → ΣSquareSet (λ b → F b .snd)
        (λ a b → emloop (lift-mark r k (~ b)) a)) z

    -- The output maps to the specified double-coset comparison.
    toDoubleCosetPullback : M.Target → P.Target
    toDoubleCosetPullback (z , h , p) = h , Bmap q z , p

    doubleCoset-naturality : (u : M.Source)
      → toDoubleCosetPullback (circleEquivalence .fst u)
        ≡ DC.DoubleCosetComparison.e (DC.doubleCosetPullback j i D) .fst (boundary u)
    doubleCoset-naturality u = cong (λ (b , h , p) → h , b , p) (boundary-naturality u)

    marked-generator-in-H : (r : D.Rep)
      → hom j .fst (D.stabH r .fst (liftHom r .fst (pos 1)))
        ≡ DC.CanonicalStabilizer.conjugate j i (D.repr r)
            (q .fst (pos (suc (length-1 r))))
    marked-generator-in-H r = DC.CanonicalStabilizer.square→conjugate j i (D.repr r)
      (D.stabH r .fst (liftHom r .fst (pos 1))) (q .fst (pos (suc (length-1 r))))
      (D.naturality r (liftHom r .fst (pos 1))
       ∙ cong (λ c → D.repr r G.· hom i .fst c)
           (lift-mark r (pos 1) ∙ cong (q .fst) (Z.·IdR (pos (suc (length-1 r))))))

-- Literal homotopy-pullback form of the dependent-sum construction.
open import Cubical.Functions.Fibration using (fiberEquiv)

familyPullback : {A B : Type₀} (F : B → Type₀) (f : A → B)
  → (Σ[ a ∈ A ] F (f a)) ≃ PB f (fst {B = F})
familyPullback F f = compEquiv
  (Σ-cong-equiv-snd (λ a → invEquiv (fiberEquiv F (f a))))
  (isoToEquiv (iso (λ (a , u , p) → a , u , sym p)
                  (λ (a , u , p) → a , u , sym p)
                  (λ _ → refl) (λ _ → refl)))

-- An actual map of HIT circles, calibrated by winding number +l.
degreeS¹ : ℕ → S1.S¹ → S1.S¹
degreeS¹ l = Circle→HIT ∘ degree l ∘ HIT→Circle

degreeS¹-loop : (l : ℕ) → cong (degreeS¹ l) S1.loop ≡ S1.intLoop (pos l)
degreeS¹-loop l = cong (cong Circle→HIT) (positive-degree l)

degreeS¹-winding : (l : ℕ) → S1.winding (cong (degreeS¹ l) S1.loop) ≡ pos l
degreeS¹-winding l = cong S1.winding (degreeS¹-loop l) ∙ S1.windingℤLoop (pos l)

module HITCircleCover {X : Type₀} (α : FinitePermutation X)
  (R : CyclicOrbitData α) where
  private
    module R = CyclicOrbitData R
    module M = CircleConstruction α R

  Family : S1.S¹ → Type₀
  Family z = M.circleFamily (HIT→Circle z) .fst

  total-reindex : (Σ S1.S¹ Family) ≃ M.CircleCover
  total-reindex = Σ-cong-equiv-fst S¹≃Circle

  circles : (R.Rep × S1.S¹) ≃ (Σ S1.S¹ Family)
  circles = compEquiv (Σ-cong-equiv-snd (λ _ → S¹≃Circle))
    (compEquiv M.CircleOrbits.equivalence (invEquiv total-reindex))

  positive-projection : (r : R.Rep) (z : S1.S¹)
    → circles .fst (r , z) .fst ≡ degreeS¹ (R.length r) z
  positive-projection r z = refl

  positive-loop : (r : R.Rep)
    → S1.winding (cong (λ z → circles .fst (r , z) .fst) S1.loop) ≡ pos (R.length r)
  positive-loop r = degreeS¹-winding (R.length r)

  pullback : (R.Rep × S1.S¹)
    ≃ PB (M.circleToCyclic ∘ HIT→Circle) (fst {B = λ b → M.finiteFamily b .fst})
  pullback = compEquiv circles
    (familyPullback (λ b → M.finiteFamily b .fst) (M.circleToCyclic ∘ HIT→Circle))

  pullback-projection : (r : R.Rep) (z : S1.S¹)
    → pullback .fst (r , z) .fst ≡ degreeS¹ (R.length r) z
  pullback-projection r z = refl

  length-times-order : (r : R.Rep)
    → suc R.modulus-1 ≡ R.length r N.· suc (R.order-1 r)
  length-times-order = R.factor

  boundary : (R.Rep × S1.S¹) → M.FiniteOrbits.Source
  boundary (r , z) = r , Bmap (M.Stabilizer.boundaryHom r) (HIT→Circle z)

  toCyclicCover : (Σ S1.S¹ Family) → M.CyclicCover
  toCyclicCover (z , x) = M.circleToCyclic (HIT→Circle z) , x

  component-compatible : (u : R.Rep × S1.S¹)
    → toCyclicCover (circles .fst u) ≡ M.FiniteOrbits.comparison (boundary u)
  component-compatible (r , z) =
    cong M.toCyclicCover (secEq total-reindex (M.CircleOrbits.comparison (r , HIT→Circle z)))
    ∙ M.boundary-naturality (r , HIT→Circle z)

  boundary-positive-generator : (r : R.Rep)
    → cong (λ z → boundary (r , z) .snd) S1.loop ≡ emloop (M.Stabilizer.generator r)
  boundary-positive-generator r = refl
