{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.H0Tail where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc ; ¬Fin0)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum using (_⊎_ ; inl ; inr)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Sequence using (SequenceMap)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.GroupPath using (GroupPath)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Subgroup using (kerGroup ; kerGroup≡)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_] ; sumCoefficients)
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology using (homology)
open import Cubical.CW.Base using (CWskel ; hasCWskel)
open import Cubical.CW.Map using (cellMap)
open import Cubical.CW.ChainComplex using (∂ ; H̃ˢᵏᵉˡ ; CW-AugChainComplex ; module augmentation)
open import Cubical.CW.Strictification using (strictCWskel ; strictifyFame ; strict≡)
open import Cubical.CW.Instances.Empty using (CWskel⊥)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→id)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (rUnitₖ)
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T² ; mulC ; _+C_)
open import DeloopS3.Move.CancelGeneral using (module CircleCoordinates)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Basis using (mulC-one ; coefficient)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map ; cellular-map-agrees)
open import DeloopS3.Bridge.DMCExactness.Geometric using (actual-source)
open import DeloopS3.Bridge.ComponentHomology.ChainTools using (chosen-skeleton)
open import DeloopS3.Bridge.ComponentHomology.Finite using (graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.Circle using (C-skeleton ; circle-boundary)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Cellular using (module ProductDifferentials)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.SeifertCharts using (concrete-torus-skeleton)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Comparison using (module Comparison)
open import DeloopS3.Bridge.CellularPushout.PrismChains.FiniteFree using (finite-free-direct-finite)
open import DeloopS3.Bridge.DegreeSpan.Pieces using (module SumSkeleton)
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry using (overlapCW ; fillingsCW)
open import DeloopS3.Bridge.Profile.BaseSeifert.Functor using (map-comp)
import DeloopS3.Bridge.Profile.H1Data.Inner as H1Inner

open IsGroupHom
open ChainComplex

-- A section of the literal continuous right leg, not just of its matrix.
right-section : fst fillingsCW → fst overlapCW
right-section (inl (inl t)) = inl (inl (t , 0C))
right-section (inl (inr t)) = inl (inr (t , 0C))
right-section (inr t) = inr (t , t)

abstract
  row-one-section : (p : ℤ) (t : C) → Literal.row (pos 1) p (t , 0C) ≡ t
  row-one-section p t = rUnitₖ {G = ℤAbGroup} 1 (mulC (pos 1) t) ∙ mulC-one t

  row-diagonal-section : (r : ℤ) (t : C) → Literal.row (pos 1 Z.- r) r (t , t) ≡ t
  row-diagonal-section r t = sym (CircleCoordinates.mulC-add (pos 1 Z.- r) r t)
    ∙ cong (λ n → mulC n t) (coefficient r) ∙ mulC-one t

  allRight-section : (p q r : ℤ) (t : fst fillingsCW)
    → Literal.Seifert.allRight p q r (right-section t) ≡ t
  allRight-section p q r (inl (inl t)) = cong {B = λ _ → (C ⊎ C) ⊎ C} (λ x → inl (inl x)) (row-one-section p t)
  allRight-section p q r (inl (inr t)) = cong {B = λ _ → (C ⊎ C) ⊎ C} (λ x → inl (inr x)) (row-one-section q t)
  allRight-section p q r (inr t) = cong inr (row-diagonal-section r t)

  right-homology-section : (p q r : ℤ) (n : ℕ)
    → compGroupHom (cellular-map fillingsCW overlapCW n right-section)
        (cellular-map overlapCW fillingsCW n (Literal.Seifert.allRight p q r))
      ≡ idGroupHom
  right-homology-section p q r n =
    sym (map-comp fillingsCW overlapCW fillingsCW n (Literal.Seifert.allRight p q r) right-section)
    ∙ cong (cellular-map fillingsCW fillingsCW n) (funExt (allRight-section p q r))
    ∙ cellular-map-agrees fillingsCW fillingsCW n (idfun _)
    ∙ H̃ᶜʷ→id {C = fillingsCW} n

-- The empty-overlap coproduct has no prism generators. Transfer the
-- component differential through the actual prism-chain comparison.
private
  emptyCell : (K : CWskel ℓ-zero) → cellMap (strictCWskel CWskel⊥) (strictCWskel K)
  SequenceMap.map (emptyCell K) n x = Empty.rec (invEq (strictifyFame CWskel⊥ n) x)
  SequenceMap.comm (emptyCell K) n x = Empty.rec (invEq (strictifyFame CWskel⊥ n) x)

  strict-edge-zero : (K : CWskel ℓ-zero) → ∂ K 0 ≡ trivGroupHom
    → ∂ (strictCWskel K) 0 ≡ trivGroupHom
  strict-edge-zero K = subst (λ L → ∂ L 0 ≡ trivGroupHom) (sym (strict≡ K))

module SumEdges (X Y : Type₀) (MX : hasCWskel X) (MY : hasCWskel Y)
  (dx : ∂ (fst MX) 0 ≡ trivGroupHom) (dy : ∂ (fst MY) 0 ≡ trivGroupHom) where
  private
    module Q = Comparison CWskel⊥ (fst MX) (fst MY) (emptyCell (fst MX)) (emptyCell (fst MY))
    module E = Q.Complete finite-free-direct-finite
    module CP = Q.CP

    empty-chain : (a : fst (CP.Aₙ 0)) → a ≡ (λ _ → pos 0)
    empty-chain a = funExt λ k → Empty.rec (¬Fin0 k)

    model-edge-zero : (z : fst (chain CP.DMC 2))
      → fst (bdry CP.DMC 1) z ≡ GroupStr.1g (snd (AbGroup→Group (chain CP.DMC 1)))
    model-edge-zero (b , c , a) = CP.DMC-∂₁ b c a
      ∙ ΣPathP
        (cong₂ (AbGroupStr._+_ (snd (CP.Bₙ 0)))
          (funExt⁻ (cong fst (strict-edge-zero (fst MX) dx)) b)
          (cong (fst (CP.f_* 0)) (empty-chain a) ∙ pres1 (snd (CP.f_* 0)))
        , cong₂ (λ x y → AbGroupStr._+_ (snd (CP.Cₙ 0)) x (AbGroupStr.-_ (snd (CP.Cₙ 0)) y))
          (funExt⁻ (cong fst (strict-edge-zero (fst MY) dy)) c)
          (cong (fst (CP.g_* 0)) (empty-chain a) ∙ pres1 (snd (CP.g_* 0))))

  abstract
    edge-zero : ∂ (SumSkeleton.skeleton X Y MX MY) 0 ≡ trivGroupHom
    edge-zero = GroupHom≡ (funExt λ z →
      cong (fst (bdry Q.actual 1)) (sym (funExt⁻ (cong fst (E.qχ 2)) z))
      ∙ funExt⁻ (cong fst Q.q-edge) (fst (Q.χ 2) z)
      ∙ cong (fst (Q.q 1)) (model-edge-zero (fst (Q.χ 2) z))
      ∙ pres1 (snd (Q.q 1)))

triple-model : {X : Type₀} → hasCWskel X → hasCWskel ((X ⊎ X) ⊎ X)
triple-model {X} M = SumSkeleton.model (X ⊎ X) X (SumSkeleton.model X X M M) M

abstract
  triple-edge-zero : {X : Type₀} (M : hasCWskel X)
    → ∂ (fst M) 0 ≡ trivGroupHom → ∂ (fst (triple-model M)) 0 ≡ trivGroupHom
  triple-edge-zero {X} M d = SumEdges.edge-zero (X ⊎ X) X (SumSkeleton.model X X M M) M
    (SumEdges.edge-zero X X M M d d) d

  overlap-edge-zero : ∂ (fst (triple-model concrete-torus-skeleton)) 0 ≡ trivGroupHom
  overlap-edge-zero = triple-edge-zero concrete-torus-skeleton (ProductDifferentials.edge-differential-zero 1)

  fillings-edge-zero : ∂ (fst (triple-model C-skeleton)) 0 ≡ trivGroupHom
  fillings-edge-zero = triple-edge-zero C-skeleton (GroupHom≡ (funExt circle-boundary))

-- With zero incoming differential the quotient is the actual kernel,
-- not the entire degree-zero chain group.
module IncomingZero (D : ChainComplex ℓ-zero) (k : ℕ)
  (in-zero : bdry D (suc k) ≡ trivGroupHom) where
  private
    G = AbGroup→Group (chain D (suc k))
    K = kerGroup (bdry D k)

    decode : fst (homology k D) → fst K
    decode = SQ.rec (GroupStr.is-set (snd K)) (idfun _)
      (λ x y → PT.rec (GroupStr.is-set (snd K) _ _)
        (λ (t , p) → kerGroup≡ (bdry D k)
          (GroupTheory.invUniqueL G
            (sym (cong fst p) ∙ funExt⁻ (cong fst in-zero) t)
            ∙ GroupTheory.invInv G (fst y))))

  kernel-iso : GroupIso (homology k D) K
  Iso.fun (fst kernel-iso) = decode
  Iso.inv (fst kernel-iso) = SQ.[_]
  Iso.sec (fst kernel-iso) x = refl
  Iso.ret (fst kernel-iso) = SQ.elimProp
    (λ _ → GroupStr.is-set (snd (homology k D)) _ _) (λ _ → refl)
  snd kernel-iso = makeIsGroupHom
    (SQ.elimProp2 (λ _ _ → GroupStr.is-set (snd K) _ _) (λ _ _ → refl))

private
  take-two : (Fin 3 → ℤ) → Fin 2 → ℤ
  take-two x (zero , _) = x fzero
  take-two x (suc zero , _) = x (fsuc fzero)
  take-two x (suc (suc k) , ())

  extend-two : (Fin 2 → ℤ) → Fin 3 → ℤ
  extend-two x (zero , _) = x fzero
  extend-two x (suc zero , _) = x (fsuc fzero)
  extend-two x (suc (suc zero) , _) = Z.- (x fzero Z.+ x (fsuc fzero))
  extend-two x (suc (suc (suc k)) , ())

  extend-sum-zero : (x : Fin 2 → ℤ) → Z.sumFinℤ (extend-two x) ≡ pos 0
  extend-sum-zero x = cong (Z.- (x fzero Z.+ x (fsuc fzero)) Z.+_)
    (Z.+Comm (x (fsuc fzero)) (x fzero))
    ∙ Z.-Cancel' (x fzero Z.+ x (fsuc fzero))

  take-extend : (x : Fin 2 → ℤ) → take-two (extend-two x) ≡ x
  take-extend x = funExt λ { (zero , _) → refl ; (suc zero , _) → refl ; (suc (suc k) , ()) }

  extend-take : (x : Fin 3 → ℤ) → Z.sumFinℤ x ≡ pos 0 → extend-two (take-two x) ≡ x
  extend-take x p = funExt λ
    { (zero , _) → refl
    ; (suc zero , _) → refl
    ; (suc (suc zero) , _) → sym
        (GroupTheory.invUniqueL ℤGroup
          (cong (x (fsuc (fsuc fzero)) Z.+_) (Z.+Comm (x fzero) (x (fsuc fzero))) ∙ p))
    ; (suc (suc (suc k)) , ()) }

  take-hom : (x y : Fin 3 → ℤ)
    → take-two (λ i → x i Z.+ y i) ≡ (λ i → take-two x i Z.+ take-two y i)
  take-hom x y = funExt λ { (zero , _) → refl ; (suc zero , _) → refl ; (suc (suc k) , ()) }

-- Explicit coordinates (x,y,z) ↦ (x,y), inverse (x,y) ↦ (x,y,-(x+y)).
augmentation-kernel-three : GroupIso (kerGroup (sumCoefficients 3)) (AbGroup→Group ℤ[Fin 2 ])
Iso.fun (fst augmentation-kernel-three) x = take-two (fst x)
Iso.inv (fst augmentation-kernel-three) x = extend-two x , funExt (λ _ → extend-sum-zero x)
Iso.sec (fst augmentation-kernel-three) = take-extend
Iso.ret (fst augmentation-kernel-three) (x , p) = kerGroup≡ (sumCoefficients 3)
  (extend-take x (funExt⁻ p fzero))
snd augmentation-kernel-three = makeIsGroupHom λ x y → take-hom (fst x) (fst y)

abstract
  three-vertex-H₀ : (K : CWskel ℓ-zero) → snd K .fst 0 ≡ 3
    → ∂ K 0 ≡ trivGroupHom → GroupEquiv (H̃ˢᵏᵉˡ K 0) (AbGroup→Group ℤ[Fin 2 ])
  three-vertex-H₀ K vertices edges =
    compGroupEquiv (GroupIso→GroupEquiv (IncomingZero.kernel-iso (CW-AugChainComplex K) 0 edges))
      (compGroupEquiv
        (invEq (GroupPath _ _)
          (cong kerGroup (augmentation.ϵ-alt K)
            ∙ cong (λ n → kerGroup (sumCoefficients n)) vertices))
        (GroupIso→GroupEquiv augmentation-kernel-three))

  overlap-H₀ : GroupEquiv (H̃ᶜʷ overlapCW 0) (AbGroup→Group ℤ[Fin 2 ])
  overlap-H₀ = compGroupEquiv (chosen-skeleton overlapCW (triple-model concrete-torus-skeleton) 0)
    (three-vertex-H₀ (fst (triple-model concrete-torus-skeleton)) refl overlap-edge-zero)

  fillings-H₀ : GroupEquiv (H̃ᶜʷ fillingsCW 0) (AbGroup→Group ℤ[Fin 2 ])
  fillings-H₀ = compGroupEquiv (chosen-skeleton fillingsCW (triple-model C-skeleton) 0)
    (three-vertex-H₀ (fst (triple-model C-skeleton)) refl fillings-edge-zero)

-- Unmarked coordinates suffice: conjugation preserves the splitting.
module SplitFiniteFree (n : ℕ) (G H : Group₀)
  (eG : GroupEquiv G (AbGroup→Group ℤ[Fin n ]))
  (eH : GroupEquiv H (AbGroup→Group ℤ[Fin n ]))
  (u : GroupHom G H) (t : GroupHom H G)
  (section : compGroupHom t u ≡ idGroupHom) where
  private
    g = equivFun (fst eG)
    h = equivFun (fst eH)
    g⁻ = invEq (fst eG)
    h⁻ = invEq (fst eH)

    U T : AbGroupHom ℤ[Fin n ] ℤ[Fin n ]
    U = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv eG))
      (compGroupHom u (GroupEquiv→GroupHom eH))
    T = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv eH))
      (compGroupHom t (GroupEquiv→GroupHom eG))

    UT : compGroupHom T U ≡ idGroupHom
    UT = GroupHom≡ (funExt λ x →
      cong (h ∘ fst u) (retEq (fst eG) (fst t (h⁻ x)))
      ∙ cong h (funExt⁻ (cong fst section) (h⁻ x))
      ∙ secEq (fst eH) x)

    TU : compGroupHom U T ≡ idGroupHom
    TU = finite-free-direct-finite n T U UT

    TU-eval : (a : fst G) → fst T (fst U (g a)) ≡ g (fst t (fst u a))
    TU-eval a = cong (fst T) (cong (h ∘ fst u) (retEq (fst eG) a))
      ∙ cong (g ∘ fst t) (retEq (fst eH) (fst u a))

  abstract
    retraction : compGroupHom u t ≡ idGroupHom
    retraction = GroupHom≡ (funExt λ a →
      sym (retEq (fst eG) (fst t (fst u a)))
      ∙ cong g⁻ (sym (TU-eval a) ∙ funExt⁻ (cong fst TU) (g a))
      ∙ retEq (fst eG) a)

    injective : (a b : fst G) → fst u a ≡ fst u b → a ≡ b
    injective a b p = sym (funExt⁻ (cong fst retraction) a)
      ∙ cong (fst t) p ∙ funExt⁻ (cong fst retraction) b

abstract
  right-H₀-retraction : (p q r : ℤ)
    → compGroupHom (cellular-map overlapCW fillingsCW 0 (Literal.Seifert.allRight p q r))
        (cellular-map fillingsCW overlapCW 0 right-section)
      ≡ idGroupHom
  right-H₀-retraction p q r = SplitFiniteFree.retraction 2
    (H̃ᶜʷ overlapCW 0) (H̃ᶜʷ fillingsCW 0) overlap-H₀ fillings-H₀
    (cellular-map overlapCW fillingsCW 0 (Literal.Seifert.allRight p q r))
    (cellular-map fillingsCW overlapCW 0 right-section)
    (right-homology-section p q r 0)

  right-H₀-injective : (p q r : ℤ) (a b : fst (H̃ᶜʷ overlapCW 0))
    → fst (cellular-map overlapCW fillingsCW 0 (Literal.Seifert.allRight p q r)) a
      ≡ fst (cellular-map overlapCW fillingsCW 0 (Literal.Seifert.allRight p q r)) b
    → a ≡ b
  right-H₀-injective p q r a b s =
    sym (funExt⁻ (cong fst (right-H₀-retraction p q r)) a)
    ∙ cong (fst (cellular-map fillingsCW overlapCW 0 right-section)) s
    ∙ funExt⁻ (cong fst (right-H₀-retraction p q r)) b

  -- The proof ignores the left coordinate and its chosen CW witness.
  -- The negative sign on the right coordinate is undone explicitly.
  zero-tail-with-left : (L : CW₀) (f : fst overlapCW → fst L)
    (p q r : ℤ) (a : fst (H̃ᶜʷ overlapCW 0))
    → actual-source overlapCW L fillingsCW f (Literal.Seifert.allRight p q r) 0 a
      ≡ GroupStr.1g (snd (DirProd (H̃ᶜʷ L 0) (H̃ᶜʷ fillingsCW 0)))
    → a ≡ GroupStr.1g (snd (H̃ᶜʷ overlapCW 0))
  zero-tail-with-left L f p q r a s =
    right-H₀-injective p q r a (GroupStr.1g (snd (H̃ᶜʷ overlapCW 0)))
      (sym (GroupTheory.invInv (H̃ᶜʷ fillingsCW 0)
          (fst (cellular-map overlapCW fillingsCW 0 (Literal.Seifert.allRight p q r)) a))
        ∙ cong (GroupStr.inv (snd (H̃ᶜʷ fillingsCW 0))) (cong snd s)
        ∙ GroupTheory.inv1g (H̃ᶜʷ fillingsCW 0)
        ∙ sym (pres1 (snd (cellular-map overlapCW fillingsCW 0 (Literal.Seifert.allRight p q r)))))

  -- Exact BaseSeifert inner-span statement, for all p,q,r.
  zero-tail : (p q r : ℤ) (a : fst (H̃ᶜʷ overlapCW 0))
    → actual-source overlapCW graph×circleCW fillingsCW
        (Literal.Seifert.allLeft p q r) (Literal.Seifert.allRight p q r) 0 a
      ≡ GroupStr.1g (snd (DirProd (H̃ᶜʷ graph×circleCW 0) (H̃ᶜʷ fillingsCW 0)))
    → a ≡ GroupStr.1g (snd (H̃ᶜʷ overlapCW 0))
  zero-tail p q r = zero-tail-with-left graph×circleCW (Literal.Seifert.allLeft p q r) p q r

-- This has precisely the zero-tail field type of Inner.H1Coordinates,
-- including Inner's distinct left-hand CW witness. No H1 premise is used.
module InnerTail (q n : ℤ) where
  private
    module I = H1Inner.Inner q n

  abstract
    inner-zero-tail : (a : fst (H̃ᶜʷ I.overlapCW 0))
      → actual-source I.overlapCW I.leftCW I.rightCW
          (Literal.Seifert.allLeft (pos 2) q n) (Literal.Seifert.allRight (pos 2) q n) 0 a
        ≡ GroupStr.1g (snd (DirProd (H̃ᶜʷ I.leftCW 0) (H̃ᶜʷ I.rightCW 0)))
      → a ≡ GroupStr.1g (snd (H̃ᶜʷ I.overlapCW 0))
    inner-zero-tail = zero-tail-with-left I.leftCW (Literal.Seifert.allLeft (pos 2) q n) (pos 2) q n
