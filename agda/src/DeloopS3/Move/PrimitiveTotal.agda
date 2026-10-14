{-# OPTIONS --safe --cubical #-}

-- Total-space cancellation for the primitive filling, with its graph correction.
-- Reattachment of retained faces is handled by Cert.Interpret.Cancel.
module DeloopS3.Move.PrimitiveTotal where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Univalence
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Int using (ℤ)
import Cubical.Data.Int as Z
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure
  using (assocₖ; commₖ; rUnitₖ; lCancelₖ)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import Cubical.HITs.Pushout.Flattening using (module FlatteningLemma)
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)
open import DeloopS3.Move.CancelMinimalCore
open import DeloopS3.Move.CancelLoopCell
open import DeloopS3.Move.CancelMinimal
  using (C; K; 0C; 0K; T²; _+C_; mulC; ω; ω₀; ω-add; U; transport-U; module Minimal)
open import DeloopS3.Move.CancelGeneral
  using (module CircleCoordinates; module ForwardGraph; module SignedWordCoordinates;
    signInt; GraphWord; exponent-x)
open import DeloopS3.Move.ShearFormula using (TκEquiv)
-- Only the positive, pointed circle model; no classification import.
open import DeloopS3.Cover.Orientation.CircleModel
  using (circleToC; CToCircle; circle-section; S¹≃C)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Shapes
  using (module Stage)

-- Unlike CancelGeneral.Staging this has an arbitrary first right vertex.
-- Its forward/inverse maps and constructorwise homotopies are also public.
module Staging₂ {ℓ : Level} {L A B R S : Type ℓ}
  (a : A → L) (b : B → L) (f : A → R) (g : B → S) where
  open Stage a b f g public

stage₂ : {ℓ : Level} {L A B R S : Type ℓ}
  (a : A → L) (b : B → L) (f : A → R) (g : B → S)
  → Stage.All a b f g ≃ Stage.Staged a b f g
stage₂ = Stage.stage₂

-- Extensionality along a specified equivalence, with all endpoints given.
abstract
  agree-on-equiv : {ℓ ℓ′ ℓ″ : Level} {A : Type ℓ} {B : Type ℓ′}
    {X : Type ℓ″} (e : A ≃ B) (f g : B → X)
    → ((a : A) → f (e .fst a) ≡ g (e .fst a))
    → (b : B) → f b ≡ g b
  agree-on-equiv e f g h b = sym (cong f (secEq e b))
    ∙ h (invEq e b) ∙ cong g (secEq e b)

-- Changing the basepoint of an ACTUAL graph image.  The homotopy on
-- retained vertices is supplied, and its loop square is transport-filler.
module PointedGraphImage {ℓ ℓ′ : Level} {Q : Type ℓ} (q₀ : Q)
  {X : Type ℓ′} (f : AddLoop Q q₀ → X) (g : Q → X)
  (h : (a : Q) → f (incQ a) ≡ g a) where
  generator : g q₀ ≡ g q₀
  generator = transport (λ i → h q₀ i ≡ h q₀ i) (cong f x)

  normalized : AddLoop Q q₀ → X
  normalized (incQ a) = g a
  normalized (x i) = generator i

  comparison : f ≡ normalized
  comparison i (incQ a) = h a i
  comparison i (x j) = transport-filler
    (λ i → h q₀ i ≡ h q₀ i) (cong f x) i j

abstract
  based-circle-homotopy : {ℓ : Level} {X : Type ℓ} (b : X)
    (f g : S¹ → X) (p : f base ≡ b) (r : g base ≡ b)
    (H : (u : S¹) → f u ≡ g u)
    → PathP (λ i → H base i ≡ b) p r
    → transport (λ i → p i ≡ p i) (cong f loop)
      ≡ transport (λ i → r i ≡ r i) (cong g loop)
  based-circle-homotopy b f g p r H sq j =
    transport (λ i → sq j i ≡ sq j i) (λ i → H (loop i) j)

  loop-square-refl : {ℓ : Level} {X : Type ℓ} {b : X}
    (p q v : b ≡ b) → v ≡ refl
    → PathP (λ i → v i ≡ v i) p q → p ≡ q
  loop-square-refl p q v e sq =
    subst (λ v → PathP (λ i → v i ≡ v i) p q) e sq

  cancel-seam-at-base : {ℓ : Level} {X : Type ℓ} {a b c : X}
    (p : a ≡ b) (h : a ≡ c)
    → sym h ∙ (p ∙ ((refl ∙ sym p) ∙ h)) ≡ refl
  cancel-seam-at-base p h =
    cong (λ z → sym h ∙ (p ∙ (z ∙ h))) (sym (lUnit (sym p)))
    ∙ cong (sym h ∙_)
      (assoc p (sym p) h ∙ cong (_∙ h) (rCancel p) ∙ sym (lUnit h))
    ∙ lCancel h

-- Prove affinity before substituting the large R1 cell homotopy.
abstract
  omega-transport-affine : (p : Path K 0K 0K) (t : C)
    → invEq ω (transport (cong U p) (ω .fst t)) ≡ t +C invEq ω p
  omega-transport-affine p t = cong (invEq ω)
    (transport-U p (ω .fst t)
      ∙ cong (ω .fst t ∙_) (sym (secEq ω p))
      ∙ sym (ω-add t (invEq ω p))) ∙ retEq ω (t +C invEq ω p)

-- Circle arithmetic for the actual row, rather than the BA(d,s) chart.
abstract
  unshear-fibre : (k : ℤ) (u t : C)
    → (t +C mulC (Z.- k) u) +C mulC k u ≡ t
  unshear-fibre k u t =
    cong (λ z → (t +C z) +C mulC k u)
      (CircleCoordinates.mulC-negate k u)
    ∙ sym (assocₖ {G = ℤAbGroup} 1 t
        (CircleCoordinates.-C mulC k u) (mulC k u))
    ∙ cong (t +C_) (lCancelₖ {G = ℤAbGroup} 1 (mulC k u))
    ∙ rUnitₖ {G = ℤAbGroup} 1 t

  unshear-row : (s k : ℤ) (u t : C)
    → mulC s u +C (t +C mulC (Z.- k) u)
      ≡ t +C mulC (s Z.- k) u
  unshear-row s k u t =
    assocₖ {G = ℤAbGroup} 1 (mulC s u) t (mulC (Z.- k) u)
    ∙ cong (_+C mulC (Z.- k) u)
        (commₖ {G = ℤAbGroup} 1 (mulC s u) t)
    ∙ sym (assocₖ {G = ℤAbGroup} 1 t (mulC s u) (mulC (Z.- k) u))
    ∙ cong (t +C_) (sym (CircleCoordinates.mulC-add s (Z.- k) u))

module Diagram {ℓ : Level} (Q : Type ℓ) (q₀ : Q)
  (L R : q₀ ≡ q₀) (ε : Sign) (s k : ℤ) where
  module P = PrimitiveCancellation Q q₀ L R ε

  oldGraph : Type ℓ
  oldGraph = AddLoop Q q₀

  wordCircle : C → oldGraph
  wordCircle = circleMap P.w ∘ CToCircle

  left : T² → oldGraph × C
  left (u , t) = wordCircle u , t +C mulC k u

  right : T² → C
  right (u , t) = mulC s u +C t

  V : Type ℓ
  V = Pushout left right

  q : ℤ
  q = s Z.- k

  normal-left : T² → oldGraph × C
  normal-left (u , t) = wordCircle u , t

  normal-right : T² → C
  normal-right (u , t) = t +C mulC q u

  Normal : Type ℓ
  Normal = Pushout normal-left normal-right

  abstract
    unshear : Normal ≃ V
    unshear = pushoutEquiv normal-left normal-right left right
      (TκEquiv (Z.- k)) (idEquiv (oldGraph × C)) (idEquiv C)
      (funExt λ { (u , t) → ΣPathP (refl , sym (unshear-fibre k u t)) })
      (funExt λ { (u , t) → sym (unshear-row s k u t) })

    unshear-graph : (a : oldGraph) (t : C)
      → unshear .fst (inl (a , t)) ≡ inl (a , t)
    unshear-graph a t = refl

  -- Work over the primitive S¹ cofiber, then change only the overlap
  -- coordinate by the positive S¹≃C, retaining the model-change square.
  hit-left : S¹ × C → oldGraph × C
  hit-left (u , t) = circleMap P.w u , t

  hit-right : S¹ × C → C
  hit-right (u , t) = t +C mulC q (circleToC u)

  HitTotal : Type ℓ
  HitTotal = Pushout hit-left hit-right

  abstract
    circle-chart : HitTotal ≃ Normal
    circle-chart = pushoutEquiv hit-left hit-right normal-left normal-right
      (Σ-cong-equiv-fst {B = λ (_ : C) → C} S¹≃C)
      (idEquiv (oldGraph × C)) (idEquiv C)
      (funExt λ { (u , t) → ΣPathP
        (cong (circleMap P.w) (sym (circle-section u)) , refl) }) refl

    circle-chart-graph : (a : oldGraph) (t : C)
      → circle-chart .fst (inl (a , t)) ≡ inl (a , t)
    circle-chart-graph a t = refl

    to-old : HitTotal ≃ V
    to-old = compEquiv circle-chart unshear

    to-old-graph : (a : oldGraph) (t : C)
      → to-old .fst (inl (a , t)) ≡ inl (a , t)
    to-old-graph a t = cong (unshear .fst) (circle-chart-graph a t)
      ∙ unshear-graph a t

  -- One specified path family, not a classification of circle bundles.
  m : P.V → K
  m (inl a) = 0K
  m (inr tt) = 0K
  m (push u i) = ω .fst (mulC q (circleToC u)) i

  Total : Type ℓ
  Total = Σ P.V (U ∘ m)

  correction : (z : P.V) → m z ≡ 0K
  correction z = cong m (λ i → P.H (~ i) z)

  -- This is the retained face of the R1 cell cube, not an
  -- assertion that the target has proposition-valued squares.
  correction-on-Q : (a : Q) → correction (P.j a) ≡ refl
  correction-on-Q a t i = m (P.H-on-Q (~ i) t a)

  graph-winding : oldGraph → C
  graph-winding a = invEq ω (correction (inl a))

  graph-value : oldGraph → C → Q × C
  graph-value a t = P.r (inl a) , t +C graph-winding a

  module M = Minimal q
  module Flat = FlatteningLemma (circleMap P.w) (λ (_ : S¹) → tt)
    (λ (_ : oldGraph) → C) (λ (_ : Unit) → C)
    (λ u → M.rotₛ (circleToC u))

  chart-forward : Pushout Flat.Σf Flat.Σg → HitTotal
  chart-forward (inl z) = inl z
  chart-forward (inr (tt , t)) = inr t
  chart-forward (push z i) = push z i

  chart-backward : HitTotal → Pushout Flat.Σf Flat.Σg
  chart-backward (inl z) = inl z
  chart-backward (inr t) = inr (tt , t)
  chart-backward (push z i) = push z i

  chart-sec : (z : HitTotal) → chart-forward (chart-backward z) ≡ z
  chart-sec (inl z) = refl
  chart-sec (inr t) = refl
  chart-sec (push z i) = refl

  chart-ret : (z : Pushout Flat.Σf Flat.Σg)
    → chart-backward (chart-forward z) ≡ z
  chart-ret (inl z) = refl
  chart-ret (inr (tt , t)) = refl
  chart-ret (push z i) = refl

  family : (z : P.V) → Flat.E z ≃ U (m z)
  family (inl a) = ω
  family (inr tt) = ω
  family (push u i) = ua-equiv-family (M.rotₛ (circleToC u))
    (λ i → U (ω .fst (mulC q (circleToC u)) i)) ω ω
    (λ t → toPathP (sym (M.seam-naturality (circleToC u) t))) i

  abstract
    flatten-chart : Pushout Flat.Σf Flat.Σg ≃ HitTotal
    flatten-chart = isoToEquiv
      (iso chart-forward chart-backward chart-sec chart-ret)

    flatten-total : HitTotal ≃ Total
    flatten-total = compEquiv (invEquiv flatten-chart)
      (compEquiv (invEquiv Flat.flatten)
        (Σ-cong-equiv-snd {A = P.V} {B = Flat.E} {B' = U ∘ m} family))

    flatten-graph : (a : oldGraph) (t : C)
      → flatten-total .fst (inl (a , t)) ≡ (inl a , ω .fst t)
    flatten-graph a t = refl

    flatten-core : (t : C)
      → flatten-total .fst (inr t) ≡ (inr tt , ω .fst t)
    flatten-core t = refl

    -- The R1 counit H, including H-on-Q and its cell cube,
    -- supplies the slice homotopy; its direction is m → m ∘ P.j.
    marked-cancel : EquivOver m (m ∘ P.j)
    marked-cancel = P.primitive-cancel-over m

    total-cancel : Total ≃ (Q × C)
    total-cancel = compEquiv
      (Σ-over-equiv {B = K} {X = P.V} {Y = Q} U
        {m = m} {n = m ∘ P.j} marked-cancel)
      (Σ-cong-equiv-snd {A = Q} {B = λ _ → U 0K} {B' = λ _ → C}
        (λ _ → invEquiv ω))

    total-cancel-formula : (z : P.V) (v : U (m z))
      → total-cancel .fst (z , v)
        ≡ (P.r z , invEq ω (transport (cong U (correction z)) v))
    total-cancel-formula z v = refl

  opaque
    cancel-on-retained : (a : Q) (t : C)
      → total-cancel .fst (P.j a , ω .fst t) ≡ (a , t)
    cancel-on-retained a t = total-cancel-formula (P.j a) (ω .fst t)
      ∙ ΣPathP ((λ i → P.rj i a) ,
        (cong (invEq ω)
          (cong (λ (p : Path K 0K 0K) → transport (cong U p) (ω .fst t)) (correction-on-Q a)
            ∙ transportRefl (ω .fst t)) ∙ retEq ω t))

  -- PrimitiveTotalAffine.Affine.cancel-on-graph identifies this transport
  -- formula with graph-value, using the abstract fibre-affinity comparison.

  opaque
    retained-winding : (a : Q) → graph-winding (incQ a) ≡ 0C
    retained-winding a = cong (invEq ω)
      (correction-on-Q a ∙ sym ω₀) ∙ retEq ω 0C

  -- This inclusion is literally the retained graph, not an arbitrary
  -- inverse chosen after forgetting all the charts.
  j-hit : Q × C → HitTotal
  j-hit (a , t) = inl (incQ a , t)

  j-total : Q × C → Total
  j-total (a , t) = P.j a , ω .fst t

  abstract
    j-total-equiv : isEquiv j-total
    j-total-equiv = compEquiv
      (Σ-cong-equiv-snd {A = Q} {B = λ _ → C} {B' = λ _ → U 0K} (λ _ → ω))
      (Σ-cong-equiv-fst {B = U ∘ m} P.jEquiv) .snd

    j-hit-equiv : isEquiv j-hit
    j-hit-equiv = lCancelIsEquiv (flatten-total .fst) j-hit
      (subst isEquiv (sym (funExt λ { (a , t) → flatten-graph (incQ a) t }))
        j-total-equiv) (flatten-total .snd)

  j : Q × C → V
  j (a , t) = inl (incQ a , t)

  abstract
    j-isEquiv : isEquiv j
    j-isEquiv = subst isEquiv
      (funExt λ { (a , t) → to-old-graph (incQ a) t })
      (compEquiv (j-hit , j-hit-equiv) to-old .snd)

    jEquiv : (Q × C) ≃ V
    jEquiv = j , j-isEquiv

  r : V → Q × C
  r = invEq (j , j-isEquiv)

  unit : (z : Q × C) → r (j z) ≡ z
  unit = retEq (j , j-isEquiv)

  counit : (z : V) → j (r z) ≡ z
  counit = secEq (j , j-isEquiv)

  abstract
    r-hit : (z : HitTotal)
      → r (to-old .fst z) ≡ total-cancel .fst (flatten-total .fst z)
    r-hit = agree-on-equiv {A = Q × C} {B = HitTotal} {X = Q × C}
      (j-hit , j-hit-equiv) (r ∘ to-old .fst)
      (total-cancel .fst ∘ flatten-total .fst)
      λ { (a , t) → cong r (to-old-graph (incQ a) t) ∙ unit (a , t)
        ∙ sym (cong (total-cancel .fst) (flatten-graph (incQ a) t)
          ∙ cancel-on-retained a t) }

    -- Actual forward map on the ENTIRE old graph times the fibre, with
    -- its explicit right-transport correction (not just a winding).
    forward-graph : (a : oldGraph) (t : C)
      → r (inl (a , t)) ≡ (P.r (inl a) ,
          invEq ω (transport (cong U (correction (inl a))) (ω .fst t)))
    forward-graph a t = sym (cong r (to-old-graph a t))
      ∙ r-hit (inl (a , t))
      ∙ cong (total-cancel .fst) (flatten-graph a t)
      ∙ total-cancel-formula (inl a) (ω .fst t)

    retained-graph : (a : Q) (t : C)
      → r (inl (incQ a , t)) ≡ (a , t)
    retained-graph a t = unit (a , t)

    old-fibre : (t : C) → r (inl (incQ q₀ , t)) ≡ (q₀ , t)
    old-fibre = retained-graph q₀

-- The cell computation is generic in a map OUT of the normalized
-- partial total.  In particular it never assumes Q is a 1-type.
module NormalizedCoordinates {ℓ : Level} (Q : Type ℓ) (q₀ : Q)
  (L R : q₀ ≡ q₀) (ε : Sign) (s k : ℤ)
  (β : Diagram.HitTotal Q q₀ L R ε s k → Q × C)
  (β-retained : (a : Q) (t : C) → β (inl (incQ a , t)) ≡ (a , t)) where
  module D = Diagram Q q₀ L R ε s k
  module P = PrimitiveCancellation Q q₀ L R ε
  module Fwd = ForwardGraph Q q₀ L R s k

  graph-map : D.oldGraph → Q × C
  graph-map a = β (inl (a , 0C))

  module G = PointedGraphImage q₀ graph-map Fwd.graph (λ a → β-retained a 0C)

  deleted-generator : Fwd.point ≡ Fwd.point
  deleted-generator = G.generator

  -- A homotopy on the ENTIRE core circle, including its fibre loop.
  core : (t : C) → β (inr t) ≡ Fwd.fibre t
  core t =
    (cong (λ c → β (inr c)) (sym (rUnitₖ {G = ℤAbGroup} 1 t))
      ∙ sym (cong β (push (base , t)))) ∙ β-retained q₀ t

  seam : (u : S¹)
    → G.normalized (circleMap P.w u)
      ≡ Fwd.fibre (mulC D.q (circleToC u))
  seam u = sym (λ i → G.comparison i (circleMap P.w u))
    ∙ (cong β (push (u , 0C)) ∙ core (mulC D.q (circleToC u)))

  abstract
    seam-base : seam base ≡ refl
    seam-base = cancel-seam-at-base
      (cong β (push (base , 0C))) (β-retained q₀ 0C)

    word-filling : (Fwd.u ∙ power ε deleted-generator) ∙ Fwd.v ≡ Fwd.h D.q
    word-filling = sym (P.map-word G.normalized)
      ∙ loop-square-refl
        (cong (G.normalized ∘ circleMap P.w) loop)
        (cong (Fwd.fibre ∘ mulC D.q ∘ circleToC) loop)
        (seam base) seam-base (λ i j → seam (loop j) i)
      ∙ cong (cong Fwd.fibre) (cong emloop (Z.·IdR D.q))

    actual-filling : ((Fwd.u ∙ power ε deleted-generator) ∙ Fwd.v) ∙ Fwd.h k
      ≡ Fwd.h s
    actual-filling = cong (_∙ Fwd.h k) word-filling
      ∙ sym (Fwd.h-add D.q k)
      ∙ cong Fwd.h
        (sym (Z.+Assoc s (Z.- k) k) ∙ cong (s Z.+_) (Z.-Cancel' k))

    -- Equality of PAIRS: the second component is the retained primitive
    -- relation comparison (cell cube), not just equality of graph loops.
    deleted-generator-comparison :
      Path (Σ[ y ∈ (Fwd.point ≡ Fwd.point) ]
        ((Fwd.u ∙ power ε y) ∙ Fwd.v ≡ Fwd.h D.q))
        (deleted-generator ,
          Fwd.filling-difference ((Fwd.u ∙ power ε deleted-generator) ∙ Fwd.v)
            actual-filling)
        (Fwd.graph-solution ε , Fwd.graph-solution-fills ε)
    deleted-generator-comparison =
      Fwd.graph-solution-unique ε deleted-generator actual-filling

    deleted-generator-formula : deleted-generator ≡ Fwd.graph-solution ε
    deleted-generator-formula = cong fst deleted-generator-comparison

  module Words {ℓG : Level} (Gens : Type ℓG) (loops : Gens → q₀ ≡ q₀) where
    module S = SignedWordCoordinates Q q₀ L R s k ε Gens loops
    open S.WithFilling deleted-generator actual-filling public

  private
    module W = Words (q₀ ≡ q₀) (idfun (q₀ ≡ q₀))
  abstract
    deleted-generator-fibre : cong snd deleted-generator
      ≡ emloop (signInt ε Z.· (s Z.- k))
    deleted-generator-fibre = W.actual-fibre

module Coordinates {ℓ : Level} (Q : Type ℓ) (q₀ : Q)
  (L R : q₀ ≡ q₀) (ε : Sign) (s k : ℤ) where
  module D = Diagram Q q₀ L R ε s k
  module Fwd = ForwardGraph Q q₀ L R s k

  β : D.HitTotal → Q × C
  β = D.r ∘ D.to-old .fst

  β-retained : (a : Q) (t : C) → β (inl (incQ a , t)) ≡ (a , t)
  β-retained a t = cong D.r (D.to-old-graph (incQ a) t) ∙ D.unit (a , t)

  module N = NormalizedCoordinates Q q₀ L R ε s k β β-retained

  old-graph : D.oldGraph → Q × C
  old-graph a = D.r (inl (a , 0C))

  -- The actual old generator, with precisely the unit basepoint path.
  deleted-generator : Fwd.point ≡ Fwd.point
  deleted-generator = transport
    (λ i → D.unit (q₀ , 0C) i ≡ D.unit (q₀ , 0C) i) (cong old-graph x)

  abstract
    generator-model-comparison : N.deleted-generator ≡ deleted-generator
    generator-model-comparison = based-circle-homotopy Fwd.point
      (N.graph-map ∘ circleMap x) (old-graph ∘ circleMap x)
      (β-retained q₀ 0C) (D.unit (q₀ , 0C))
      (λ u → cong D.r (D.to-old-graph (circleMap x u) 0C))
      (λ i → compPath-filler'
        (cong D.r (D.to-old-graph (incQ q₀) 0C)) (D.unit (q₀ , 0C)) (~ i))

    actual-filling : ((Fwd.u ∙ power ε deleted-generator) ∙ Fwd.v) ∙ Fwd.h k
      ≡ Fwd.h s
    actual-filling = cong (λ y → ((Fwd.u ∙ power ε y) ∙ Fwd.v) ∙ Fwd.h k)
      (sym generator-model-comparison) ∙ N.actual-filling

    -- The actual old generator AND its relation comparison, together.
    deleted-generator-comparison :
      Path (Σ[ y ∈ (Fwd.point ≡ Fwd.point) ]
        ((Fwd.u ∙ power ε y) ∙ Fwd.v ≡ Fwd.h (s Z.- k)))
        (deleted-generator ,
          Fwd.filling-difference ((Fwd.u ∙ power ε deleted-generator) ∙ Fwd.v)
            actual-filling)
        (Fwd.graph-solution ε , Fwd.graph-solution-fills ε)
    deleted-generator-comparison =
      Fwd.graph-solution-unique ε deleted-generator actual-filling

    deleted-generator-formula : deleted-generator ≡ Fwd.graph-solution ε
    deleted-generator-formula = cong fst deleted-generator-comparison

    retained-loop : (p : q₀ ≡ q₀)
      → transport (λ i → D.unit (q₀ , 0C) i ≡ D.unit (q₀ , 0C) i)
          (cong (λ a → old-graph (incQ a)) p)
        ≡ cong Fwd.graph p
    retained-loop p = fromPathP
      {A = λ i → D.unit (q₀ , 0C) i ≡ D.unit (q₀ , 0C) i}
      {x = cong (λ a → old-graph (incQ a)) p} {y = cong Fwd.graph p}
      (λ i j → D.unit (p j , 0C) i)

    fibre-loop : (n : ℤ)
      → transport (λ i → D.unit (q₀ , 0C) i ≡ D.unit (q₀ , 0C) i)
          (cong (λ t → D.r (inl (incQ q₀ , t))) (emloop n))
        ≡ Fwd.h n
    fibre-loop n = fromPathP
      {A = λ i → D.unit (q₀ , 0C) i ≡ D.unit (q₀ , 0C) i}
      {x = cong (λ t → D.r (inl (incQ q₀ , t))) (emloop n)} {y = Fwd.h n}
      (λ i j → D.unit (q₀ , emloop n j) i)

  module Words {ℓG : Level} (Gens : Type ℓG) (loops : Gens → q₀ ≡ q₀) where
    module S = SignedWordCoordinates Q q₀ L R s k ε Gens loops
    open S.WithFilling deleted-generator actual-filling public

  private
    module W = Words (q₀ ≡ q₀) (idfun (q₀ ≡ q₀))
  abstract
    deleted-generator-fibre : cong snd deleted-generator
      ≡ emloop (signInt ε Z.· (s Z.- k))
    deleted-generator-fibre = W.actual-fibre

record PrimitiveTotalData {ℓ : Level} (Q : Type ℓ) (q₀ : Q)
  (L R : q₀ ≡ q₀) (ε : Sign) (s k : ℤ) : Type ℓ where
  private
    module D = Diagram Q q₀ L R ε s k
  field
    j : Q × C → D.V
    r : D.V → Q × C
    unit : (z : Q × C) → r (j z) ≡ z
    counit : (z : D.V) → j (r z) ≡ z
    j-graph : (a : Q) (t : C) → j (a , t) ≡ inl (incQ a , t)

  abstract
    jEquiv : (Q × C) ≃ D.V
    jEquiv = isoToEquiv (iso j r counit unit)

primitive-total : {ℓ : Level} (Q : Type ℓ) (q₀ : Q)
  (L R : q₀ ≡ q₀) (ε : Sign) (s k : ℤ)
  → PrimitiveTotalData Q q₀ L R ε s k
primitive-total Q q₀ L R ε s k = record
  { j = D.j ; r = D.r ; unit = D.unit ; counit = D.counit
  ; j-graph = λ _ _ → refl }
  where module D = Diagram Q q₀ L R ε s k
