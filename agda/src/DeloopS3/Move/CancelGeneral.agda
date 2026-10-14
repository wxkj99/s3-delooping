{-# OPTIONS --safe --cubical #-}

-- Marked loop--cell cancellation with retained attachments and graph correction.
-- All pushouts are untruncated; markings include the changed seams.
-- The local quotient isomorphism is in ShearFormula.
module DeloopS3.Move.CancelGeneral where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (Square→compPath)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.Data.Sum using (_⊎_) renaming (inl to left; inr to right)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import Cubical.HITs.Pushout.Flattening using (module FlatteningLemma)
open import DeloopS3.Move.CancelMinimalCore
open import DeloopS3.Move.CancelLoopCell
open import DeloopS3.Move.CancelMinimal using (C; K; 0C; 0K; U; Tot; _+C_; mulC; ω; ω-add; module Minimal)
import Cubical.Data.Int as Z
open Z using (ℤ)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (embase; emloop; emsquash; emloop-comp; emloop-sym; emloop-1g)
open import Cubical.HITs.EilenbergMacLane1.Properties using (elimSet)
open import Cubical.HITs.Susp.Base using (Susp)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (-ₖ_; cong₂+₁)
open import Cubical.Homotopy.EilenbergMacLane.Properties using (EM→ΩEM+1-sym)

private
  variable
    ℓA ℓW ℓS ℓD ℓQ ℓB : Level

-- Staging works for any first attaching type W, not only S¹.
module Staging {A : Type ℓA} {W : Type ℓW}
  {S : Type ℓS} {D : Type ℓD}
  (w : W → A) (u : S → A) (b : S → D) where

  all-left : W ⊎ S → A
  all-left (left a) = w a
  all-left (right a) = u a

  all-right : W ⊎ S → Unit ⊎ D
  all-right (left a) = left tt
  all-right (right a) = right (b a)

  Oall = Pushout all-left all-right
  V = Pushout w (λ _ → tt)

  stage-left : S → V
  stage-left = inl ∘ u

  Ostage = Pushout stage-left b

  stage-map : Oall → Ostage
  stage-map (inl a) = inl (inl a)
  stage-map (inr (left tt)) = inl (inr tt)
  stage-map (inr (right d)) = inr d
  stage-map (push (left a) i) = inl (push a i)
  stage-map (push (right a) i) = push a i

  unstage-vertex : V → Oall
  unstage-vertex (inl a) = inl a
  unstage-vertex (inr tt) = inr (left tt)
  unstage-vertex (push a i) = push (left a) i

  unstage : Ostage → Oall
  unstage (inl v) = unstage-vertex v
  unstage (inr d) = inr (right d)
  unstage (push a i) = push (right a) i

  stage-unstage-vertex : (v : V) → stage-map (unstage-vertex v) ≡ inl v
  stage-unstage-vertex (inl a) = refl
  stage-unstage-vertex (inr tt) = refl
  stage-unstage-vertex (push a i) = refl

  stage-unstage : (z : Ostage) → stage-map (unstage z) ≡ z
  stage-unstage (inl v) = stage-unstage-vertex v
  stage-unstage (inr d) = refl
  stage-unstage (push a i) = refl

  unstage-stage : (z : Oall) → unstage (stage-map z) ≡ z
  unstage-stage (inl a) = refl
  unstage-stage (inr (left tt)) = refl
  unstage-stage (inr (right d)) = refl
  unstage-stage (push (left a) i) = refl
  unstage-stage (push (right a) i) = refl

  stage : Oall ≃ Ostage
  stage = isoToEquiv (iso stage-map unstage stage-unstage unstage-stage)

-- Span invariance retains the binary-composite seam
-- rather than replacing it with a constant path.
module ReplaceLeft {V : Type ℓA} {Q : Type ℓQ}
  {S : Type ℓS} {D : Type ℓD}
  (j : Q ≃ V) (r : V → Q) (H : (v : V) → j .fst (r v) ≡ v)
  (u : S → V) (b : S → D) where

  u′ : S → Q
  u′ = r ∘ u

  Ostage = Pushout u b
  O′ = Pushout u′ b

  F : O′ → Ostage
  F (inl q) = inl (j .fst q)
  F (inr d) = inr d
  F (push a i) = (cong inl (H (u a)) ∙ push a) i

  private
    spanEquiv : O′ ≃ Ostage
    spanEquiv = pushoutEquiv u′ b u b (idEquiv S) j (idEquiv D)
      (funExt (H ∘ u)) refl

    span-map-agrees : (z : O′) → spanEquiv .fst z ≡ F z
    span-map-agrees (inl q) = refl
    span-map-agrees (inr d) = refl
    span-map-agrees (push a i) k =
      sym (leftright (cong inl (H (u a))) (push a)) k i

  F-isEquiv : isEquiv F
  F-isEquiv = subst isEquiv (funExt span-map-agrees) (spanEquiv .snd)

  FEquiv : O′ ≃ Ostage
  FEquiv = F , F-isEquiv

  module Marking {B : Type ℓB} (m : Ostage → B) where
    m₀ : V → B
    m₀ = m ∘ inl

    mD : D → B
    mD = m ∘ inr

    mQ : Q → B
    mQ = m₀ ∘ j .fst

    τ : (a : S) → m₀ (u a) ≡ mD (b a)
    τ a = cong m (push a)

    τ′ : (a : S) → mQ (u′ a) ≡ mD (b a)
    τ′ a = cong m₀ (H (u a)) ∙ τ a

    m′ : O′ → B
    m′ = m ∘ F

    -- This equality is a coherent function of a. Its circle instances
    -- supply the cubes, not just equalities of fundamental-group values.
    seam-formula : (a : S) → cong m′ (push a) ≡ τ′ a
    seam-formula a = cong-∙ m (cong inl (H (u a))) (push a)

    rec-mark : O′ → B
    rec-mark (inl q) = mQ q
    rec-mark (inr d) = mD d
    rec-mark (push a i) = τ′ a i

    rec-mark-agrees : m′ ≡ rec-mark
    rec-mark-agrees k (inl q) = mQ q
    rec-mark-agrees k (inr d) = mD d
    rec-mark-agrees k (push a i) = seam-formula a k i

    marked-replacement : EquivOver m′ m
    marked-replacement = FEquiv , λ _ → refl

    -- The forward graph correction is the inverse of the
    -- counit correction occurring in the new seam.
    β : (a : S) → m₀ (u a) ≡ mQ (u′ a)
    β a = sym (cong m₀ (H (u a)))

    graph-sign-correction : (a : S) → τ′ a ≡ sym (β a) ∙ τ a
    graph-sign-correction a = refl

module General (Q : Type ℓQ) (q : Q) (L R : q ≡ q) (ε : Sign)
  {S : Type ℓS} {D : Type ℓD}
  (u : S → AddLoop Q q) (b : S → D) where

  module P = PrimitiveCancellation Q q L R ε
  module T = Staging (circleMap P.w) u b
  module Rpl = ReplaceLeft P.jEquiv P.r (λ v i → P.H i v) (inl ∘ u) b

  open T public using (Oall; Ostage; stage)
  open Rpl public using (u′; O′; F; F-isEquiv; FEquiv)

  cancel-all : O′ ≃ Oall
  cancel-all = compEquiv FEquiv (invEquiv stage)

  marked-primitive-cancel : {B : Type ℓB} (m : Oall → B)
    → Σ[ m′ ∈ (O′ → B) ] EquivOver m′ m
  marked-primitive-cancel m = (m ∘ cancel-all .fst) , cancel-all , λ _ → refl

  module AllMarkings {B : Type ℓB} (m : Oall → B) where
    open Rpl.Marking (m ∘ T.unstage) public

    -- The surviving graph and every other component are unchanged,
    -- not merely equivalent after forgetting their markings.
    retained-graph : (a : Q) → m′ (inl a) ≡ m (inl (incQ a))
    retained-graph a = refl

    retained-component : (d : D) → m′ (inr d) ≡ m (inr (right d))
    retained-component d = refl

    marked-all : EquivOver m′ m
    marked-all = cancel-all , λ _ → refl

    total-all : (U : B → Type ℓA)
      → Σ O′ (U ∘ m′) ≃ Σ Oall (U ∘ m)
    total-all U = Σ-over-equiv U marked-all

-- Coordinate evaluation uses actual maps C → C. The EM₁
-- set-valued eliminator retains the loop squares and fills only the
-- higher comparisons forced by the groupoid truncation of C.
module CircleCoordinates where
  -C_ : C → C
  -C_ = -ₖ_ {G = ℤAbGroup} {n = 1}

  mulC-compose : (s m : ℤ) (a : C)
    → mulC s (mulC m a) ≡ mulC (s Z.· m) a
  mulC-compose s m = elimSet ℤGroup (λ _ → emsquash _ _) refl
    (λ g i j → emloop (Z.·Assoc s m g j) i)

  mulC-negate : (s : ℤ) (a : C) → mulC (Z.- s) a ≡ -C mulC s a
  mulC-negate s = elimSet ℤGroup (λ _ → emsquash _ _) refl
    (λ g i j → (cong emloop (sym (Z.-DistL· s g))
      ∙ emloop-sym ℤGroup (s Z.· g)) j i)

  mulC-add : (s t : ℤ) (a : C)
    → mulC (s Z.+ t) a ≡ mulC s a +C mulC t a
  mulC-add s t = elimSet ℤGroup (λ _ → emsquash _ _) refl
    (λ g i j → (cong emloop (Z.·DistL+ s t g)
      ∙ emloop-comp ℤGroup (s Z.· g) (t Z.· g)
      ∙ sym (cong₂+₁ {G = ℤAbGroup} (emloop (s Z.· g)) (emloop (t Z.· g)))) j i)

  circle-coordinate : (s t m : ℤ) (a : C)
    → (-C mulC s (mulC m a)) +C mulC t a
      ≡ mulC (t Z.- (m Z.· s)) a
  circle-coordinate s t m a =
    cong (λ z → (-C z) +C mulC t a) (mulC-compose s m a)
    ∙ cong (_+C mulC t a) (sym (mulC-negate (s Z.· m) a))
    ∙ sym (mulC-add (Z.- (s Z.· m)) t a)
    ∙ cong (λ z → mulC z a)
        (Z.+Comm (Z.- (s Z.· m)) t
          ∙ cong (λ z → t Z.+ (Z.- z)) (Z.·Comm s m))

  clutching-coordinate : (s t m : ℤ) (a : C)
    → sym (ω .fst (mulC s (mulC m a))) ∙ ω .fst (mulC t a)
      ≡ ω .fst (mulC (t Z.- (m Z.· s)) a)
  clutching-coordinate s t m a =
    cong (_∙ ω .fst (mulC t a))
      (sym (EM→ΩEM+1-sym {G = ℤAbGroup} 1 (mulC s (mulC m a))))
    ∙ sym (ω-add (-C mulC s (mulC m a)) (mulC t a))
    ∙ cong (ω .fst) (circle-coordinate s t m a)

-- Second-cap calculation. Neither the changed seam nor its degree
-- is inferred from the unmarked base or from a group presentation.
module TwoCap (s t m : ℤ) where
  module M = Minimal s
  module N = Minimal t
  module T = Staging (idfun C) (mulC m) (λ _ → tt)

  O₂ = T.Oall

  c₂ : O₂ → K
  c₂ (inl a) = 0K
  c₂ (inr (left tt)) = 0K
  c₂ (inr (right tt)) = 0K
  c₂ (push (left a) i) = M.αₛ a i
  c₂ (push (right a) i) = N.αₛ a i

  capEquiv : Unit ≃ T.V
  capEquiv = isoToEquiv (iso (λ _ → M.v) (λ _ → tt)
    (λ v → sym (M.h v)) (λ _ → refl))

  module Rpl = ReplaceLeft capEquiv (λ _ → tt) (λ v → sym (M.h v))
    T.stage-left (λ _ → tt)

  reduced-base : Rpl.O′ ≃ Susp C
  reduced-base = PushoutSusp≃Susp

  two-cap-base : O₂ ≃ Susp C
  two-cap-base = compEquiv T.stage (compEquiv (invEquiv Rpl.FEquiv) reduced-base)

  module Mark = Rpl.Marking (c₂ ∘ T.unstage)

  reduced-seam : (a : C)
    → Mark.τ′ a ≡ sym (M.αₛ (mulC m a)) ∙ N.αₛ a
  reduced-seam a = refl

  e : ℤ
  e = t Z.- (m Z.· s)

  -- An actual homotopy from the corrected clutching map to its coordinate form.
  remaining-shear : (a : C) → Mark.τ′ a ≡ ω .fst (mulC e a)
  remaining-shear a = CircleCoordinates.clutching-coordinate s t m a

  normalized-mark : Rpl.O′ → K
  normalized-mark (inl tt) = 0K
  normalized-mark (inr tt) = 0K
  normalized-mark (push a i) = ω .fst (mulC e a) i

  seam-normalization : Mark.rec-mark ≡ normalized-mark
  seam-normalization j (inl tt) = 0K
  seam-normalization j (inr tt) = 0K
  seam-normalization j (push a i) = remaining-shear a j i

  marking-normalization : Mark.m′ ≡ normalized-mark
  marking-normalization = Mark.rec-mark-agrees ∙ seam-normalization

  cancel-two-cap : Rpl.O′ ≃ O₂
  cancel-two-cap = compEquiv Rpl.FEquiv (invEquiv T.stage)

  two-cap-marked : EquivOver normalized-mark c₂
  two-cap-marked = cancel-two-cap , λ z → funExt⁻ (sym marking-normalization) z

  two-cap-total : Tot normalized-mark ≃ Tot c₂
  two-cap-total = Σ-over-equiv U two-cap-marked

  -- The final total diagram, literally C ←[0,1] C×C →[e,1] C.
  module E = Minimal e
  module Flat = FlatteningLemma (λ (_ : C) → tt) (λ (_ : C) → tt)
    (λ _ → C) (λ _ → C) E.rotₛ

  final-total = Pushout (snd {A = C} {B = λ _ → C}) E.bₛ

  private
    flatten-chart : Pushout Flat.Σf Flat.Σg ≃ final-total
    flatten-chart = isoToEquiv (iso f g fg gf)
      where
      f : Pushout Flat.Σf Flat.Σg → final-total
      f (inl (tt , t)) = inl t
      f (inr (tt , t)) = inr t
      f (push z i) = push z i

      g : final-total → Pushout Flat.Σf Flat.Σg
      g (inl t) = inl (tt , t)
      g (inr t) = inr (tt , t)
      g (push z i) = push z i

      fg : (z : final-total) → f (g z) ≡ z
      fg (inl t) = refl
      fg (inr t) = refl
      fg (push z i) = refl

      gf : (z : Pushout Flat.Σf Flat.Σg) → g (f z) ≡ z
      gf (inl (tt , t)) = refl
      gf (inr (tt , t)) = refl
      gf (push z i) = refl

  family-two-cap : (z : Rpl.O′) → Flat.E z ≃ U (normalized-mark z)
  family-two-cap (inl tt) = ω
  family-two-cap (inr tt) = ω
  family-two-cap (push a i) = ua-equiv-family (E.rotₛ a)
    (λ i → U (ω .fst (mulC e a) i)) ω ω
    (λ t → toPathP (sym (E.seam-naturality a t))) i

  total-two-cap-diagram : Tot normalized-mark ≃ final-total
  total-two-cap-diagram = compEquiv
    (invEquiv (Σ-cong-equiv-snd family-two-cap))
    (compEquiv Flat.flatten flatten-chart)

  original-total-diagram : Tot c₂ ≃ final-total
  original-total-diagram = compEquiv (invEquiv two-cap-total) total-two-cap-diagram

-- Solve the actual filling path. Centrality below is supplied
-- by the product-path square, not by a presentation-group assertion.
module GraphPathAlgebra where
  right-solve : {X : Type ℓA} {a : X} (w k s : a ≡ a)
    → w ∙ k ≡ s → w ≡ s ∙ sym k
  right-solve w k s filling = rUnit w
    ∙ cong (w ∙_) (sym (rCancel k))
    ∙ assoc w k (sym k)
    ∙ cong (_∙ sym k) filling

  solve-plus-central : {X : Type ℓA} {a : X} (u v z : a ≡ a)
    → z ∙ v ≡ v ∙ z
    → (u ∙ ((sym u ∙ sym v) ∙ z)) ∙ v ≡ z
  solve-plus-central u v z commute =
    cong (_∙ v) (assoc u (sym u ∙ sym v) z)
    ∙ sym (assoc (u ∙ (sym u ∙ sym v)) z v)
    ∙ cong ((u ∙ (sym u ∙ sym v)) ∙_) commute
    ∙ assoc (u ∙ (sym u ∙ sym v)) v z
    ∙ cong (_∙ z) (solve-plus u v)
    ∙ sym (lUnit z)

  solve-minus-central : {X : Type ℓA} {a : X} (u v z : a ≡ a)
    → z ∙ v ≡ v ∙ z
    → z ∙ sym (v ∙ u) ≡ sym (v ∙ u) ∙ z
    → (u ∙ sym ((v ∙ u) ∙ sym z)) ∙ v ≡ z
  solve-minus-central u v z commute commute-inverse =
    cong (λ p → (u ∙ p) ∙ v)
      (symDistr (v ∙ u) (sym z)
        ∙ commute-inverse
        ∙ cong (_∙ z) (symDistr v u))
    ∙ solve-plus-central u v z commute

  -- The two parameters of the square are independent graph/fibre paths.
  product-commute : {X : Type ℓA} {Y : Type ℓB} {a : X} {b : Y}
    (p : a ≡ a) (q : b ≡ b)
    → (λ i → p i , b) ∙ (λ i → a , q i)
      ≡ (λ i → a , q i) ∙ (λ i → p i , b)
  product-commute p q = Square→compPath (λ i j → p i , q j)

module ForwardGraph (Q : Type ℓQ) (q : Q) (L R : q ≡ q) (s k : ℤ) where
  open GraphPathAlgebra

  point : Q × C
  point = q , 0C

  graph : Q → Q × C
  graph a = a , 0C

  fibre : C → Q × C
  fibre a = q , a

  u v : point ≡ point
  u = cong graph L
  v = cong graph R

  h : ℤ → point ≡ point
  h n = cong fibre (emloop n)

  h-add : (a b : ℤ) → h (a Z.+ b) ≡ h a ∙ h b
  h-add a b = cong (cong fibre) (emloop-comp ℤGroup a b)
    ∙ cong-∙ fibre (emloop a) (emloop b)

  h-negate : (a : ℤ) → h (Z.- a) ≡ sym (h a)
  h-negate a = cong (cong fibre) (emloop-sym ℤGroup a)

  δ : ℤ
  δ = s Z.- k

  filling-difference : (w : point ≡ point) → w ∙ h k ≡ h s → w ≡ h δ
  filling-difference w filling = right-solve w (h k) (h s) filling
    ∙ cong (h s ∙_) (sym (h-negate k))
    ∙ sym (h-add s (Z.- k))

  graph-solution : Sign → point ≡ point
  graph-solution plus = (sym u ∙ sym v) ∙ h δ
  graph-solution minus = (v ∙ u) ∙ sym (h δ)

  private
    commute-v : h δ ∙ v ≡ v ∙ h δ
    commute-v = sym (product-commute R (emloop δ))

    inverse-word : sym (v ∙ u) ≡ cong graph (sym (R ∙ L))
    inverse-word = cong sym (sym (cong-∙ graph R L))

    commute-inverse : h δ ∙ sym (v ∙ u) ≡ sym (v ∙ u) ∙ h δ
    commute-inverse = cong (h δ ∙_) inverse-word
      ∙ sym (product-commute (sym (R ∙ L)) (emloop δ))
      ∙ cong (_∙ h δ) (sym inverse-word)

  graph-solution-fills : (ε : Sign)
    → (u ∙ power ε (graph-solution ε)) ∙ v ≡ h δ
  graph-solution-fills plus = solve-plus-central u v (h δ) commute-v
  graph-solution-fills minus = solve-minus-central u v (h δ) commute-v commute-inverse

  -- Equality in the full fibre retains its dependent relation comparison
  -- (the cell cube).
  graph-solution-unique : (ε : Sign) (x : point ≡ point)
    (filling : ((u ∙ power ε x) ∙ v) ∙ h k ≡ h s)
    → Path (Σ[ y ∈ (point ≡ point) ] ((u ∙ power ε y) ∙ v ≡ h δ))
        (x , filling-difference ((u ∙ power ε x) ∙ v) filling)
        (graph-solution ε , graph-solution-fills ε)
  graph-solution-unique ε y filling =
    sym (contract .snd (y , filling-difference ((u ∙ power ε y) ∙ v) filling))
    ∙ contract .snd (graph-solution ε , graph-solution-fills ε)
    where
    contract = ΦEquiv point u v ε .snd .equiv-proof (h δ)

  forward-graph-formula : (ε : Sign) (x : point ≡ point)
    → ((u ∙ power ε x) ∙ v) ∙ h k ≡ h s
    → x ≡ graph-solution ε
  forward-graph-formula ε y filling = cong fst (graph-solution-unique ε y filling)

  solution-fibre-plus : cong snd (graph-solution plus) ≡ emloop δ
  solution-fibre-plus = cong-∙ snd (sym u ∙ sym v) (h δ)
    ∙ cong (_∙ emloop δ) (cong-∙ snd (sym u) (sym v) ∙ sym (lUnit refl))
    ∙ sym (lUnit (emloop δ))

  solution-fibre-minus : cong snd (graph-solution minus) ≡ emloop (Z.- δ)
  solution-fibre-minus = cong-∙ snd (v ∙ u) (sym (h δ))
    ∙ cong (_∙ sym (emloop δ)) (cong-∙ snd v u ∙ sym (lUnit refl))
    ∙ sym (lUnit (sym (emloop δ)))
    ∙ sym (emloop-sym ℤGroup δ)

-- Induction on words. This syntax records concatenation and
-- reversal explicitly, and does not quotient or truncate the graph.
data GraphWord (G : Type ℓA) : Type ℓA where
  emptyWord : GraphWord G
  surviving : G → GraphWord G
  eliminated : GraphWord G
  concatWord : GraphWord G → GraphWord G → GraphWord G
  reverseWord : GraphWord G → GraphWord G

exponent-x : {G : Type ℓA} → GraphWord G → ℤ
exponent-x emptyWord = Z.pos 0
exponent-x (surviving a) = Z.pos 0
exponent-x eliminated = Z.pos 1
exponent-x (concatWord v w) = exponent-x v Z.+ exponent-x w
exponent-x (reverseWord v) = Z.- exponent-x v

signInt : Sign → ℤ
signInt plus = Z.pos 1
signInt minus = Z.negsuc 0

module WordCoordinates (Q : Type ℓQ) (q : Q) (G : Type ℓA)
  (loops : G → q ≡ q)
  (replacement : Path (Q × C) (q , 0C) (q , 0C))
  (κ : ℤ) (replacement-fibre : cong snd replacement ≡ emloop κ) where

  eval : GraphWord G → Path (Q × C) (q , 0C) (q , 0C)
  eval emptyWord = refl
  eval (surviving a) = cong (λ z → z , 0C) (loops a)
  eval eliminated = replacement
  eval (concatWord v w) = eval v ∙ eval w
  eval (reverseWord v) = sym (eval v)

  κgraph : GraphWord G → ℤ
  κgraph v = exponent-x v Z.· κ

  word-fibre-winding : (v : GraphWord G) → cong snd (eval v) ≡ emloop (κgraph v)
  word-fibre-winding emptyWord = sym (emloop-1g ℤGroup)
  word-fibre-winding (surviving a) = sym (emloop-1g ℤGroup)
  word-fibre-winding eliminated = replacement-fibre
  word-fibre-winding (concatWord v w) = cong-∙ snd (eval v) (eval w)
    ∙ cong₂ _∙_ (word-fibre-winding v) (word-fibre-winding w)
    ∙ sym (emloop-comp ℤGroup (κgraph v) (κgraph w))
    ∙ cong emloop (sym (Z.·DistL+ (exponent-x v) (exponent-x w) κ))
  word-fibre-winding (reverseWord v) = cong sym (word-fibre-winding v)
    ∙ sym (emloop-sym ℤGroup (κgraph v))
    ∙ cong emloop (Z.-DistL· (exponent-x v) κ)

  -- A pre-existing lift exponent is retained, not overwritten.
  lifted-word-winding : (v : GraphWord G) (kᵥ : ℤ)
    → cong snd (eval v ∙ cong (λ z → q , z) (emloop kᵥ))
      ≡ emloop (kᵥ Z.+ κgraph v)
  lifted-word-winding v kᵥ = cong-∙ snd (eval v) (cong (λ z → q , z) (emloop kᵥ))
    ∙ cong (_∙ emloop kᵥ) (word-fibre-winding v)
    ∙ sym (emloop-comp ℤGroup (κgraph v) kᵥ)
    ∙ cong emloop (Z.+Comm (κgraph v) kᵥ)

module SignedWordCoordinates (Q : Type ℓQ) (q : Q) (L R : q ≡ q)
  (s k : ℤ) (ε : Sign) (G : Type ℓA) (loops : G → q ≡ q) where
  module Fwd = ForwardGraph Q q L R s k

  private
    signed-fibre : (σ : Sign)
      → cong snd (Fwd.graph-solution σ) ≡ emloop (signInt σ Z.· Fwd.δ)
    signed-fibre plus = Fwd.solution-fibre-plus
    signed-fibre minus = Fwd.solution-fibre-minus

  -- Apply this to the actual image y of the deleted generator and its
  -- filling path. The comparison uses the full contractible fibre above.
  module WithFilling (y : Fwd.point ≡ Fwd.point)
    (filling : ((Fwd.u ∙ power ε y) ∙ Fwd.v) ∙ Fwd.h k ≡ Fwd.h s) where

    actual-fibre : cong snd y ≡ emloop (signInt ε Z.· Fwd.δ)
    actual-fibre = cong (cong snd) (Fwd.forward-graph-formula ε y filling)
      ∙ signed-fibre ε

    module W = WordCoordinates Q q G loops y (signInt ε Z.· Fwd.δ) actual-fibre
    open W public

    signed-substitution : (v : GraphWord G)
      → κgraph v ≡ (exponent-x v Z.· signInt ε) Z.· (s Z.- k)
    signed-substitution v = Z.·Assoc (exponent-x v) (signInt ε) (s Z.- k)

    signed-word-winding : (v : GraphWord G)
      → cong snd (eval v) ≡ emloop ((exponent-x v Z.· signInt ε) Z.· (s Z.- k))
    signed-word-winding v = word-fibre-winding v ∙ cong emloop (signed-substitution v)
