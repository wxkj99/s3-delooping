{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cover.DoubleCoset where

-- Double-coset cover decompositions. The input contains algebraic orbit
-- representatives and stabilizer witnesses, never a topological equivalence.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Algebra.Group.Base hiding (group)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.HITs.EilenbergMacLane1.Base
import Cubical.HITs.EilenbergMacLane1.Properties as EM
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Cover.Cosets public

private variable ℓ ℓR ℓX ℓY : Level

-- A group model for each actual stabilizer, with its two markings.
-- stab-full and the monicity of stabC say precisely that the model is
-- { c : C | t i(c) t⁻¹ lies in H }. The equation avoids inverse conventions.
record DoubleCosetData {H C G : Group ℓ}
  (j : SubgroupEmbedding H G) (i : SubgroupEmbedding C G) : Type (ℓ-suc ℓ) where
  private
    _·_ = GroupStr._·_ (G .snd)
  field
    Rep : Type ℓ
    rep-set : isSet Rep
    repr : Rep → G .fst
    Stab : Rep → Group ℓ
    stabH : (r : Rep) → GroupHom (Stab r) H
    stabC : (r : Rep) → SubgroupEmbedding (Stab r) C
    naturality : (r : Rep) (k : Stab r .fst)
      → hom j .fst (stabH r .fst k) · repr r
        ≡ repr r · hom i .fst (hom (stabC r) .fst k)
    stab-full : (r : Rep) (h : H .fst) (c : C .fst)
      → hom j .fst h · repr r ≡ repr r · hom i .fst c
      → Σ[ k ∈ Stab r .fst ] (stabH r .fst k ≡ h) × (hom (stabC r) .fst k ≡ c)
    separate : (r s : Rep) (h : H .fst) (c : C .fst)
      → hom j .fst h · repr s ≡ repr r · hom i .fst c → r ≡ s
    cover : (g : G .fst)
      → PT.∥ Σ[ r ∈ Rep ] Σ[ h ∈ H .fst ] Σ[ c ∈ C .fst ]
          hom j .fst h · g ≡ repr r · hom i .fst c ∥₁
open DoubleCosetData public

-- Paths in a pullback of groupoids are determined by the two projection
-- paths. The last coordinate is a square in a groupoid, hence a proposition.
PB-path-ext : {A B D : Type ℓ} {f : A → D} {g : B → D}
  (D-groupoid : isGroupoid D) {u v : PB f g} (p q : u ≡ v)
  → cong fst p ≡ cong fst q
  → cong (λ z → z .snd .fst) p ≡ cong (λ z → z .snd .fst) q
  → p ≡ q
PB-path-ext {f = f} {g = g} D-groupoid {u} {v} p q a b k l =
  a k l , b k l , square k l
  where
  square : PathP
    (λ k → PathP (λ l → f (a k l) ≡ g (b k l)) (u .snd .snd) (v .snd .snd))
    (λ l → p l .snd .snd) (λ l → q l .snd .snd)
  square = isProp→PathP
    (λ k → isOfHLevelPathP' 1 (D-groupoid _ _) _ _) _ _

-- Faithfulness of a family of maps over a SET of components. A path in the
-- component index can be straightened uniquely. This is a generic J lemma,
-- kept separate from the large EM₁ expressions below.
module TotalFaithful {R : Type ℓR} (Rset : isSet R)
  {X : R → Type ℓX} {Y : Type ℓY} (f : (r : R) → X r → Y)
  (faithful : (r : R) {x y : X r} (p q : x ≡ y)
    → cong (f r) p ≡ cong (f r) q → p ≡ q) where

  total : Σ R X → Y
  total (r , x) = f r x

  straighten : {r : R} {x y : X r} (p : Path (Σ R X) (r , x) (r , y))
    → Σ[ q ∈ x ≡ y ] p ≡ cong (r ,_) q
  straighten {r} {x} {y} p = q , λ k l → e k l , straighten-fill k l
    where
    e = Rset r r (cong fst p) refl
    family = λ (a : r ≡ r) → PathP (λ l → X (a l)) x y
    q = subst family e (λ l → p l .snd)
    straighten-fill = subst-filler family e (λ l → p l .snd)

  inject : {u v : Σ R X} (p q : u ≡ v)
    → cong total p ≡ cong total q → p ≡ q
  inject {u = u@(r , x)} p = J
    (λ v p → (q : u ≡ v) → cong total p ≡ cong total q → p ≡ q)
    base p
    where
    base : (q : u ≡ u) → refl ≡ cong total q → refl ≡ q
    base q eq = cong (cong (r ,_))
      (faithful r refl (straighten q .fst)
        (eq ∙ cong (cong total) (straighten q .snd)))
      ∙ sym (straighten q .snd)

module ComparisonMap {H C G : Group ℓ}
  (j : SubgroupEmbedding H G) (i : SubgroupEmbedding C G)
  (R : DoubleCosetData j i) where
  private
    module G = GroupStr (G .snd)
    module H = GroupStr (H .snd)
    module C = GroupStr (C .snd)
    jh = hom j
    ih = hom i

  Source : Type ℓ
  Source = Σ[ r ∈ Rep R ] EM₁ (Stab R r)

  Target : Type ℓ
  Target = PB (Bmap jh) (Bmap ih)

  source-groupoid : isGroupoid Source
  source-groupoid = isGroupoidΣ (isSet→isGroupoid (rep-set R)) (λ _ → emsquash)

  target-groupoid : isGroupoid Target
  target-groupoid = isGroupoidΣ emsquash
    (λ _ → isGroupoidΣ emsquash (λ _ → isSet→isGroupoid (emsquash _ _)))

  left : Source → EM₁ H
  left (r , x) = Bmap (stabH R r) x

  right : Source → EM₁ C
  right (r , x) = Bmap (hom (stabC R r)) x

  algebra-square : (h : H .fst) (c : C .fst) (t u : G .fst)
    → jh .fst h G.· u ≡ t G.· ih .fst c
    → Square (emloop t) (emloop u)
        (emloop (jh .fst h)) (emloop (ih .fst c))
  algebra-square h c t u eq = compPath→Square
    (sym (emloop-comp G (jh .fst h) u)
     ∙ cong emloop eq ∙ emloop-comp G t (ih .fst c))

  seam : (z : Source) → Bmap jh (left z) ≡ Bmap ih (right z)
  seam (r , x) = EM.elimSet (Stab R r)
    {B = λ x → Bmap jh (Bmap (stabH R r) x) ≡ Bmap ih (Bmap (hom (stabC R r)) x)}
    (λ _ → emsquash _ _) (emloop (repr R r))
    (λ k → algebra-square (stabH R r .fst k) (hom (stabC R r) .fst k)
      (repr R r) (repr R r) (naturality R r k)) x

  comparison : Source → Target
  comparison z = left z , right z , seam z

  comparison-base : (r : Rep R)
    → comparison (r , embase) ≡ (embase , embase , emloop (repr R r))
  comparison-base r = refl

  -- Read the specific group equation off a pullback path at two basepoints.
  path-equation : {t u : G .fst}
    (p : Path Target (embase , embase , emloop t) (embase , embase , emloop u))
    → jh .fst (loopCode H (cong fst p)) G.· u
      ≡ t G.· ih .fst (loopCode C (cong (λ z → z .snd .fst) p))
  path-equation {t} {u} p = emloop-injective G
    (emloop-comp G _ u
     ∙ cong (_∙ emloop u) (cong (cong (Bmap jh)) (loop-codeLoop H (cong fst p)))
     ∙ Square→compPath (λ k l → p k .snd .snd l)
     ∙ cong (emloop t ∙_) (sym (cong (cong (Bmap ih))
         (loop-codeLoop C (cong (λ z → z .snd .fst) p))))
     ∙ sym (emloop-comp G t _))

  right-faithful : {u v : Source} (p q : u ≡ v)
    → cong right p ≡ cong right q → p ≡ q
  right-faithful = TotalFaithful.inject (rep-set R)
    (λ r → Bmap (hom (stabC R r)))
    (λ r p q → isEmbedding→Inj (Bmap-faithful (stabC R r) _ _) p q)

  comparison-faithful : {u v : Source} (p q : u ≡ v)
    → cong comparison p ≡ cong comparison q → p ≡ q
  comparison-faithful p q eq = right-faithful p q
    (cong (cong (λ z → z .snd .fst)) eq)

  same-base-lift : (r : Rep R)
    (p : comparison (r , embase) ≡ comparison (r , embase))
    → fiber (cong {x = (r , embase)} {y = (r , embase)} comparison) p
  same-base-lift r p = q , PB-path-ext emsquash (cong comparison q) p
    (cong emloop (lifted .snd .fst) ∙ loop-codeLoop H (cong fst p))
    (cong emloop (lifted .snd .snd) ∙ loop-codeLoop C (cong (λ z → z .snd .fst) p))
    where
    lifted = stab-full R r (loopCode H (cong fst p))
      (loopCode C (cong (λ z → z .snd .fst) p)) (path-equation p)
    q : Path Source (r , embase) (r , embase)
    q = cong (r ,_) (emloop (lifted .fst))

  base-lift-along : (r s : Rep R) → r ≡ s
    → (p : comparison (r , embase) ≡ comparison (s , embase))
    → fiber (cong {x = (r , embase)} {y = (s , embase)} comparison) p
  base-lift-along r s e = J
    (λ s e → (p : comparison (r , embase) ≡ comparison (s , embase))
      → fiber (cong {x = (r , embase)} {y = (s , embase)} comparison) p)
    (same-base-lift r) e

  base-lift : (r s : Rep R)
    (p : comparison (r , embase) ≡ comparison (s , embase))
    → fiber (cong {x = (r , embase)} {y = (s , embase)} comparison) p
  base-lift r s p = base-lift-along r s
    (separate R r s (loopCode H (cong fst p))
      (loopCode C (cong (λ z → z .snd .fst) p)) (path-equation p)) p

  base-fully-faithful : (r s : Rep R)
    → isEquiv (cong {x = (r , embase)} {y = (s , embase)} comparison)
  base-fully-faithful r s = isoToIsEquiv (iso
    (cong comparison) (λ p → base-lift r s p .fst)
    (λ p → base-lift r s p .snd)
    (λ q → comparison-faithful _ q (base-lift r s (cong comparison q) .snd)))

  fully-faithful : isEmbedding comparison
  fully-faithful (r , x) (s , y) = EM.elimProp (Stab R r)
    {B = λ x → (y : EM₁ (Stab R s))
      → isEquiv (cong {x = (r , x)} {y = (s , y)} comparison)}
    (λ x → isPropΠ λ y → isPropIsEquiv _)
    (EM.elimProp (Stab R s)
      {B = λ y → isEquiv (cong {x = (r , embase)} {y = (s , y)} comparison)}
      (λ y → isPropIsEquiv _) (base-fully-faithful r s)) x y

  base-surjective : (g : G .fst)
    → PT.∥ fiber comparison (embase , embase , emloop g) ∥₁
  base-surjective g = PT.rec PT.squash₁
    (λ (r , h , c , eq) → PT.∣ (r , embase) ,
      (λ k → emloop h k , emloop c k ,
        algebra-square h c (repr R r) g eq k) ∣₁)
    (cover R g)

  surjective : isSurjection comparison
  surjective (x , y , p) = EM.elimProp H
    {B = λ x → (y : EM₁ C) (p : Bmap jh x ≡ Bmap ih y)
      → PT.∥ fiber comparison (x , y , p) ∥₁}
    (λ x → isPropΠ2 λ y p → PT.squash₁)
    (EM.elimProp C
      {B = λ y → (p : embase ≡ Bmap ih y)
        → PT.∥ fiber comparison (embase , y , p) ∥₁}
      (λ y → isPropΠ λ p → PT.squash₁)
      (λ p → subst (λ q → PT.∥ fiber comparison (embase , embase , q) ∥₁)
        (loop-codeLoop G p) (base-surjective (loopCode G p)))) x y p

  comparison-isEquiv : isEquiv comparison
  comparison-isEquiv = isEmbedding×isSurjection→isEquiv (fully-faithful , surjective)

-- In addition to an equivalence, retain both projection homotopies and the
-- dependent square relating them to the actual BG path. The seam has a
-- specified value emloop t at every component basepoint.
record DoubleCosetComparison {H C G : Group ℓ}
  (j : SubgroupEmbedding H G) (i : SubgroupEmbedding C G)
  (R : DoubleCosetData j i) : Type ℓ where
  private module M = ComparisonMap j i R
  field
    e : M.Source ≃ M.Target
    projectionH : (z : M.Source) → e .fst z .fst ≡ M.left z
    projectionC : (z : M.Source) → e .fst z .snd .fst ≡ M.right z
    path-compatible : (z : M.Source)
      → PathP (λ k → Bmap (hom j) (projectionH z k)
                      ≡ Bmap (hom i) (projectionC z k))
          (e .fst z .snd .snd) (M.seam z)
    base-seam : (r : Rep R) → M.seam (r , embase) ≡ emloop (repr R r)

  -- This is derived from the stored projection tracks AND their square,
  -- so the basepoint claim concerns e itself, not merely an auxiliary map.
  component-base : (r : Rep R)
    → e .fst (r , embase) ≡ (embase , embase , emloop (repr R r))
  component-base r =
    (λ k → projectionH (r , embase) k , projectionC (r , embase) k ,
      path-compatible (r , embase) k)
    ∙ (λ k → embase , embase , base-seam r k)

-- No topological hypotheses are assumed in DoubleCosetData.
doubleCosetPullback : {H C G : Group ℓ}
  (j : SubgroupEmbedding H G) (i : SubgroupEmbedding C G)
  (R : DoubleCosetData j i) → DoubleCosetComparison j i R
DoubleCosetComparison.e (doubleCosetPullback j i R) =
  ComparisonMap.comparison j i R , ComparisonMap.comparison-isEquiv j i R
DoubleCosetComparison.projectionH (doubleCosetPullback j i R) z = refl
DoubleCosetComparison.projectionC (doubleCosetPullback j i R) z = refl
DoubleCosetComparison.path-compatible (doubleCosetPullback j i R) z = refl
DoubleCosetComparison.base-seam (doubleCosetPullback j i R) r = refl

-- Canonical stabilizers. Thus clients need supply only representatives,
-- separation and orbit coverage; they need not invent stabilizer groups.
module CanonicalStabilizer {H C G : Group ℓ}
  (j : SubgroupEmbedding H G) (i : SubgroupEmbedding C G) (t : G .fst) where
  private
    module G = GroupStr (G .snd)
    module H = GroupStr (H .snd)
    module C = GroupStr (C .snd)
    module GT = GroupTheory G
    jh = hom j
    ih = hom i
    module JH = IsGroupHom (jh .snd)
    module IH = IsGroupHom (ih .snd)

  Witness : C .fst → Type ℓ
  Witness c = Σ[ h ∈ H .fst ] jh .fst h G.· t ≡ t G.· ih .fst c

  witness-prop : (c : C .fst) → isProp (Witness c)
  witness-prop c (h , p) (h' , q) = Σ≡Prop (λ _ → G.is-set _ _)
    (mono j (GT.·CancelR t (p ∙ sym q)))

  Carrier : Type ℓ
  Carrier = Σ (C .fst) Witness

  carrier-ext : {x y : Carrier} → x .fst ≡ y .fst → x ≡ y
  carrier-ext = Σ≡Prop witness-prop

  unit : Carrier
  unit = C.1g , H.1g ,
    cong (G._· t) JH.pres1 ∙ G.·IdL t ∙ sym (G.·IdR t)
    ∙ cong (t G.·_) (sym IH.pres1)

  product : Carrier → Carrier → Carrier
  product (c , h , p) (d , k , q) = (c C.· d) , (h H.· k) ,
    cong (G._· t) (JH.pres· h k)
    ∙ sym (G.·Assoc (jh .fst h) (jh .fst k) t)
    ∙ cong (jh .fst h G.·_) q
    ∙ G.·Assoc (jh .fst h) t (ih .fst d)
    ∙ cong (G._· ih .fst d) p
    ∙ sym (G.·Assoc t (ih .fst c) (ih .fst d))
    ∙ cong (t G.·_) (sym (IH.pres· c d))

  inverse-square : (a b : G .fst) → a G.· t ≡ t G.· b
    → G.inv a G.· t ≡ t G.· G.inv b
  inverse-square a b p = GT.·CancelL a
    (G.·Assoc a (G.inv a) t
     ∙ cong (G._· t) (G.·InvR a) ∙ G.·IdL t
     ∙ sym (G.·Assoc a t (G.inv b)
       ∙ cong (G._· G.inv b) p
       ∙ sym (G.·Assoc t b (G.inv b))
       ∙ cong (t G.·_) (G.·InvR b) ∙ G.·IdR t))

  inverse : Carrier → Carrier
  inverse (c , h , p) = C.inv c , H.inv h ,
    cong (G._· t) (JH.presinv h)
    ∙ inverse-square (jh .fst h) (ih .fst c) p
    ∙ cong (t G.·_) (sym (IH.presinv c))

  group : Group ℓ
  group = makeGroup-right unit product inverse
    (isSetΣ C.is-set (λ c → isProp→isSet (witness-prop c)))
    (λ x y z → carrier-ext (C.·Assoc (x .fst) (y .fst) (z .fst)))
    (λ x → carrier-ext (C.·IdR (x .fst)))
    (λ x → carrier-ext (C.·InvR (x .fst)))

  toC : SubgroupEmbedding group C
  hom toC = fst , makeIsGroupHom (λ _ _ → refl)
  mono toC = carrier-ext

  toH : GroupHom group H
  toH = (λ x → x .snd .fst) , makeIsGroupHom (λ _ _ → refl)

  square : (k : group .fst)
    → jh .fst (toH .fst k) G.· t ≡ t G.· ih .fst (hom toC .fst k)
  square k = k .snd .snd

  full : (h : H .fst) (c : C .fst)
    → jh .fst h G.· t ≡ t G.· ih .fst c
    → Σ[ k ∈ group .fst ] (toH .fst k ≡ h) × (hom toC .fst k ≡ c)
  full h c p = (c , h , p) , refl , refl

  -- The square definition really is the subgroup t i(c) t⁻¹ ∈ H
  -- with exactly that conjugation direction.
  conjugate : C .fst → G .fst
  conjugate c = (t G.· ih .fst c) G.· G.inv t

  square→conjugate : (h : H .fst) (c : C .fst)
    → jh .fst h G.· t ≡ t G.· ih .fst c → jh .fst h ≡ conjugate c
  square→conjugate h c p = sym (G.·IdR (jh .fst h))
    ∙ cong (jh .fst h G.·_) (sym (G.·InvR t))
    ∙ G.·Assoc (jh .fst h) t (G.inv t)
    ∙ cong (G._· G.inv t) p

  conjugate→square : (h : H .fst) (c : C .fst)
    → jh .fst h ≡ conjugate c → jh .fst h G.· t ≡ t G.· ih .fst c
  conjugate→square h c p = cong (G._· t) p
    ∙ sym (G.·Assoc (t G.· ih .fst c) (G.inv t) t)
    ∙ cong ((t G.· ih .fst c) G.·_) (G.·InvL t)
    ∙ G.·IdR (t G.· ih .fst c)

  witness≃membership : (c : C .fst) → Witness c ≃ fiber (jh .fst) (conjugate c)
  witness≃membership c = isoToEquiv (iso
    (λ (h , p) → h , square→conjugate h c p)
    (λ (h , p) → h , conjugate→square h c p)
    (λ _ → Σ≡Prop (λ _ → G.is-set _ _) refl)
    (λ _ → Σ≡Prop (λ _ → G.is-set _ _) refl))

  stabilizer≃subgroup : group .fst ≃ (Σ[ c ∈ C .fst ] fiber (jh .fst) (conjugate c))
  stabilizer≃subgroup = Σ-cong-equiv-snd witness≃membership

  conjugation-marking : (k : group .fst)
    → jh .fst (toH .fst k) ≡ conjugate (hom toC .fst k)
  conjugation-marking (c , h , p) = square→conjugate h c p

-- A constructor from only algebraic orbit data, with no stabilizer or
-- delooping obligations left to the caller.
canonicalDoubleCosetData : {H C G : Group ℓ}
  (j : SubgroupEmbedding H G) (i : SubgroupEmbedding C G)
  (Reps : Type ℓ) (setReps : isSet Reps) (t : Reps → G .fst)
  (disjoint : (r s : Reps) (h : H .fst) (c : C .fst)
    → GroupStr._·_ (G .snd) (hom j .fst h) (t s)
      ≡ GroupStr._·_ (G .snd) (t r) (hom i .fst c) → r ≡ s)
  (complete : (g : G .fst)
    → PT.∥ Σ[ r ∈ Reps ] Σ[ h ∈ H .fst ] Σ[ c ∈ C .fst ]
      GroupStr._·_ (G .snd) (hom j .fst h) g
      ≡ GroupStr._·_ (G .snd) (t r) (hom i .fst c) ∥₁)
  → DoubleCosetData j i
Rep (canonicalDoubleCosetData j i Reps setReps t disjoint complete) = Reps
rep-set (canonicalDoubleCosetData j i Reps setReps t disjoint complete) = setReps
repr (canonicalDoubleCosetData j i Reps setReps t disjoint complete) = t
Stab (canonicalDoubleCosetData j i Reps setReps t disjoint complete) r =
  CanonicalStabilizer.group j i (t r)
stabH (canonicalDoubleCosetData j i Reps setReps t disjoint complete) r =
  CanonicalStabilizer.toH j i (t r)
stabC (canonicalDoubleCosetData j i Reps setReps t disjoint complete) r =
  CanonicalStabilizer.toC j i (t r)
naturality (canonicalDoubleCosetData j i Reps setReps t disjoint complete) r =
  CanonicalStabilizer.square j i (t r)
stab-full (canonicalDoubleCosetData j i Reps setReps t disjoint complete) r =
  CanonicalStabilizer.full j i (t r)
separate (canonicalDoubleCosetData j i Reps setReps t disjoint complete) = disjoint
cover (canonicalDoubleCosetData j i Reps setReps t disjoint complete) = complete
