{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- Charts and based-loop adapters for the inversion total, retaining Base.fA.
module DeloopS3.Seifert.MarkedSeifert.DescentChart where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt)
open import Cubical.Data.Bool using (Bool; false; true; not; _⊕_; isSetBool)
open import Cubical.Data.NatMinusOne
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import Cubical.HITs.Pushout.Flattening using (module FlatteningLemma)
open import Cubical.HITs.RPn.Base using (RP; cov⁻¹; Bool*)
open import Cubical.HITs.S1.Base using (S¹; base; loop; invS¹Equiv)
open import Cubical.HITs.S1.Properties using (isConnectedS¹; isGroupoidS¹)
open import Cubical.HITs.EilenbergMacLane1.Base using (embase)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Move.CancelMinimal using (C; 0C; T²; ua-equiv-family)
open import DeloopS3.Cover.Orientation.CircleModel
  using (S¹≃C; circleToC; CToCircle; circle-section; circle-retraction; hC)
open import DeloopS3.Seifert.TwistedBundle.SignCircle
open import DeloopS3.Seifert.TwistedBundle.Base
  using (R; A; w₁; pr₁; δ; δ-invol; fA; Ksign; λA)
import DeloopS3.Seifert.TwistedBundle.Chart as Ch
import DeloopS3.Seifert.TwistedBundle.FrameSign as FS
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.TorusMap
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary
  using (based; based-refl; based-comp; based-square; uT; vT)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third using (cong-based)
open import DeloopS3.Seifert.MarkedSeifert.Final using (DescentChart; λsign)

-- Generic adapters, before specializing the descended family.
opaque
  Σ-path-faithful : ∀ {ℓ ℓ′} {X : Type ℓ} {P : X → Type ℓ′}
    → ((x : X) → isSet (P x))
    → {u v : Σ X P} (p q : u ≡ v)
    → cong fst p ≡ cong fst q → p ≡ q
  Σ-path-faithful {P = P} sets {u = u} {v = v} p q e j i = e j i ,
    isSet→SquareP {A = λ i j → P (e j i)} (λ i j → sets (e j i))
      (λ _ → u .snd) (λ _ → v .snd)
      (λ i → p i .snd) (λ i → q i .snd) i j

  based-chain : ∀ {ℓ} {X : Type ℓ} {x y z : X}
    (p : x ≡ y) (q : y ≡ z) (l : x ≡ x)
    → based (p ∙ q) l ≡ based q (based p l)
  based-chain p q l = J
    (λ z q → based (p ∙ q) l ≡ based q (based p l))
    (cong (λ v → based v l) (sym (rUnit p))
      ∙ sym (based-refl (based p l))) q

  refl-square : ∀ {ℓ} {X : Type ℓ} {x y : X}
    (p q : x ≡ y) → p ≡ q → Square refl refl p q
  refl-square p q e = compPath→Square
    (sym (rUnit p) ∙ e ∙ lUnit q)

  naturality : ∀ {ℓ ℓ′} {X : Type ℓ} {Y : Type ℓ′}
    {f g : X → Y} (h : (x : X) → f x ≡ g x)
    {x y : X} (p : x ≡ y)
    → cong f p ∙ h y ≡ h x ∙ cong g p
  naturality h p = Square→compPath (λ i j → h (p i) j)

-- Prepending is proved before specializing transport to the descended EM family.
opaque
  prepend-dependent : ∀ {ℓ} (P : I → Type ℓ)
    (x y : P i0) (z : P i1) → x ≡ y → PathP P y z → PathP P x z
  prepend-dependent P x y z p q = toPathP
    (cong (transport (λ i → P i)) p ∙ fromPathP q)

opaque
  inverse-frame-seam : ∀ {ℓR ℓS ℓP ℓY} {R₀ : Type ℓR}
    (S : R₀ → Type ℓS) (P : R₀ → Type ℓP) {Y : Type ℓY}
    (d : (x : R₀) → S x → S x)
    (H : (a : Σ R₀ S) → (a .fst , d (a .fst) (a .snd)) ≡ a)
    (f : (x : R₀) → S x → Y → P x) (g : Y → Y)
    (swap : (x : R₀) (y : S x) (u : Y) → f x (d x y) (g u) ≡ f x y u)
    (a : Σ R₀ S) (u : Y)
    → PathP (λ i → P (H a i .fst))
      (f (a .fst) (a .snd) u) (f (a .fst) (a .snd) (g u))
  inverse-frame-seam S P d H f g swap a u = prepend-dependent
    (λ i → P (H a i .fst))
    (f (a .fst) (a .snd) u)
    (f (a .fst) (d (a .fst) (a .snd)) (g u))
    (f (a .fst) (a .snd) (g u))
    (sym (swap (a .fst) (a .snd) u))
    (λ i → f (H a i .fst) (H a i .snd) (g u))

-- The circle eliminator is kept generic; no specialized PathP
-- formation for the descended EM family is needed in its loop clause.
module InverseFrameChart {R₀ : Type₀} (S P : R₀ → Type₀) {Y : Type₀}
  (e : Y ≃ Y) (d : (x : R₀) → S x → S x)
  (H : (a : Σ R₀ S) → (a .fst , d (a .fst) (a .snd)) ≡ a)
  (frame : (x : R₀) → S x → Y ≃ P x)
  (swap : (x : R₀) (y : S x) (u : Y)
    → frame x (d x y) .fst (e .fst u) ≡ frame x y .fst u) where

  source : S¹ → Type₀
  source base = Y
  source (loop i) = ua e i

  baseCircle : Σ R₀ S → S¹ → R₀
  baseCircle a base = a .fst
  baseCircle a (loop i) = H a i .fst

  opaque
    loopChart : (a : Σ R₀ S)
      → PathP (λ i → ua e i ≃ P (H a i .fst))
        (frame (a .fst) (a .snd)) (frame (a .fst) (a .snd))
    loopChart a = ua-equiv-family e (λ k → P (H a k .fst))
      (frame (a .fst) (a .snd)) (frame (a .fst) (a .snd))
      (inverse-frame-seam S P d H (λ x y → frame x y .fst) (e .fst) swap a)

  family : (a : Σ R₀ S) (b : S¹) → source b ≃ P (baseCircle a b)
  family a base = frame (a .fst) (a .snd)
  family a (loop i) = loopChart a i

-- Keep both endpoint families explicit before specializing a total chart.
module TotalChart {ℓX ℓY ℓP ℓQ}
  {X : Type ℓX} {Y : Type ℓY} {P : X → Type ℓP} {Q : Y → Type ℓQ}
  (e : X ≃ Y) (f : (x : X) → P x ≃ Q (e .fst x)) where

  map : Σ X P → Σ Y Q
  map (x , u) = e .fst x , f x .fst u

  opaque
    map-isEquiv : isEquiv map
    map-isEquiv = compEquiv
      {A = Σ X P} {B = Σ X (λ x → Q (e .fst x))} {C = Σ Y Q}
      (Σ-cong-equiv-snd {A = X} {B = P} {B' = λ x → Q (e .fst x)} f)
      (Σ-cong-equiv-fst {B = Q} e) .snd

  equivalence : Σ X P ≃ Σ Y Q
  equivalence = map , map-isEquiv

-- The literal two-edge RP 1, with the prescribed positive loop.
rCircle : S¹ → R
rCircle base = pr₁ Ch.L₀
rCircle (loop i) = Ch.t i

private
  rInverse : R → S¹
  rInverse (inl (inr tt)) = base
  rInverse (inr tt) = base
  rInverse (push (inr tt , false) i) = base
  rInverse (push (inr tt , true) i) = loop (~ i)

  rInverse-loop : cong rInverse Ch.t ≡ loop
  rInverse-loop = cong-∙ rInverse (Ch.a false) (sym (Ch.a true))
    ∙ sym (lUnit loop)

  r-section : (x : R) → rCircle (rInverse x) ≡ x
  r-section (inl (inr tt)) = refl
  r-section (inr tt) = Ch.a false
  r-section (push (inr tt , false) i) = compPath→Square
    {p = refl} {q = Ch.a false} {r = refl} {s = Ch.a false} refl i
  r-section (push (inr tt , true) i) = compPath→Square
    (cong (_∙ Ch.a false) (symDistr (Ch.a false) (sym (Ch.a true)))
      ∙ compPathr-cancel (Ch.a false) (Ch.a true)
      ∙ lUnit (Ch.a true)) i

  r-retraction : (x : S¹) → rInverse (rCircle x) ≡ x
  r-retraction base = refl
  r-retraction (loop i) = refl-square (cong rInverse Ch.t) loop rInverse-loop i

opaque
  rCircle-isEquiv : isEquiv rCircle
  rCircle-isEquiv = isoToIsEquiv (iso rCircle rInverse r-section r-retraction)

  R-groupoid : isGroupoid R
  R-groupoid = isOfHLevelRespectEquiv 3 (rCircle , rCircle-isEquiv) isGroupoidS¹

  Ksign-groupoid : isGroupoid Ksign
  Ksign-groupoid = isOfHLevelΣ 3 R-groupoid (sign-groupoid ∘ w₁)

-- Finite graph normalization, retaining the specified four edges.
private
  left₄ right₄ : Bool × Bool → Bool
  left₄ = snd
  right₄ (y , z) = y ⊕ z

G₄ : Type₀
G₄ = Pushout left₄ right₄

g₄ : G₄ → A
g₄ (inl z) = Ch.L z
g₄ (inr z) = Ch.Rv z
g₄ (push (y , z) i) = Ch.E y z i

private
  module Flat = FlatteningLemma
    (λ (a : Σ (RP 0) (λ x → fst (cov⁻¹ 0 x))) → fst a)
    (λ _ → tt)
    (λ x → fst (cov⁻¹ 0 x)) (λ (_ : Unit) → Bool)
    (λ a → frame (cov⁻¹ 0 (fst a)) (snd a))

  cover≃Flat : (x : R) → fst (w₁ x) ≃ Flat.E x
  cover≃Flat (inl x) = idEquiv _
  cover≃Flat (inr x) = idEquiv _
  cover≃Flat (push a i) = idEquiv _

  fromFlat : Σ R Flat.E → A
  fromFlat (x , z) = x , invEq (cover≃Flat x) z

  flatEdge : (y z : Bool) → Ch.L z ≡ Ch.Rv (frame Bool* y .fst z)
  flatEdge y z = cong (fromFlat ∘ Flat.FlattenIso.fwd) (push ((inr tt , y) , z))

  -- The private adapter in Chart is copied, not assumed exported.
  E-adjust : (y z : Bool) (j : I)
    → Ch.L z ≡ Ch.Rv (Ch.frame-bool y z j)
  E-adjust y z j i = push (inr tt , y) i ,
    ua-gluePath (frame Bool* y) (λ k → Ch.frame-bool y z (k ∧ j)) i

  leftChart₄ : Bool ≃ Σ (RP 0) (λ x → fst (cov⁻¹ 0 x))
  leftChart₄ = isoToEquiv (iso (λ z → inr tt , z)
    (λ { (inr tt , z) → z }) (λ { (inr tt , z) → refl }) (λ _ → refl))

  rightChart₄ : Bool ≃ (Unit × Bool)
  rightChart₄ = isoToEquiv (iso (λ z → tt , z) snd
    (λ { (tt , z) → refl }) (λ _ → refl))

  overlapChart₄ : (Bool × Bool) ≃ Σ (Σ (RP 0) (λ x → fst (cov⁻¹ 0 x)))
    (λ a → fst (cov⁻¹ 0 (fst a)))
  overlapChart₄ = isoToEquiv (iso (λ { (y , z) → (inr tt , y) , z })
    (λ { ((inr tt , y) , z) → y , z })
    (λ { ((inr tt , y) , z) → refl }) (λ { (y , z) → refl }))

  span₄ : G₄ ≃ Pushout Flat.Σf Flat.Σg
  span₄ = pushoutEquiv left₄ right₄ Flat.Σf Flat.Σg
    overlapChart₄ leftChart₄ rightChart₄ refl
    (funExt λ { (y , z) → ΣPathP (refl , sym (Ch.frame-bool y z)) })

  g₄-equiv-raw : G₄ ≃ A
  g₄-equiv-raw = compEquiv span₄
    (compEquiv (invEquiv Flat.flatten)
      (invEquiv (Σ-cong-equiv-snd cover≃Flat)))

  g₄-edge : (y z : Bool)
    → cong (g₄-equiv-raw .fst) (push (y , z)) ≡ Ch.E y z
  g₄-edge y z = cong-∙∙ (fromFlat ∘ Flat.FlattenIso.fwd)
      refl (push ((inr tt , y) , z))
      (λ i → inr (tt , Ch.frame-bool y z i))
    ∙ doubleCompPath-elim refl (flatEdge y z) (cong Ch.Rv (Ch.frame-bool y z))
    ∙ cong (_∙ cong Ch.Rv (Ch.frame-bool y z)) (sym (lUnit (flatEdge y z)))
    ∙ Square→compPath (λ i j → E-adjust y z j i)
    ∙ sym (lUnit (Ch.E y z))

  g₄-agrees : g₄-equiv-raw .fst ≡ g₄
  g₄-agrees = funExt λ { (inl z) → refl ; (inr z) → refl
    ; (push (y , z) i) → λ j → g₄-edge y z j i }

opaque
  g₄-isEquiv : isEquiv g₄
  g₄-isEquiv = subst isEquiv g₄-agrees (g₄-equiv-raw .snd)

private
  edge₄ : (y z : Bool) → Path G₄ (inl z) (inr (y ⊕ z))
  edge₄ y z = push (y , z)

  P₄ : Path G₄ (inl false) (inl true)
  P₄ = edge₄ false false ∙ sym (edge₄ true true)

  Q₄ : Path G₄ (inl false) (inr true)
  Q₄ = P₄ ∙ edge₄ false true

  W₄ : Path G₄ (inl false) (inl false)
  W₄ = P₄ ∙ (edge₄ false true ∙ sym (edge₄ true false))

  circle₄ : S¹ → G₄
  circle₄ base = inl false
  circle₄ (loop i) = W₄ i

  inverse₄ : G₄ → S¹
  inverse₄ (inl z) = base
  inverse₄ (inr z) = base
  inverse₄ (push (false , false) i) = base
  inverse₄ (push (true , true) i) = base
  inverse₄ (push (false , true) i) = base
  inverse₄ (push (true , false) i) = loop (~ i)

  section₄ : (z : G₄) → circle₄ (inverse₄ z) ≡ z
  section₄ (inl false) = refl
  section₄ (inl true) = P₄
  section₄ (inr false) = edge₄ false false
  section₄ (inr true) = Q₄
  section₄ (push (false , false) i) = compPath→Square
    {p = refl} {q = edge₄ false false} {r = refl} {s = edge₄ false false} refl i
  section₄ (push (true , true) i) = compPath→Square
    (sym (lUnit (edge₄ false false))
      ∙ sym (compPathr-cancel (edge₄ true true) (edge₄ false false))) i
  section₄ (push (false , true) i) = compPath→Square (sym (lUnit Q₄)) i
  section₄ (push (true , false) i) = compPath→Square
    (cong (λ v → sym v ∙ Q₄) (assoc P₄ (edge₄ false true) (sym (edge₄ true false)))
      ∙ cong (_∙ Q₄) (symDistr Q₄ (sym (edge₄ true false)))
      ∙ compPathr-cancel Q₄ (edge₄ true false)
      ∙ lUnit (edge₄ true false)) i

  inverse₄-loop : cong inverse₄ W₄ ≡ loop
  inverse₄-loop = cong-∙ inverse₄ P₄ (edge₄ false true ∙ sym (edge₄ true false))
    ∙ cong₂ _∙_
      (cong-∙ inverse₄ (edge₄ false false) (sym (edge₄ true true)) ∙ sym (lUnit refl))
      (cong-∙ inverse₄ (edge₄ false true) (sym (edge₄ true false)) ∙ sym (lUnit loop))
    ∙ sym (lUnit loop)

  retraction₄ : (x : S¹) → inverse₄ (circle₄ x) ≡ x
  retraction₄ base = refl
  retraction₄ (loop i) = refl-square (cong inverse₄ W₄) loop inverse₄-loop i

  circle₄-equiv : S¹ ≃ G₄
  circle₄-equiv = isoToEquiv (iso circle₄ inverse₄ section₄ retraction₄)

  g₄-loop : cong g₄ W₄ ≡ Ch.w
  g₄-loop = cong-∙ g₄ P₄ (edge₄ false true ∙ sym (edge₄ true false))
    ∙ cong₂ _∙_
      (cong-∙ g₄ (edge₄ false false) (sym (edge₄ true true)))
      (cong-∙ g₄ (edge₄ false true) (sym (edge₄ true false)))

aCircle₀ : S¹ → A
aCircle₀ base = Ch.L₀
aCircle₀ (loop i) = Ch.w i

opaque
  aCircle₀-isEquiv : isEquiv aCircle₀
  aCircle₀-isEquiv = subst isEquiv
    (funExt λ { base → refl ; (loop i) → λ j → g₄-loop j i })
    (compEquiv circle₄-equiv (g₄ , g₄-isEquiv) .snd)

  A-connected : (a : A) → PT.∥ Ch.L₀ ≡ a ∥₁
  A-connected a = PT.map
    (λ p → cong aCircle₀ p ∙ secEq (aCircle₀ , aCircle₀-isEquiv) a)
    (isConnectedS¹ (invEq (aCircle₀ , aCircle₀-isEquiv) a))

-- Rooted half traversals and their double-cover generator.
h : (a : A) → δ a ≡ a
h = Ch.deck-homotopy

β : (a : A) → pr₁ a ≡ pr₁ a
β a = cong pr₁ (h a)

τ : (a : A) → pr₁ a ≡ pr₁ a
τ a = sym (β a)

γ : (a : A) → a ≡ a
γ a = (sym (h a) ∙ sym (h (δ a))) ∙ δ-invol a

opaque
  β-L₀ : β Ch.L₀ ≡ sym Ch.t
  β-L₀ = cong (cong pr₁) (Ch.deck-L false)
    ∙ cong-∙ pr₁ (Ch.δ-L false) (Ch.half-L false)
    ∙ cong (refl ∙_) (cong-∙ pr₁ (Ch.E true true) (sym (Ch.E false false)))
    ∙ sym (lUnit (Ch.a true ∙ sym (Ch.a false)))
    ∙ sym (symDistr (Ch.a false) (sym (Ch.a true)))

  β-next : (a : A) → β (δ a) ≡ β a
  β-next a = sym (cong (cong pr₁)
    (invEq (congEquiv (compPathrEquiv (h a))) (naturality h (h a))))

  γ-projects : (a : A) → cong pr₁ (γ a) ≡ τ a ∙ τ a
  γ-projects a = cong-∙ pr₁ (sym (h a) ∙ sym (h (δ a))) (δ-invol a)
    ∙ cong (_∙ refl) (cong-∙ pr₁ (sym (h a)) (sym (h (δ a))))
    ∙ sym (rUnit (τ a ∙ τ (δ a)))
    ∙ cong (τ a ∙_) (cong sym (β-next a))

  carrier-set : (T : B) → isSet (fst T)
  carrier-set T = PT.rec isPropIsSet
    (λ e → isOfHLevelRespectEquiv 2 (invEquiv e) isSetBool) (snd T)

  γ-L₀ : γ Ch.L₀ ≡ Ch.w
  γ-L₀ = Σ-path-faithful (carrier-set ∘ w₁) (γ Ch.L₀) Ch.w
    (γ-projects Ch.L₀ ∙ cong₂ _∙_ (cong sym β-L₀) (cong sym β-L₀)
      ∙ sym Ch.w-projects)

aCircle : A → S¹ → A
aCircle a base = a
aCircle a (loop i) = γ a i

bCircle : A → S¹ → R
bCircle a base = pr₁ a
bCircle a (loop i) = β a i

opaque
  aCircle-isEquiv : (a : A) → isEquiv (aCircle a)
  aCircle-isEquiv a = PT.rec (isPropIsEquiv (aCircle a))
    (λ p → subst (λ a → isEquiv (aCircle a)) p at-L₀) (A-connected a)
    where
    at-L₀ : isEquiv (aCircle Ch.L₀)
    at-L₀ = subst isEquiv
      (funExt λ { base → refl ; (loop i) → λ j → γ-L₀ (~ j) i })
      aCircle₀-isEquiv

  bCircle-isEquiv : (a : A) → isEquiv (bCircle a)
  bCircle-isEquiv a = PT.rec (isPropIsEquiv (bCircle a))
    (λ p → subst (λ a → isEquiv (bCircle a)) p at-L₀) (A-connected a)
    where
    at-L₀ : isEquiv (bCircle Ch.L₀)
    at-L₀ = subst isEquiv
      (funExt λ { base → refl ; (loop i) → λ j → β-L₀ (~ j) i })
      (compEquiv invS¹Equiv (rCircle , rCircle-isEquiv) .snd)

  CToCircle-isEquiv : isEquiv CToCircle
  CToCircle-isEquiv = isoToIsEquiv
    (iso CToCircle circleToC circle-section circle-retraction)

rootC : (a : A) → C ≃ A
rootC a = compEquiv (CToCircle , CToCircle-isEquiv) (aCircle a , aCircle-isEquiv a)

rootC-base : (a : A) → rootC a .fst 0C ≡ a
rootC-base a = refl

opaque
  rootC-loop : (a : A) → cong (rootC a .fst) hC ≡ γ a
  rootC-loop a = cong (cong (aCircle a)) (λ k i → circle-section (loop i) k)

rootR : (a : A) → S¹ ≃ R
rootR a = bCircle a , bCircle-isEquiv a

-- The actual family chart, including the inverse-frame seam.
F : A → C → Ksign
F a u = λA (a , u)

F₀ : A → Ksign
F₀ a = F a 0C

Z : R → Ksign
Z x = x , embase

V : (a : A) → (0C ≡ 0C) → F₀ a ≡ F₀ a
V a p = cong (F a) p

sgnLoop : ∀ {ℓ} {X : Type ℓ} {x : X} → Bool → (x ≡ x) → x ≡ x
sgnLoop false p = p
sgnLoop true p = sym p

α : (T : B) → fst T → C → SignC T
α T y = invEq (ε T y)

opaque
  χ : (T : B) (y : fst T) (u : C)
    → α T (op T y) (ι .fst u) ≡ α T y u
  χ T y u = invEq (congEquiv (ε T (op T y)))
    (secEq (ε T (op T y)) (ι .fst u)
      ∙ cong (λ f → f u) ι-map
      ∙ sym (ε-op T y (α T y u) ∙ cong negC (secEq (ε T y) u)))

open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.FilledLoops
  using (based-sym; square-based)

opaque
  based-inverse : ∀ {ℓ} {X : Type ℓ} {x y : X}
    (p : x ≡ y) (l : x ≡ x) → based (sym p) (based p l) ≡ l
  based-inverse p l = J
    (λ y p → based (sym p) (based p l) ≡ l)
    (based-refl (based refl l) ∙ based-refl l) p

  based-conjugate : ∀ {ℓ} {X : Type ℓ} {x y : X}
    (p : x ≡ y) (l : y ≡ y) → based p ((p ∙ l) ∙ sym p) ≡ l
  based-conjugate p l = based-inverse (sym p) l


-- Instantiate the generic inverse-frame circle chart without unfolding SignC.
private
  module Family = InverseFrameChart {R₀ = R}
    (λ x → fst (w₁ x)) (λ x → SignC (w₁ x)) {Y = C}
    ι (λ x → op (w₁ x)) h (λ x y → invEquiv (ε (w₁ x) y))
    (λ x → χ (w₁ x))

-- Adapt only the generic chart's source presentation, avoiding specialized
-- SignC PathP elaboration.
private
  sourceFamily : (b : S¹) → Dinv b ≃ Family.source b
  sourceFamily base = idEquiv C
  sourceFamily (loop i) = idEquiv (ua ι i)

  familyBase-agree : (a : A) (b : S¹) → Family.baseCircle a b ≡ bCircle a b
  familyBase-agree a base = refl
  familyBase-agree a (loop i) = refl

  opaque
    familyBase-isEquiv : (a : A) → isEquiv (Family.baseCircle a)
    familyBase-isEquiv a = subst isEquiv (sym (funExt (familyBase-agree a)))
      (bCircle-isEquiv a)

raw : (a : A) → Kinv ≃ Ksign
raw a = TotalChart.equivalence
  {X = S¹} {Y = R} {P = Dinv} {Q = SignC ∘ w₁}
  (Family.baseCircle a , familyBase-isEquiv a)
  (λ b → compEquiv
    {A = Dinv b} {B = Family.source b} {C = SignC (w₁ (Family.baseCircle a b))}
    (sourceFamily b) (Family.family a b))

raw-over : (a : A) (z : Kinv) → fst (raw a .fst z) ≡ bCircle a (fst z)
raw-over a z = familyBase-agree a (fst z)

raw-fibre : (a : A) (u : C) → raw a .fst (base , u) ≡ F a u
raw-fibre a u = refl

raw-base : (a : A) → raw a .fst kbase ≡ F₀ a
raw-base a = cong (raw a .fst) klein-base


-- DescentChart.L9 proves raw-r and raw-j-projects for this total chart;
-- DescentChart.Finish uses them to construct the marked boundary comparison.

prSign : Ksign → R
prSign = fst

-- Zero section, including the inverse evaluation's pointing.
q : (a : A) → F₀ a ≡ Z (pr₁ a)
q (x , y) = ΣPathP (refl ,
  sym (cong (invEq (ε (w₁ x) y)) (ε-base (w₁ x) y))
    ∙ retEq (ε (w₁ x) y) embase)

J₀ : (a : A) → F₀ a ≡ F₀ a
J₀ a = (q a ∙ cong Z (τ a)) ∙ sym (q a)

opaque
  J-projects : (a : A) → cong prSign (J₀ a) ≡ τ a
  J-projects a = cong-∙ prSign (q a ∙ cong Z (τ a)) (sym (q a))
    ∙ cong (_∙ refl) (cong-∙ prSign (q a) (cong Z (τ a)))
    ∙ based-refl (τ a)

  γ-boundary : (a : A) → cong F₀ (γ a) ≡ J₀ a ∙ J₀ a
  γ-boundary a = sym (based-inverse (q a) (cong F₀ (γ a)))
    ∙ cong (based (sym (q a)))
      (square-based (q a) (cong F₀ (γ a)) (cong (Z ∘ pr₁) (γ a))
        (λ i j → q (γ a i) j)
        ∙ cong (cong Z) (γ-projects a) ∙ cong-∙ Z (τ a) (τ a))
    ∙ based-comp (sym (q a)) (cong Z (τ a)) (cong Z (τ a))

open import Cubical.Foundations.Pointed
open import Cubical.Homotopy.Loopspace using (Ω→; Ω→∘; Ω≃∙)
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emloop-sym)

-- Pointed loop functor adapters: binary based is not judgmentally Ω→.
opaque
  Ω-based : ∀ {ℓ ℓ′} {X : Pointed ℓ} {Y : Pointed ℓ′}
    (f : X →∙ Y) (p : X .snd ≡ X .snd)
    → Ω→ f .fst p ≡ based (f .snd) (cong (f .fst) p)
  Ω-based f p = doubleCompPath-elim (sym (f .snd)) (cong (f .fst) p) (f .snd)

  Ω-id : ∀ {ℓ} {X : Pointed ℓ} (p : X .snd ≡ X .snd)
    → Ω→ (idfun∙ X) .fst p ≡ p
  Ω-id p = Ω-based (idfun∙ _) p ∙ based-refl p

  Ω-section : {X Y : Pointed ℓ-zero} (e : X ≃∙ Y)
    (p : Y .snd ≡ Y .snd)
    → Ω→ (≃∙map e) .fst (Ω→ (≃∙map (invEquiv∙ e)) .fst p) ≡ p
  Ω-section e p = sym (Ω→∘ (≃∙map e) (≃∙map (invEquiv∙ e)) p)
    ∙ cong (λ f → Ω→ f .fst p) (≃∙→ret/sec∙ e .snd) ∙ Ω-id p

  Ω-retraction : {X Y : Pointed ℓ-zero} (e : X ≃∙ Y)
    (p : X .snd ≡ X .snd)
    → Ω→ (≃∙map (invEquiv∙ e)) .fst (Ω→ (≃∙map e) .fst p) ≡ p
  Ω-retraction e p = sym (Ω→∘ (≃∙map (invEquiv∙ e)) (≃∙map e) p)
    ∙ cong (λ f → Ω→ f .fst p) (≃∙→ret/sec∙ e .fst) ∙ Ω-id p

  neg-loop : (p : 0C ≡ 0C) → cong negC p ≡ sym p
  neg-loop p = cong (cong negC) (sym (FS.emloop-encC p))
    ∙ emloop-sym ℤGroup (FS.encC p) ∙ cong sym (FS.emloop-encC p)

  -- Generic inverse-loop cancellation, so no EM family is unfolded here.
  inverse-loop-op : {X : Pointed ℓ-zero}
    (e d : X ≃∙ (C , 0C))
    → ((l : X .snd ≡ X .snd)
      → Ω→ (≃∙map e) .fst l ≡ sym (Ω→ (≃∙map d) .fst l))
    → (p : 0C ≡ 0C)
    → Ω→ (≃∙map (invEquiv∙ e)) .fst p
      ≡ Ω→ (≃∙map (invEquiv∙ d)) .fst (sym p)
  inverse-loop-op e d eq p = invEq (congEquiv (Ω≃∙ e .fst))
    (Ω-section e p ∙ sym
      (eq (Ω→ (≃∙map (invEquiv∙ d)) .fst (sym p))
        ∙ cong sym (Ω-section d (sym p))))

ε∙ : (T : B) (y : fst T) → (SignC T , embase) ≃∙ (C , 0C)
ε∙ T y = ε T y , ε-base T y

opaque
  ε-op-loop : (T : B) (y : fst T) (l : Path (SignC T) embase embase)
    → Ω→ (≃∙map (ε∙ T (op T y))) .fst l
      ≡ sym (Ω→ (≃∙map (ε∙ T y)) .fst l)
  ε-op-loop T y l = cong (λ f → Ω→ f .fst l) (ε-op-pointed T y)
    ∙ sym (cong-∙∙ negC (sym (ε-base T y)) (cong (ε T y .fst) l) (ε-base T y))
    ∙ neg-loop (Ω→ (≃∙map (ε∙ T y)) .fst l)

  inverse-ε-op-loop : (T : B) (y : fst T) (p : 0C ≡ 0C)
    → Ω→ (≃∙map (invEquiv∙ (ε∙ T (op T y)))) .fst p
      ≡ Ω→ (≃∙map (invEquiv∙ (ε∙ T y))) .fst (sym p)
  inverse-ε-op-loop T y = inverse-loop-op
    (ε∙ T (op T y)) (ε∙ T y) (ε-op-loop T y)


-- DescentChart.L11 proves fibre conjugation, vertical factorization and
-- the odd-square law for this family, retaining the pointings.

-- Untruncated factorization of a Sigma loop over refl.
opaque
  vertical-path : ∀ {ℓ ℓ′} {X : Type ℓ} {P : X → Type ℓ′}
    {u : Σ X P} (v : u ≡ u) → cong fst v ≡ refl
    → Σ[ p ∈ (u .snd ≡ u .snd) ] (v ≡ cong (λ t → u .fst , t) p)
  vertical-path {P = P} {u = u} v e =
    subst (λ r → PathP (λ i → P (r i)) (u .snd) (u .snd)) e (λ i → v i .snd) ,
    λ j i → e j i ,
      subst-filler (λ r → PathP (λ i → P (r i)) (u .snd) (u .snd))
        e (λ i → v i .snd) j i


-- Only the first boundary generator has an unmarked-frame sign.
open import Cubical.Data.Int using (_·_)

LImage : {X : Type₀} {x : X}
  → (C , 0C) ≃∙ (X , x) → (0C ≡ 0C) → x ≡ x
LImage e p = based (snd e) (cong (fst (fst e)) p)

opaque
  Ω-sym : ∀ {ℓ ℓ′} {X : Pointed ℓ} {Y : Pointed ℓ′}
    (f : X →∙ Y) (p : X .snd ≡ X .snd)
    → Ω→ f .fst (sym p) ≡ sym (Ω→ f .fst p)
  Ω-sym f p = Ω-based f (sym p) ∙ based-sym (f .snd) (cong (f .fst) p)
    ∙ cong sym (sym (Ω-based f p))

  Ω-sign : ∀ {ℓ ℓ′} {X : Pointed ℓ} {Y : Pointed ℓ′}
    (f : X →∙ Y) (s : Bool) (p : X .snd ≡ X .snd)
    → Ω→ f .fst (sgnLoop s p) ≡ sgnLoop s (Ω→ f .fst p)
  Ω-sign f false p = refl
  Ω-sign f true p = Ω-sym f p

  emloop-sign : (s : Bool) → emloop (FS.signℤ s · pos 1) ≡ sgnLoop s hC
  emloop-sign false = refl
  emloop-sign true = emloop-sym ℤGroup (pos 1)

  circle-frame-sign : {X : Type₀} {x : X}
    (e d : (C , 0C) ≃∙ (X , x))
    → Σ[ s ∈ Bool ] (LImage d hC ≡ sgnLoop s (LImage e hC))
  circle-frame-sign e d = s ,
    sym (Ω-based (≃∙map d) hC)
      ∙ sym (Ω-section e (Ω→ (≃∙map d) .fst hC))
      ∙ cong (Ω→ (≃∙map e) .fst)
        (sym (Ω→∘ (≃∙map (invEquiv∙ e)) (≃∙map d) hC))
      ∙ cong (Ω→ (≃∙map e) .fst) φ-sign
      ∙ Ω-sign (≃∙map e) s hC
      ∙ cong (sgnLoop s) (Ω-based (≃∙map e) hC)
    where
    φ : (C , 0C) ≃∙ (C , 0C)
    φ = compEquiv∙ d (invEquiv∙ e)
    s : Bool
    s = FS.pointed-C-auto-sign φ .fst
    φ-sign : Ω→ (≃∙map φ) .fst hC ≡ sgnLoop s hC
    φ-sign = sym (FS.emloop-encC (Ω→ (≃∙map φ) .fst hC))
      ∙ cong emloop (FS.pointed-C-auto-sign φ .snd (pos 1)) ∙ emloop-sign s

a★ : A
a★ = invEq fA 0C

coverLoop : a★ ≡ a★
coverLoop = cong (invEq fA) hC

opaque
  boundary-sign : Σ[ s ∈ Bool ] (coverLoop ≡ sgnLoop s (γ a★))
  boundary-sign = frames .fst , sym (based-refl coverLoop)
    ∙ frames .snd
    ∙ cong (sgnLoop (frames .fst))
      (based-refl (cong (rootC a★ .fst) hC) ∙ rootC-loop a★)
    where
    frames : Σ[ s ∈ Bool ]
      (LImage (invEquiv fA , refl) hC ≡ sgnLoop s (LImage (rootC a★ , refl) hC))
    frames = circle-frame-sign (rootC a★ , refl) (invEquiv fA , refl)

boundarySign : Bool
boundarySign = boundary-sign .fst

opaque
  cong-sign : ∀ {ℓ ℓ′} {X : Type ℓ} {Y : Type ℓ′}
    (f : X → Y) {x : X} (s : Bool) (p : x ≡ x)
    → cong f (sgnLoop s p) ≡ sgnLoop s (cong f p)
  cong-sign f false p = refl
  cong-sign f true p = refl


  sign-u : cong λsign uT ≡ sgnLoop boundarySign (J₀ a★ ∙ J₀ a★)
  sign-u = cong (cong F₀) (boundary-sign .snd)
    ∙ cong-sign F₀ boundarySign (γ a★)
    ∙ cong (sgnLoop boundarySign) (γ-boundary a★)

  sign-v : cong λsign vT ≡ V a★ hC
  sign-v = refl

-- Reverse j and fix r on the actual Klein HIT, not its presentation.
import Cubical.HITs.KleinBottle.Base as KB
import Cubical.HITs.KleinBottle.Properties as KP

private
  opaque
    reverse-relator : sym KB.line2 ∙ KB.line1 ≡ sym KB.line1 ∙ sym KB.line2
    reverse-relator = rUnit (sym KB.line2 ∙ KB.line1)
      ∙ cong ((sym KB.line2 ∙ KB.line1) ∙_) (sym (rCancel KB.line2))
      ∙ assoc (sym KB.line2 ∙ KB.line1) KB.line2 (sym KB.line2)
      ∙ cong (_∙ sym KB.line2) (sym (assoc (sym KB.line2) KB.line1 KB.line2))
      ∙ cong (λ v → (sym KB.line2 ∙ v) ∙ sym KB.line2)
        (sym (LoopWords.inverse-fibre KB.line2 KB.line1
          (sym (Square→compPath KB.square))))
      ∙ cong (_∙ sym KB.line2) (compPathl-cancel (sym KB.line2) (sym KB.line1))

  reverseKB : KB.KleinBottle → KB.KleinBottle
  reverseKB KB.point = KB.point
  reverseKB (KB.line1 i) = KB.line1 i
  reverseKB (KB.line2 i) = KB.line2 (~ i)
  reverseKB (KB.square i j) = compPath→Square (sym reverse-relator) i j

  opaque
    reverseKB-invol : (x : KB.KleinBottle) → reverseKB (reverseKB x) ≡ x
    reverseKB-invol = KP.elimSet (λ x → KP.isGroupoidKleinBottle _ _)
      refl (λ i → refl) (λ i → refl)

    reverseKB-isEquiv : isEquiv reverseKB
    reverseKB-isEquiv = isoToIsEquiv (iso reverseKB reverseKB reverseKB-invol reverseKB-invol)

  reverseKB∙ : (KB.KleinBottle , KB.point) ≃∙ (KB.KleinBottle , KB.point)
  reverseKB∙ = (reverseKB , reverseKB-isEquiv) , refl

  klein∙ : (KB.KleinBottle , KB.point) ≃∙ (Kinv , kbase)
  klein∙ = klein≃Kinv , refl

reverseK∙ : (Kinv , kbase) ≃∙ (Kinv , kbase)
reverseK∙ = compEquiv∙ (invEquiv∙ klein∙) (compEquiv∙ reverseKB∙ klein∙)

reverseK : Kinv ≃ Kinv
reverseK = reverseK∙ .fst

reverseK-base : reverseK .fst kbase ≡ kbase
reverseK-base = reverseK∙ .snd

opaque
  Ω-conjugate : {X Y : Pointed ℓ-zero} (e : X ≃∙ Y) (f : X ≃∙ X)
    (p : X .snd ≡ X .snd)
    → Ω→ (≃∙map (compEquiv∙ (invEquiv∙ e) (compEquiv∙ f e))) .fst
      (Ω→ (≃∙map e) .fst p)
      ≡ Ω→ (≃∙map e) .fst (Ω→ (≃∙map f) .fst p)
  Ω-conjugate e f p = Ω→∘ (≃∙map (compEquiv∙ f e)) (≃∙map (invEquiv∙ e))
      (Ω→ (≃∙map e) .fst p)
    ∙ Ω→∘ (≃∙map e) (≃∙map f)
      (Ω→ (≃∙map (invEquiv∙ e)) .fst (Ω→ (≃∙map e) .fst p))
    ∙ cong (Ω→ (≃∙map e) .fst ∘ Ω→ (≃∙map f) .fst) (Ω-retraction e p)

  reverseK-j : based reverseK-base (cong (reverseK .fst) j) ≡ sym j
  reverseK-j = sym (Ω-based (≃∙map reverseK∙) j)
    ∙ cong (Ω→ (≃∙map reverseK∙) .fst)
      (sym (Ω-based (≃∙map klein∙) KB.line2 ∙ based-refl j))
    ∙ Ω-conjugate klein∙ reverseKB∙ KB.line2
    ∙ cong (Ω→ (≃∙map klein∙) .fst)
      (Ω-based (≃∙map reverseKB∙) KB.line2 ∙ based-refl (sym KB.line2))
    ∙ Ω-sym (≃∙map klein∙) KB.line2
    ∙ cong sym (Ω-based (≃∙map klein∙) KB.line2 ∙ based-refl j)

  reverseK-r : based reverseK-base (cong (reverseK .fst) r) ≡ r
  reverseK-r = sym (Ω-based (≃∙map reverseK∙) r)
    ∙ cong (Ω→ (≃∙map reverseK∙) .fst)
      (sym (Ω-based (≃∙map klein∙) KB.line1 ∙ based-refl r))
    ∙ Ω-conjugate klein∙ reverseKB∙ KB.line1
    ∙ cong (Ω→ (≃∙map klein∙) .fst)
      (Ω-based (≃∙map reverseKB∙) KB.line1 ∙ based-refl KB.line1)
    ∙ Ω-based (≃∙map klein∙) KB.line1 ∙ based-refl r


-- Based-loop markings determine the full torus-boundary path in Ksign.
-- DescentChart.Finish supplies markedTotal and its descentChart.
record MarkedTotal : Type₁ where
  field
    total : Kinv ≃ Ksign
    basepoint : total .fst kbase ≡ λsign (0C , 0C)
    mark-u : based basepoint (cong (total .fst) (j ∙ j)) ≡ cong λsign uT
    mark-v : based basepoint (cong (total .fst) r) ≡ cong λsign vT

module FromMarkedTotal (marked : MarkedTotal) where
  open MarkedTotal marked

  opaque
    ku : based basepoint (cong (total .fst ∘ λ₂) uT) ≡ cong λsign uT
    ku = cong (based basepoint ∘ cong (total .fst)) λ₂-u ∙ mark-u

    kv : based basepoint (cong (total .fst ∘ λ₂) vT) ≡ cong λsign vT
    kv = cong (based basepoint ∘ cong (total .fst)) λ₂-v ∙ mark-v

    boundary : total .fst ∘ λ₂ ≡ λsign
    boundary = Compare.homotopy Ksign-groupoid (total .fst ∘ λ₂) λsign basepoint
      (based-square basepoint (cong (total .fst ∘ λ₂) uT) (cong λsign uT) ku)
      (based-square basepoint (cong (total .fst ∘ λ₂) vT) (cong λsign vT) kv)

    descentChart : DescentChart
    descentChart .DescentChart.total = total
    descentChart .DescentChart.boundary = boundary
