{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.CofibreLES where

-- Construct the cofibre LES from the geometric pushout sequence.
-- The algebra is factored through arbitrary groups before instantiating cellular homology.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; +-comm)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Unit using (Unit ; tt ; Unit≃Unit*)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.CW.Base using (isCW ; hasCWskel)
open import Cubical.CW.Instances.Unit using (CWskelUnit* ; hasFinCWskelUnit*)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using
  (Exact₃ ; cellular-map ; cellular-map-agrees ; CofibreSequenceData
  ; CofibreLES ; finite-cofibreCW)
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→ ; cofibCW)
open import DeloopS3.Bridge.ComponentHomology.ChainTools using
  (chosen-zero ; one-vertex-homology)
open import DeloopS3.Bridge.DMCExactness.Geometric using
  (SpanSequenceData ; GeometricPushoutLES ; actual-source ; actual-sum)
open import DeloopS3.Bridge.DMCExactness.Transport using
  (conjugateHom ; conjugate-exact)
open import DeloopS3.Bridge.DMCExactness.Exactness using (exact-from-kernel)
open import DeloopS3.Bridge.DMCExactness.Groups using (exact-composite)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging using
  (finite-pushoutLES-merely)

open IsGroupHom

-- This small equivalence is transparent: its forward map is snd and
-- its inverse inserts the identity, not a chosen centre of contraction.
zero-product-right : {G H : Group₀} → isContr (fst G)
  → GroupEquiv (DirProd G H) H
zero-product-right {G} {H} c = isoToEquiv
  (iso snd (λ h → GroupStr.1g (snd G) , h) (λ _ → refl)
    (λ x → ΣPathP
      (sym (snd c (GroupStr.1g (snd G))) ∙ snd c (fst x) , refl))) ,
  makeIsGroupHom (λ _ _ → refl)

abstract
  group-hom-path : {G H : Group₀} (u v : GroupHom G H)
    → ((x : fst G) → fst u x ≡ fst v x) → u ≡ v
  group-hom-path {G} {H} u v p =
    Σ≡Prop (λ _ → isPropIsGroupHom G H) (funExt p)

  exact-rewrite : {G H K : Group₀}
    (u u′ : GroupHom G H) (v v′ : GroupHom H K)
    → ((x : fst G) → fst u x ≡ fst u′ x)
    → ((x : fst H) → fst v x ≡ fst v′ x)
    → Exact₃ u v → Exact₃ u′ v′
  exact-rewrite u u′ v v′ pu pv =
    subst2 Exact₃ (group-hom-path u u′ pu) (group-hom-path v v′ pv)

  -- The two maps being compared are GIVEN homomorphisms.  These lemmas
  -- do not require inversion itself to be a homomorphism.
  exact-change-sign-right : {G H K : Group₀}
    (u : GroupHom G H) (v v′ : GroupHom H K)
    → ((h : fst H) → fst v′ h ≡ GroupStr.inv (snd K) (fst v h))
    → Exact₃ u v → Exact₃ u v′
  exact-change-sign-right {K = K} u v v′ sign ex =
    exact-from-kernel u v′
      (λ h p → equivFun (ex h)
        (sym (GroupTheory.invInv K (fst v h))
        ∙ cong (GroupStr.inv (snd K)) (sym (sign h) ∙ p)
        ∙ GroupTheory.inv1g K))
      (λ x → sign (fst u x)
        ∙ cong (GroupStr.inv (snd K))
            (exact-composite {u = u} {v = v} ex x)
        ∙ GroupTheory.inv1g K)

  exact-change-sign-left : {G H K : Group₀}
    (u u′ : GroupHom G H) (v : GroupHom H K)
    → ((g : fst G) → fst u′ g ≡ GroupStr.inv (snd H) (fst u g))
    → Exact₃ u v → Exact₃ u′ v
  exact-change-sign-left {G} {H} {K} u u′ v sign ex =
    exact-from-kernel u′ v
      (λ h p → PT.map
        (λ { (g , q) → GroupStr.inv (snd G) g ,
          sign (GroupStr.inv (snd G) g)
          ∙ cong (GroupStr.inv (snd H)) (presinv (snd u) g)
          ∙ GroupTheory.invInv H (fst u g) ∙ q })
        (equivFun (ex h) p))
      (λ g → cong (fst v) (sign g)
        ∙ presinv (snd v) (fst u g)
        ∙ cong (GroupStr.inv (snd K))
            (exact-composite {u = u} {v = v} ex g)
        ∙ GroupTheory.inv1g K)

  reverse-sign : {G H : Group₀} (u v : GroupHom G H)
    → ((x : fst G) → fst u x ≡ GroupStr.inv (snd H) (fst v x))
    → (x : fst G) → fst v x ≡ GroupStr.inv (snd H) (fst u x)
  reverse-sign {H = H} u v p x =
    sym (GroupTheory.invInv H (fst v x))
      ∙ cong (GroupStr.inv (snd H)) (sym (p x))

unitCW : CW₀
unitCW = Unit , finite≤→isCW unit-finite≤

private
  -- The one-vertex argument also covers degree zero; dimension alone
  -- only proves the positive-degree vanishings.
  unit-skeleton : hasCWskel Unit
  unit-skeleton = CWskelUnit* ,
    compEquiv Unit≃Unit* (snd (snd hasFinCWskelUnit*))

abstract
  unit-Hzero : (n : ℕ) → Hzero unitCW n
  unit-Hzero zero = chosen-zero unitCW unit-skeleton 0
    (one-vertex-homology CWskelUnit* refl)
  unit-Hzero (suc n) = finite≤-homology-above unitCW 0 (suc n)
    unit-finite≤ (n , +-comm n 1)

  -- Identity on the underlying type; only the propositional CW witness
  -- changes. In particular, no path in the underlying type is erased.
  CW-witness-path : {X : Type} (c d : isCW X)
    → _≡_ {A = CW₀} (X , c) (X , d)
  CW-witness-path c d = ΣPathP (refl , PT.squash₁ c d)

-- The sequence conversion is entirely group-theoretic.  The supplied
-- comparison equations specify the negative source and the actual right
-- inclusion; no cellular homology unfolds while constructing the record.
module Collapse
  (HA HU HB HC : ℕ → Group₀)
  (source : (n : ℕ) → fst (HA n) → fst (DirProd (HU n) (HB n)))
  (vertices : (n : ℕ) → fst (DirProd (HU n) (HB n)) → fst (HC n))
  (fH : (n : ℕ) → GroupHom (HA n) (HB n))
  (iH : (n : ℕ) → GroupHom (HB n) (HC n))
  (d : SpanSequenceData HA HU HB HC source vertices)
  (u0 : (n : ℕ) → isContr (fst (HU n)))
  (source-sign : (n : ℕ) (a : fst (HA n))
    → snd (source n a) ≡ GroupStr.inv (snd (HB n)) (fst (fH n) a))
  (vertices-right : (n : ℕ) (b : fst (HB n))
    → vertices n (GroupStr.1g (snd (HU n)) , b) ≡ fst (iH n) b)
  where

  private
    module S = SpanSequenceData d

    e : (n : ℕ) → GroupEquiv (DirProd (HU n) (HB n)) (HB n)
    e n = zero-product-right (u0 n)

    s : (n : ℕ) → GroupHom (HA n) (HB n)
    s n = conjugateHom (idGroupEquiv {G = HA n}) (e n) (S.source-map n)

    t : (n : ℕ) → GroupHom (HB n) (HC n)
    t n = conjugateHom (e n) (idGroupEquiv {G = HC n}) (S.sum-map n)

    bdy : (n : ℕ) → GroupHom (HC (suc n)) (HA n)
    bdy n = conjugateHom (idGroupEquiv {G = HC (suc n)})
      (idGroupEquiv {G = HA n}) (S.boundary n)

    abstract
      s-sign : (n : ℕ) (a : fst (HA n))
        → fst (s n) a ≡ GroupStr.inv (snd (HB n)) (fst (fH n) a)
      s-sign n a = cong snd (S.source-agrees n a) ∙ source-sign n a

      t-agrees : (n : ℕ) (b : fst (HB n)) → fst (t n) b ≡ fst (iH n) b
      t-agrees n b = S.sum-agrees n (GroupStr.1g (snd (HU n)) , b)
        ∙ vertices-right n b

      total-exact : (n : ℕ) → n < 5 → Exact₃ (iH (suc n)) (S.boundary n)
      total-exact n lt = exact-rewrite
        (t (suc n)) (iH (suc n)) (bdy n) (S.boundary n)
        (t-agrees (suc n)) (λ _ → refl)
        (conjugate-exact (e (suc n)) (idGroupEquiv {G = HC (suc n)})
          (idGroupEquiv {G = HA n}) (S.sum-map (suc n)) (S.boundary n)
          (S.exact-total n lt))

      source-exact : (n : ℕ) → n < 5 → Exact₃ (S.boundary n) (fH n)
      source-exact n lt = exact-change-sign-right
        (S.boundary n) (s n) (fH n) (reverse-sign (s n) (fH n) (s-sign n))
        (exact-rewrite (bdy n) (S.boundary n) (s n) (s n)
          (λ _ → refl) (λ _ → refl)
          (conjugate-exact (idGroupEquiv {G = HC (suc n)})
            (idGroupEquiv {G = HA n}) (e n) (S.boundary n) (S.source-map n)
            (S.exact-source n lt)))

      target-exact : (n : ℕ) → n < 5 → Exact₃ (fH n) (iH n)
      target-exact n lt = exact-change-sign-left (s n) (fH n) (iH n)
        (reverse-sign (s n) (fH n) (s-sign n))
        (exact-rewrite (s n) (s n) (t n) (iH n)
          (λ _ → refl) (t-agrees n)
          (conjugate-exact (idGroupEquiv {G = HA n}) (e n)
            (idGroupEquiv {G = HC n}) (S.source-map n) (S.sum-map n)
            (S.exact-target n lt)))

  abstract
    sequence : CofibreSequenceData HA HB HC fH iH
    CofibreSequenceData.boundary sequence = S.boundary
    CofibreSequenceData.exact-cofibre sequence = total-exact
    CofibreSequenceData.exact-source sequence = source-exact
    CofibreSequenceData.exact-target sequence = target-exact

abstract
  -- p is the SAME identification as in the supplied pushout LES.  The
  -- inclusion is transport (sym p) ∘ inr, never assumed to be plain inr.
  pushout-to-cofibreLES : (A B P : CW₀) (f : fst A → fst B)
    → GeometricPushoutLES A unitCW B (λ _ → tt) f P
    → CofibreLES A B f P
  pushout-to-cofibreLES A B P f (p , d) = p , Collapse.sequence
    (H̃ᶜʷ A) (H̃ᶜʷ unitCW) (H̃ᶜʷ B) (H̃ᶜʷ P)
    (actual-source A unitCW B (λ _ → tt) f)
    (actual-sum A unitCW B (λ _ → tt) f P p)
    (λ n → cellular-map A B n f)
    (λ n → cellular-map B P n (λ b → transport (sym p) (inr b)))
    d unit-Hzero (λ _ _ → refl) right-inclusion
    where
    right-inclusion : (n : ℕ) (b : fst (H̃ᶜʷ B n))
      → actual-sum A unitCW B (λ _ → tt) f P p n
          (GroupStr.1g (snd (H̃ᶜʷ unitCW n)) , b)
        ≡ fst (cellular-map B P n (λ b → transport (sym p) (inr b))) b
    right-inclusion n b =
      cong (λ z → GroupStr._·_ (snd (H̃ᶜʷ P n)) z
        (fst (cellular-map B P n (λ b → transport (sym p) (inr b))) b))
        (pres1 (snd (cellular-map unitCW P n
          (λ u → transport (sym p) (inl u)))))
      ∙ GroupStr.·IdL (snd (H̃ᶜʷ P n))
          (fst (cellular-map B P n (λ b → transport (sym p) (inr b))) b)

abstract
  cofibreLES-change-CW : (A B : CW₀) (f : fst A → fst B)
    (c d : isCW (cofib f))
    → CofibreLES A B f (cofib f , c)
    → CofibreLES A B f (cofib f , d)
  cofibreLES-change-CW A B f c d =
    subst (CofibreLES A B f) (CW-witness-path c d)

  -- The geometric theorem supplies the LES, with all choices
  -- retained under one propositional truncation.
  finite-cofibreLES-merely : (A B : CW₀) (f : fst A → fst B)
    (dA dB : ℕ) (finA : Finite≤ dA (fst A)) (finB : Finite≤ dB (fst B))
    → PT.∥ CofibreLES A B f
        (finite-cofibreCW A B f dA dB finA finB) ∥₁
  finite-cofibreLES-merely A B f dA dB finA finB =
    PT.map
      (λ les → cofibreLES-change-CW A B f (snd P)
        (snd (finite-cofibreCW A B f dA dB finA finB))
        (pushout-to-cofibreLES A B P f les))
      (finite-pushoutLES-merely A unitCW B (λ _ → tt) f
        dA 0 dB finA unit-finite≤ finB)
    where
    P : CW₀
    P = cofib f , finite≤→isCW
      (pushout-finite≤ (λ _ → tt) f dA 0 dB finA unit-finite≤ finB)

  recognition-cofibreLES-merely : (A B : CW₀) (f : fst A → fst B)
    (finA : Finite≤ 4 (fst A)) (finB : Finite≤ 4 (fst B))
    → PT.∥ CofibreLES A B f
        (cofibCW A B (finite≤→isFinCW {d = 4} finA) f) ∥₁
  recognition-cofibreLES-merely A B f finA finB =
    PT.map
      (cofibreLES-change-CW A B f
        (snd (finite-cofibreCW A B f 4 4 finA finB))
        (snd (cofibCW A B (finite≤→isFinCW {d = 4} finA) f)))
      (finite-cofibreLES-merely A B f 4 4 finA finB)
