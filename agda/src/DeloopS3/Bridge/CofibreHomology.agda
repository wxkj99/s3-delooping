{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CofibreHomology where

-- Cofibre exact-sequence interfaces and Moore homology computed from
-- the actual bouquet-cofibre skeleton. Profile.CofibreLES constructs the
-- finite cofibre sequence; MooreMarked identifies the bottom generators.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; +-comm)
open import Cubical.Data.Nat.Order using (_<_ ; ¬-<-zero)
import Cubical.Data.Empty as Empty
import Cubical.HITs.SetQuotients as SQ
open import Cubical.Data.Int using (ℤ ; pos ; abs ; ·IdL ; +Comm)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (Fin ; fzero ; isContrFin1 ; ¬Fin0)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr ; push ; pushoutEquiv)
open import Cubical.HITs.Sn using (S₊ ; ptSn)
open import Cubical.HITs.Sn.Degree using (degree)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal ; bouquetDegree ; bouquetDegreeSusp)
open import Cubical.CW.Base using (CWskel ; realise)
open import Cubical.CW.ChainComplex using (H̃ˢᵏᵉˡ ; ∂ ; CW-AugChainComplex )
open import Cubical.Algebra.ChainComplex.Base using (ChainComplex)
open import Cubical.Algebra.ChainComplex.Homology using (homology)
open import Cubical.CW.Instances.SphereBouquetMap using
  (SphereBouquet/ˢᵏᵉˡ ; SphereBouquet/ᶜʷ ; hasCWskelSphereBouquet/)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→Equiv)
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap using
  (ℤ[]/ImSphereMap ; GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap
  ; bouquetSusp→Charac)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Algebra.Group.ZAction using (ℤ/imIso ; imℤHomSubGroup)
open import Cubical.Algebra.Group.QuotientGroup using (_/_ ; Hom/ImIso)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import DeloopS3.Bridge.FiniteDim public
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.Recognition.Degree
open import DeloopS3.Local.Powers using (degSphere)
import Cubical.HITs.PropositionalTruncation as PT

Exact₃ : {G H K : Group₀} → GroupHom G H → GroupHom H K → Type
Exact₃ {H = H} {K = K} u v = (h : fst H) →
  (fst v h ≡ GroupStr.1g (snd K)) ≃ PT.∥ fiber (fst u) h ∥₁

private
  -- A one-petal bouquet, with its oriented sphere as an explicit retract.
  one-petal : (n : ℕ) → SphereBouquet n (Fin 1) → S₊ n
  one-petal n = pickPetal fzero

  one-in : (n : ℕ) → S₊ n → SphereBouquet n (Fin 1)
  one-in n x = inr (fzero , x)

  one-ret : (n : ℕ) (x : SphereBouquet n (Fin 1))
    → one-in n (one-petal n x) ≡ x
  one-ret n (inl tt) = sym (push fzero)
  one-ret n (inr ((zero , tt) , x)) = refl
  one-ret n (push (zero , tt) i) j = push fzero (i ∨ ~ j)

  abstract
    one-equiv : (n : ℕ) → SphereBouquet n (Fin 1) ≃ S₊ n
    one-equiv n = isoToEquiv (iso (one-petal n) (one-in n) (λ _ → refl) (one-ret n))

  one-map : {n : ℕ} → (S₊ (suc n) → S₊ (suc n)) → FinSphereBouquetMap 1 1 n
  one-map {n} f = one-in (suc n) ∘ f ∘ one-petal (suc n)

  abstract
    one-cofibre : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
      → cofib (one-map f) ≃ cofib f
    one-cofibre {n} f = pushoutEquiv (λ _ → tt) (one-map f) (λ _ → tt) f
      (one-equiv (suc n)) (idEquiv Unit) (one-equiv (suc n)) refl refl

  eval-iso : GroupIso (AbGroup→Group ℤ[Fin 1 ]) ℤGroup
  Iso.fun (fst eval-iso) r = r fzero
  Iso.inv (fst eval-iso) z = λ _ → z
  Iso.sec (fst eval-iso) z = refl
  Iso.ret (fst eval-iso) r = funExt λ x → cong r (snd isContrFin1 x)
  snd eval-iso = makeIsGroupHom λ _ _ → refl

  conjugate-degree : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
    → GroupHom ℤGroup ℤGroup
  conjugate-degree f = compGroupHom (GroupIso→GroupHom (invGroupIso eval-iso))
    (compGroupHom (bouquetDegree (one-map f)) (GroupIso→GroupHom eval-iso))

  abstract
    conjugate-degree-one : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
      → fst (conjugate-degree f) (pos 1) ≡ degree (suc n) f
    conjugate-degree-one f = ·IdL _

    one-cokernel : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n)) (m : ℕ)
      → degree (suc n) f ≡ pos m
      → GroupEquiv (ℤ[]/ImSphereMap (one-map f)) (ℤGroup/ m)
    one-cokernel f m deg = GroupIso→GroupEquiv
      (compGroupIso
        (Hom/ImIso (bouquetDegree (one-map f)) (conjugate-degree f)
          eval-iso eval-iso
          (λ r → cong (λ s → fst (bouquetDegree (one-map f)) s fzero)
            (Iso.ret (fst eval-iso) r)))
        (subst (λ z → GroupIso (ℤGroup / imℤHomSubGroup (conjugate-degree f))
                    (ℤGroup/ abs z))
          (conjugate-degree-one f ∙ deg) (ℤ/imIso (conjugate-degree f))))

    sphere-cofibre-bottom : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
      (X : CW₀) → fst X ≡ cofib f → (m : ℕ)
      → degree (suc n) f ≡ pos m
      → GroupEquiv (H̃ᶜʷ X (suc n)) (ℤGroup/ m)
    sphere-cofibre-bottom {n} f X p m deg =
      compGroupEquiv
        (H̃ᶜʷ→Equiv {C = X} {D = SphereBouquet/ᶜʷ (one-map f)} (suc n)
          (compEquiv (pathToEquiv p) (invEquiv (one-cofibre f))))
        (compGroupEquiv
          (GroupIso→GroupEquiv (GroupIso-Hₙ₊₁SphereBouquetⁿ/→ℤ[]/ImSphereMap (one-map f)))
          (one-cokernel f m deg))

abstract
  bottom-H₂ : GroupEquiv (H̃ᶜʷ bottomCW 2) (ℤGroup/ 2)
  bottom-H₂ = sphere-cofibre-bottom (degSphere 2 1) bottomCW refl 2
    (degree-degSphere-S² 2)

  -- Positivity is not needed for the bottom group: ℤGroup/ 0 is ℤGroup.
  moore3-H₃ : (m : ℕ) → 0 < m
    → GroupEquiv (H̃ᶜʷ (moore3CW m) 3) (ℤGroup/ m)
  moore3-H₃ m _ = sphere-cofibre-bottom (degSphere m 2) (moore3CW m) refl m
    (degree-degSphere-S³ m)

private
  abstract
    top-boundary₂ : (α : FinSphereBouquetMap 1 1 1)
      → α (inl tt) ≡ inl tt
      → ∂ (SphereBouquet/ˢᵏᵉˡ α) 2 ≡ bouquetDegree α
    top-boundary₂ α apt = cong bouquetDegree
      (bouquetSusp→Charac α (λ _ → pos 0) (λ _ → pos 0) apt refl refl)
      ∙ sym (bouquetDegreeSusp α)

    top-boundary₃ : (α : FinSphereBouquetMap 1 1 2)
      → α (inl tt) ≡ inl tt
      → ∂ (SphereBouquet/ˢᵏᵉˡ α) 3 ≡ bouquetDegree α
    top-boundary₃ α apt = cong bouquetDegree
      (bouquetSusp→Charac α (λ _ → pos 0) (λ _ → pos 0) apt refl refl)
      ∙ sym (bouquetDegreeSusp α)

  zero-kernel-homology : (C : ChainComplex ℓ-zero) (k : ℕ)
    → ((x : fst (ChainComplex.chain C (suc k)))
      → fst (ChainComplex.bdry C k) x
          ≡ GroupStr.1g (snd (AbGroup→Group (ChainComplex.chain C k)))
      → x ≡ GroupStr.1g (snd (AbGroup→Group (ChainComplex.chain C (suc k)))))
    → isContr (fst (homology k C))
  zero-kernel-homology C k kill = GroupStr.1g (snd (homology k C)) ,
    SQ.elimProp (λ _ → GroupStr.is-set (snd (homology k C)) _ _)
      (λ z → cong SQ.[_] (Σ≡Prop
        (λ _ → GroupStr.is-set (snd (AbGroup→Group (ChainComplex.chain C k))) _ _)
        (sym (kill (fst z) (snd z)))))

  one-degree-kernel : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n)) (m : ℕ)
    → degree (suc n) f ≡ pos (suc m)
    → (r : Fin 1 → ℤ) → fst (bouquetDegree (one-map f)) r ≡ (λ _ → pos 0)
    → r ≡ (λ _ → pos 0)
  one-degree-kernel f m deg r ker = funExt λ x →
    cong r (sym (snd isContrFin1 x))
    ∙ Z.·suc→0 (r fzero) m
        (cong (r fzero Z.·_) (sym deg) ∙ funExt⁻ ker fzero)

  abstract
    sphere-cofibre-vanishing : {n : ℕ} (f : S₊ (suc n) → S₊ (suc n))
      (X : CW₀) → fst X ≡ cofib f → (k : ℕ)
      → isContr (fst (H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ (one-map f)) k))
      → Hzero X k
    sphere-cofibre-vanishing f X p k = isOfHLevelRespectEquiv 0
      (invEquiv (fst (H̃ᶜʷ→Equiv {C = X} {D = SphereBouquet/ᶜʷ (one-map f)} k
        (compEquiv (pathToEquiv p) (invEquiv (one-cofibre f))))))

    moore3-top-zero : (m : ℕ)
      → isContr (fst (H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ (one-map (degSphere (suc m) 2))) 4))
    moore3-top-zero m = zero-kernel-homology
      (CW-AugChainComplex (SphereBouquet/ˢᵏᵉˡ (one-map (degSphere (suc m) 2)))) 4
      λ r ker → one-degree-kernel (degSphere (suc m) 2) m
        (degree-degSphere-S³ (suc m)) r
        (sym (funExt⁻ (cong fst
          (top-boundary₃ (one-map (degSphere (suc m) 2)) (sym (push fzero)))) r) ∙ ker)

    bottom-top-zero :
      isContr (fst (H̃ˢᵏᵉˡ (SphereBouquet/ˢᵏᵉˡ (one-map (degSphere 2 1))) 3))
    bottom-top-zero = zero-kernel-homology
      (CW-AugChainComplex (SphereBouquet/ˢᵏᵉˡ (one-map (degSphere 2 1)))) 3
      λ r ker → one-degree-kernel (degSphere 2 1) 1
        (degree-degSphere-S² 2) r
        (sym (funExt⁻ (cong fst
          (top-boundary₂ (one-map (degSphere 2 1)) (sym (push fzero)))) r) ∙ ker)

abstract
  moore3-H₄ : (m : ℕ) → 0 < m → Hzero (moore3CW m) 4
  moore3-H₄ zero p = Empty.rec (¬-<-zero p)
  moore3-H₄ (suc m) _ = sphere-cofibre-vanishing
    (degSphere (suc m) 2) (moore3CW (suc m)) refl 4 (moore3-top-zero m)

  bottom-H≥3 : (n : ℕ) → Hzero bottomCW (3 + n)
  bottom-H≥3 zero = sphere-cofibre-vanishing
    (degSphere 2 1) bottomCW refl 3 bottom-top-zero
  bottom-H≥3 (suc n) = finite≤-homology-above bottomCW 3 (3 + suc n)
    bottom-finite≤ (n , +-comm n 4)

  moore3-H≥4 : (m : ℕ) → 0 < m → (n : ℕ) → Hzero (moore3CW m) (4 + n)
  moore3-H≥4 m p zero = moore3-H₄ m p
  moore3-H≥4 m p (suc n) = finite≤-homology-above (moore3CW m) 4 (4 + suc n)
    (moore3-finite≤ m) (n , +-comm n 5)


private
  -- In these skeleta there is one 0-cell, no 1-cells (or, for Moore3,
  -- 2-cells), and the augmentation of the unique 0-cell is one.
  no-cells-homology : (C : CWskel ℓ-zero) (k : ℕ)
    → C .snd .fst k ≡ 0 → isContr (fst (H̃ˢᵏᵉˡ C k))
  no-cells-homology C k p = zero-kernel-homology (CW-AugChainComplex C) k
    λ x _ → subst (λ r → (x : Fin r → ℤ) → x ≡ (λ _ → pos 0))
      (sym p) (λ x → funExt λ y → Empty.rec (¬Fin0 y)) x

  one-vertex-homology : (C : CWskel ℓ-zero)
    → C .snd .fst 0 ≡ 1 → isContr (fst (H̃ˢᵏᵉˡ C 0))
  one-vertex-homology C p = zero-kernel-homology (CW-AugChainComplex C) 0
    λ x ker → subst (λ r → (x : Fin r → ℤ)
      → Z.sumFinℤ x ≡ pos 0 → x ≡ (λ _ → pos 0)) (sym p)
      (λ x q → funExt λ y → cong x (sym (snd isContrFin1 y)) ∙ q) x
      (sym (funExt⁻ (funExt⁻ (cong fst (Cubical.CW.ChainComplex.augmentation.ϵ-alt C)) x) fzero)
        ∙ funExt⁻ ker fzero)

abstract
  bottom-H₀ : Hzero bottomCW 0
  bottom-H₀ = sphere-cofibre-vanishing (degSphere 2 1) bottomCW refl 0
    (one-vertex-homology (SphereBouquet/ˢᵏᵉˡ (one-map (degSphere 2 1))) refl)

  bottom-H₁ : Hzero bottomCW 1
  bottom-H₁ = sphere-cofibre-vanishing (degSphere 2 1) bottomCW refl 1
    (no-cells-homology (SphereBouquet/ˢᵏᵉˡ (one-map (degSphere 2 1))) 1 refl)

  moore3-H₀ : (m : ℕ) → Hzero (moore3CW m) 0
  moore3-H₀ m = sphere-cofibre-vanishing (degSphere m 2) (moore3CW m) refl 0
    (one-vertex-homology (SphereBouquet/ˢᵏᵉˡ (one-map (degSphere m 2))) refl)

  moore3-H₁ : (m : ℕ) → Hzero (moore3CW m) 1
  moore3-H₁ m = sphere-cofibre-vanishing (degSphere m 2) (moore3CW m) refl 1
    (no-cells-homology (SphereBouquet/ˢᵏᵉˡ (one-map (degSphere m 2))) 1 refl)

  moore3-H₂ : (m : ℕ) → Hzero (moore3CW m) 2
  moore3-H₂ m = sphere-cofibre-vanishing (degSphere m 2) (moore3CW m) refl 2
    (no-cells-homology (SphereBouquet/ˢᵏᵉˡ (one-map (degSphere m 2))) 2 refl)

-- The functor implementation uses cellular approximation.  Keep it opaque
-- while checking the record, with an explicit identification with H̃ᶜʷ→.
abstract
  cellular-map : (A B : CW₀) (n : ℕ) (f : fst A → fst B)
    → GroupHom (H̃ᶜʷ A n) (H̃ᶜʷ B n)
  cellular-map A B n f = H̃ᶜʷ→ {C = A} {D = B} n f

  cellular-map-agrees : (A B : CW₀) (n : ℕ) (f : fst A → fst B)
    → cellular-map A B n f ≡ H̃ᶜʷ→ {C = A} {D = B} n f
  cellular-map-agrees A B n f = refl

-- Factoring out the algebra prevents record elaboration from normalizing
-- the implementation of cellular homology (the endpoint groups stay fixed).
record CofibreSequenceData (HA HB HC : ℕ → Group₀)
  (fH : (n : ℕ) → GroupHom (HA n) (HB n))
  (iH : (n : ℕ) → GroupHom (HB n) (HC n)) : Type where
  field
    boundary : (n : ℕ) → GroupHom (HC (suc n)) (HA n)
    exact-cofibre : (n : ℕ) → n < 5
      → Exact₃ {G = HB (suc n)} {H = HC (suc n)} {K = HA n}
          (iH (suc n)) (boundary n)
    exact-source : (n : ℕ) → n < 5
      → Exact₃ {G = HC (suc n)} {H = HA n} {K = HB n}
          (boundary n) (fH n)
    exact-target : (n : ℕ) → n < 5
      → Exact₃ {G = HA n} {H = HB n} {K = HC n} (fH n) (iH n)


-- Specialized interface.  The Sigma packaging avoids expanding H̃ᶜʷ
-- during Agda's record elaboration.  Its first component specifies the
-- actual cofibre; the second is the record of the three exact positions.
CofibreLES : (A B : CW₀) (f : fst A → fst B) (Cf : CW₀) → Type₁
CofibreLES A B f Cf = Σ[ p ∈ (fst Cf ≡ cofib f) ]
  CofibreSequenceData (H̃ᶜʷ A) (H̃ᶜʷ B) (H̃ᶜʷ Cf)
    (λ n → cellular-map A B n f)
    (λ n → cellular-map B Cf n (λ b → transport (sym p) (inr b)))

-- The derived witness retains the defining HIT as its underlying type.
finite-cofibreCW : (A B : CW₀) (f : fst A → fst B) (dA dB : ℕ)
  → Finite≤ dA (fst A) → Finite≤ dB (fst B) → CW₀
finite-cofibreCW A B f dA dB finA finB = cofib f ,
  finite≤→isCW (cofib-finite≤ f dA dB finA finB)

module CofibreLES (A B : CW₀) (f : fst A → fst B) (Cf : CW₀)
  (les : CofibreLES A B f Cf) where
  cofibre-identification : fst Cf ≡ cofib f
  cofibre-identification = fst les

  inclusion : fst B → fst Cf
  inclusion b = transport (sym cofibre-identification) (inr b)

  inclusion-induced : (n : ℕ) → GroupHom (H̃ᶜʷ B n) (H̃ᶜʷ Cf n)
  inclusion-induced n = cellular-map B Cf n inclusion

  inclusion-induced-agrees : (n : ℕ)
    → inclusion-induced n ≡ H̃ᶜʷ→ {C = B} {D = Cf} n inclusion
  inclusion-induced-agrees n = cellular-map-agrees B Cf n inclusion

  map-induced : (n : ℕ) → GroupHom (H̃ᶜʷ A n) (H̃ᶜʷ B n)
  map-induced n = cellular-map A B n f

  map-induced-agrees : (n : ℕ)
    → map-induced n ≡ H̃ᶜʷ→ {C = A} {D = B} n f
  map-induced-agrees n = cellular-map-agrees A B n f

  open CofibreSequenceData (snd les) public


