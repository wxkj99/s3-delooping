{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.CoverDegreeFromH2 where

-- Derive cover degree from four H₂ charts and three H₂ naturality squares.
-- The H₃ charts are constructed jointly from the actual boundary sequences.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
import Cubical.Data.Int as Z
open import Cubical.Data.Bool using (false)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup using (kerGroup)
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup ; ℤHom)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.CW.Homology.Base using (H̃ᶜʷ→comp ; H̃ᶜʷ→Equiv)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.Recognition.Notation using (CW₀ ; H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.CofibreHomology using (Exact₃ ; cellular-map-agrees)
open import DeloopS3.Bridge.DMCExactness.Geometric using (SpanSequenceData)
open import DeloopS3.Bridge.Profile.BaseSeifert.Groups using (module KernelSequence ; module ChangeKernel)
open import DeloopS3.Bridge.CoverChains.Incidence using
  (Tori ; RoseEdges ; Dhat ; constant ; ones ; cover-kernel ; kernel-constant)
open import DeloopS3.Bridge.CoverChains.Complex using (U₂ ; F₃-ones)
import DeloopS3.Bridge.CoverChains.OrbitSums as Orbits
import DeloopS3.Bridge.SeifertChains.Matrices as Base
open import DeloopS3.Cert.Interpret.Short using (ShortCase ; octa ; icosa)
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Input
import DeloopS3.Cert.Input.Initial.Endpoint as Init
import DeloopS3.Bridge.DegreeSpan.Map as Map
import DeloopS3.Bridge.DegreeSpan.Pieces as Pieces
import DeloopS3.Bridge.DegreeSpan.InitialBoundaryNatural as Natural
import DeloopS3.Bridge.OriginalSpan as OS
import DeloopS3.Bridge.Profile.Facts as Facts
open import DeloopS3.Bridge.Profile.FromCoverDegree using (CoverDegreeInput)

open IsGroupHom

-- Elaborate the record with neutral groups before inserting cellular H2.
private
  module Comparisons
    (Os Ot Ls Lt : ShortCase → Group₀)
    (ls : (c : ShortCase) → GroupHom (Os c) (Ls c))
    (lt : (c : ShortCase) → GroupHom (Ot c) (Lt c))
    (o : (c : ShortCase) → GroupHom (Os c) (Ot c)) where
    record CoverH2Comparisons (c : ShortCase) : Type₀ where
      field
        eOs : GroupEquiv (Os c) (AbGroup→Group (Tori c))
        eOt : GroupEquiv (Ot c) (AbGroup→Group Base.ℤ³)
        eLs : GroupEquiv (Ls c) (AbGroup→Group (RoseEdges c))
        eLt : GroupEquiv (Lt c) (AbGroup→Group Base.ℤ²)
        source-left : (x : fst (Os c))
          → equivFun (fst eLs) (fst (ls c) x)
            ≡ fst (Dhat c) (equivFun (fst eOs) x)
        target-left : (x : fst (Ot c))
          → equivFun (fst eLt) (fst (lt c) x)
            ≡ fst Base.D (equivFun (fst eOt) x)
        overlap-cover : (x : fst (Os c))
          → equivFun (fst eOt) (fst (o c) x)
            ≡ fst (U₂ c) (equivFun (fst eOs) x)

open Comparisons
  (λ c → H̃ᶜʷ (Pieces.O₀CW c) 2)
  (λ c → H̃ᶜʷ (Pieces.OᵦCW c) 2)
  (λ c → H̃ᶜʷ (Pieces.L₀CW c) 2)
  (λ c → H̃ᶜʷ (Pieces.LᵦCW c) 2)
  (λ c → H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.L₀CW c} 2 (R.left (Input.S₀ c)))
  (λ c → H̃ᶜʷ→ {C = Pieces.OᵦCW c} {D = Pieces.LᵦCW c} 2 (R.Span.left (Input.BaseSpan c)))
  (λ c → H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.OᵦCW c} 2 (Map.πO c))
  public using (CoverH2Comparisons)

private
  -- Projection to the left factor is an equivalence when the right
  -- factor vanishes.  This uses no coordinate choice for that factor.
  drop-right : (B C : Group₀) → isContr (fst C) → GroupEquiv (DirProd B C) B
  drop-right B C z = isoToEquiv i , makeIsGroupHom (λ _ _ → refl)
    where
    i : Iso (fst (DirProd B C)) (fst B)
    Iso.fun i = fst
    Iso.inv i b = b , fst z
    Iso.sec i _ = refl
    Iso.ret i (b , c) = ΣPathP (refl , snd z c)

  module LeftKernel {V P A B C A′ B′ : Group₀}
    (u : GroupHom V P) (δ : GroupHom P A)
    (s : GroupHom A (DirProd B C)) (d : GroupHom A′ B′)
    (atP : Exact₃ u δ) (atA : Exact₃ δ s)
    (vzero : isContr (fst V)) (czero : isContr (fst C))
    (eA : GroupEquiv A A′) (eB : GroupEquiv B B′)
    (square : (a : fst A) → equivFun (fst eB) (fst (fst s a))
      ≡ fst d (equivFun (fst eA) a)) where
    module K = KernelSequence u δ s atP atA vzero
    module Change = ChangeKernel eA (compGroupEquiv (drop-right B C czero) eB) s d square
    abstract
      kernel : GroupEquiv P (kerGroup d)
      kernel = compGroupEquiv K.kernel-equiv Change.kernel-change

      coordinate : (x : fst P)
        → fst (equivFun (fst kernel) x) ≡ equivFun (fst eA) (fst δ x)
      coordinate x = Change.kernel-change-coordinate (equivFun (fst K.kernel-equiv) x)
        ∙ cong (equivFun (fst eA)) (K.kernel-equiv-coordinate x)

  -- Integer homomorphisms are determined by +1, including negative inputs.
  abstract
    integer-hom-ext : {G : Group₀} (f g : GroupHom ℤGroup G)
      → fst f (pos 1) ≡ fst g (pos 1) → (t : ℤ) → fst f t ≡ fst g t
    integer-hom-ext {G} f g one = all
      where
      positive : (n : ℕ) → fst f (pos n) ≡ fst g (pos n)
      positive zero = pres1 (snd f) ∙ sym (pres1 (snd g))
      positive (suc n) = pres· (snd f) (pos n) (pos 1)
        ∙ cong₂ (GroupStr._·_ (snd G)) (positive n) one
        ∙ sym (pres· (snd g) (pos n) (pos 1))
      all : (t : ℤ) → fst f t ≡ fst g t
      all (pos n) = positive n
      all (negsuc n) = presinv (snd f) (pos (suc n))
        ∙ cong (GroupStr.inv (snd G)) (positive (suc n))
        ∙ sym (presinv (snd g) (pos (suc n)))

  third : GroupHom (AbGroup→Group Base.ℤ³) ℤGroup
  fst third v = snd (snd v)
  snd third = makeIsGroupHom λ _ _ → refl

  constant-hom : (c : ShortCase) → GroupHom ℤGroup (AbGroup→Group (Tori c))
  fst (constant-hom c) = constant c
  snd (constant-hom c) = makeIsGroupHom λ _ _ → refl

  abstract
    orbit-N : (c : ShortCase) → Orbits.N c ≡ OS.N c
    orbit-N octa = refl
    orbit-N icosa = refl

    sum-constant : (c : ShortCase) (t : ℤ)
      → fst third (fst (U₂ c) (constant c t)) ≡ pos (OS.N c) Z.· t
    sum-constant c = integer-hom-ext
      (compGroupHom (constant-hom c) (compGroupHom (U₂ c) third))
      (ℤHom (pos (OS.N c)))
      (cong (fst third) (F₃-ones c) ∙ cong pos (orbit-N c)
        ∙ sym (Z.·IdR (pos (OS.N c))))

  -- This is the entire degree argument, on neutral groups.  Neither an
  -- H3 equation nor an all-degree comparison is an input.
  module Degree (c : ShortCase) {Ps Pt Os Ot : Group₀}
    (δs : GroupHom Ps Os) (δt : GroupHom Pt Ot)
    (p : GroupHom Ps Pt) (o : GroupHom Os Ot)
    (eOs : GroupEquiv Os (AbGroup→Group (Tori c)))
    (eOt : GroupEquiv Ot (AbGroup→Group Base.ℤ³))
    (ks : GroupEquiv Ps (kerGroup (Dhat c)))
    (kt : GroupEquiv Pt (kerGroup Base.D))
    (cs : (x : fst Ps) → fst (equivFun (fst ks) x) ≡ equivFun (fst eOs) (fst δs x))
    (ct : (x : fst Pt) → fst (equivFun (fst kt) x) ≡ equivFun (fst eOt) (fst δt x))
    (square : (x : fst Os) → equivFun (fst eOt) (fst o x)
      ≡ fst (U₂ c) (equivFun (fst eOs) x))
    (natural : compGroupHom p δt ≡ compGroupHom δs o) where

    eS : GroupEquiv Ps ℤGroup
    eS = compGroupEquiv ks (cover-kernel c)
    eT : GroupEquiv Pt ℤGroup
    eT = compGroupEquiv kt Base.D-kernel

    abstract
      source-coordinate : (x : fst Ps)
        → equivFun (fst eOs) (fst δs x) ≡ constant c (equivFun (fst eS) x)
      source-coordinate x = sym (cs x)
        ∙ kernel-constant c (fst (equivFun (fst ks) x)) (snd (equivFun (fst ks) x))

      degree : (x : fst Ps) → equivFun (fst eT) (fst p x)
        ≡ pos (OS.N c) Z.· equivFun (fst eS) x
      degree x = cong (fst third) (ct (fst p x))
        ∙ cong (fst third ∘ equivFun (fst eOt)) (funExt⁻ (cong fst natural) x)
        ∙ cong (fst third) (square (fst δs x))
        ∙ cong (fst third ∘ fst (U₂ c)) (source-coordinate x)
        ∙ sum-constant c (equivFun (fst eS) x)

  module SequenceTop (A B C P : ℕ → Group₀)
    (source : (n : ℕ) → fst (A n) → fst (DirProd (B n) (C n)))
    (vertices : (n : ℕ) → fst (DirProd (B n) (C n)) → fst (P n))
    (L : SpanSequenceData A B C P source vertices)
    {A′ B′ : Group₀} (d : GroupHom A′ B′)
    (eA : GroupEquiv (A 2) A′) (eB : GroupEquiv (B 2) B′)
    (bzero : isContr (fst (B 3))) (czero : isContr (fst (C 3)))
    (c₂zero : isContr (fst (C 2)))
    (square : (a : fst (A 2)) → equivFun (fst eB) (fst (source 2 a))
      ≡ fst d (equivFun (fst eA) a)) where
    private
      module L = SpanSequenceData L
      module K = LeftKernel (L.sum-map 3) (L.boundary 2) (L.source-map 2) d
        (L.exact-total 2 (2 , refl)) (L.exact-source 2 (2 , refl))
        (isContrΣ bzero (λ _ → czero)) c₂zero eA eB
        (λ a → cong (equivFun (fst eB) ∘ fst) (L.source-agrees 2 a) ∙ square a)
    open K public using (kernel ; coordinate)

  record DegreeData (A C : Group₀) (p : GroupHom A C) (n : ℕ) : Type₀ where
    field
      source-equiv : GroupEquiv A ℤGroup
      target-equiv : GroupEquiv C ℤGroup
      degree-law : (x : fst A) → equivFun (fst target-equiv) (fst p x)
        ≡ pos n Z.· equivFun (fst source-equiv) x

  abstract
    rechart : {A C S T : Group₀} {p : GroupHom A C} {q : GroupHom S T} {n : ℕ}
      (a : GroupEquiv A S) (b : GroupEquiv C T)
      → compGroupHom p (GroupEquiv→GroupHom b)
        ≡ compGroupHom (GroupEquiv→GroupHom a) q
      → DegreeData S T q n → DegreeData A C p n
    DegreeData.source-equiv (rechart a b square d) =
      compGroupEquiv a (DegreeData.source-equiv d)
    DegreeData.target-equiv (rechart a b square d) =
      compGroupEquiv b (DegreeData.target-equiv d)
    DegreeData.degree-law (rechart a b square d) x =
      cong (equivFun (fst (DegreeData.target-equiv d))) (funExt⁻ (cong fst square) x)
      ∙ DegreeData.degree-law d (equivFun (fst a) x)

    -- Four-space functoriality, with cellular-map only on the actual p.
    homology-square : (A C S T : CW₀)
      (a : fst A ≃ fst S) (b : fst C ≃ fst T)
      (p : fst A → fst C) (q : fst S → fst T)
      → ((x : fst A) → equivFun b (p x) ≡ q (equivFun a x))
      → compGroupHom (DeloopS3.Bridge.CofibreHomology.cellular-map A C 3 p)
          (GroupEquiv→GroupHom (H̃ᶜʷ→Equiv {C = C} {D = T} 3 b))
        ≡ compGroupHom (GroupEquiv→GroupHom (H̃ᶜʷ→Equiv {C = A} {D = S} 3 a))
          (H̃ᶜʷ→ {C = S} {D = T} 3 q)
    homology-square A C S T a b p q square =
      cong (λ h → compGroupHom h (H̃ᶜʷ→ {C = C} {D = T} 3 (equivFun b)))
        (cellular-map-agrees A C 3 p)
      ∙ sym (H̃ᶜʷ→comp {C = A} {D = C} {E = T} 3 (equivFun b) p)
      ∙ cong (H̃ᶜʷ→ {C = A} {D = T} 3) (funExt square)
      ∙ H̃ᶜʷ→comp {C = A} {D = S} {E = T} 3 q (equivFun a)

  module ForCase (c : ShortCase) (h : CoverH2Comparisons c)
    (joint : Natural.InitialBoundaryNatural c) where
    private
      module H = CoverH2Comparisons h
      sourceLES = fst joint
      targetLES = fst (snd joint)
      module S = SpanSequenceData (snd sourceLES)
      module T = SpanSequenceData (snd targetLES)

      abstract
        source-square : (x : fst (H̃ᶜʷ (Pieces.O₀CW c) 2))
          → equivFun (fst H.eLs)
              (fst (DeloopS3.Bridge.DMCExactness.Geometric.actual-source
                (Pieces.O₀CW c) (Pieces.L₀CW c) (Pieces.R₀CW c)
                (R.left (Input.S₀ c)) (R.right (Input.S₀ c)) 2 x))
            ≡ fst (Dhat c) (equivFun (fst H.eOs) x)
        source-square x = cong (equivFun (fst H.eLs))
          (funExt⁻ (cong fst (cellular-map-agrees (Pieces.O₀CW c) (Pieces.L₀CW c)
            2 (R.left (Input.S₀ c)))) x) ∙ H.source-left x

        target-square : (x : fst (H̃ᶜʷ (Pieces.OᵦCW c) 2))
          → equivFun (fst H.eLt)
              (fst (DeloopS3.Bridge.DMCExactness.Geometric.actual-source
                (Pieces.OᵦCW c) (Pieces.LᵦCW c) (Pieces.RᵦCW c)
                (R.Span.left (Input.BaseSpan c)) (R.Span.right (Input.BaseSpan c)) 2 x))
            ≡ fst Base.D (equivFun (fst H.eOt) x)
        target-square x = cong (equivFun (fst H.eLt))
          (funExt⁻ (cong fst (cellular-map-agrees (Pieces.OᵦCW c) (Pieces.LᵦCW c)
            2 (R.Span.left (Input.BaseSpan c)))) x) ∙ H.target-left x

      module KS = SequenceTop
        (H̃ᶜʷ (Pieces.O₀CW c)) (H̃ᶜʷ (Pieces.L₀CW c)) (H̃ᶜʷ (Pieces.R₀CW c))
        (H̃ᶜʷ (Natural.source-CW c)) _ _ (snd sourceLES)
        (Dhat c) H.eOs H.eLs
        (Pieces.initial-left-H₃-zero c) (Pieces.initial-right-H₃-zero c)
        (Pieces.initial-right-H₂-zero c) source-square
      module KT = SequenceTop
        (H̃ᶜʷ (Pieces.OᵦCW c)) (H̃ᶜʷ (Pieces.LᵦCW c)) (H̃ᶜʷ (Pieces.RᵦCW c))
        (H̃ᶜʷ (Natural.target-CW c)) _ _ (snd targetLES)
        Base.D H.eOt H.eLt
        (Pieces.base-left-H₃-zero c) (Pieces.base-right-H₃-zero c)
        (Pieces.base-right-H₂-zero c) target-square
      module D = Degree c (S.boundary 2) (T.boundary 2)
        (H̃ᶜʷ→ {C = Natural.source-CW c} {D = Natural.target-CW c} 3 (Init.initialProjection c))
        (H̃ᶜʷ→ {C = Pieces.O₀CW c} {D = Pieces.OᵦCW c} 2 (Map.πO c))
        H.eOs H.eOt KS.kernel KT.kernel KS.coordinate KT.coordinate
        H.overlap-cover (snd (snd joint))

    abstract
      initial-degree : DegreeData (H̃ᶜʷ (Natural.source-CW c) 3)
        (H̃ᶜʷ (Natural.target-CW c) 3)
        (H̃ᶜʷ→ {C = Natural.source-CW c} {D = Natural.target-CW c} 3 (Init.initialProjection c))
        (OS.N c)
      DegreeData.source-equiv initial-degree = D.eS
      DegreeData.target-equiv initial-degree = D.eT
      DegreeData.degree-law initial-degree = D.degree

      actual-degree : DegreeData (H̃ᶜʷ (Facts.ACW c) 3)
        (H̃ᶜʷ (Facts.CCW c) 3) (Facts.pH c 3) (OS.N c)
      actual-degree = rechart
        (H̃ᶜʷ→Equiv {C = Facts.ACW c} {D = Natural.source-CW c} 3 (Map.A≃I c))
        (H̃ᶜʷ→Equiv {C = Facts.CCW c} {D = Natural.target-CW c} 3 (Input.originalTotalEquiv c))
        (homology-square (Facts.ACW c) (Facts.CCW c) (Natural.source-CW c) (Natural.target-CW c)
          (Map.A≃I c) (Input.originalTotalEquiv c) (OS.p c) (Init.initialProjection c)
          (Map.outer-right c)) initial-degree

  ActualDegree : ShortCase → Type₀
  ActualDegree c = DegreeData (H̃ᶜʷ (Facts.ACW c) 3)
    (H̃ᶜʷ (Facts.CCW c) 3) (Facts.pH c 3) (OS.N c)

  both : {F : ShortCase → Type₀} → F octa → F icosa → (c : ShortCase) → F c
  both o i octa = o
  both o i icosa = i

  assemble : ((c : ShortCase) → ActualDegree c) → CoverDegreeInput
  CoverDegreeInput.eA (assemble d) c = DegreeData.source-equiv (d c)
  CoverDegreeInput.eC (assemble d) c = DegreeData.target-equiv (d c)
  CoverDegreeInput.sign (assemble d) c = false
  CoverDegreeInput.degree (assemble d) c = DegreeData.degree-law (d c)

  abstract
    case-degree : (c : ShortCase) → PT.∥ CoverH2Comparisons c ∥₁ → PT.∥ ActualDegree c ∥₁
    case-degree c h = PT.map2 (λ h j → ForCase.actual-degree c h j)
      h (Natural.initial-boundary-natural c)

abstract
  -- The input is exactly four H2 equivalences and three H2 squares per
  -- case, under PT.  The LES choices and both derived H3 charts remain
  -- jointly truncated all the way to the existing final consumer.
  cover-degree-from-H2 : ((c : ShortCase) → PT.∥ CoverH2Comparisons c ∥₁)
    → PT.∥ CoverDegreeInput ∥₁
  cover-degree-from-H2 h = PT.map2 (λ o i → assemble (both o i))
    (case-degree octa (h octa)) (case-degree icosa (h icosa))
