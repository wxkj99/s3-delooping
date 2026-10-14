{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.EI where

-- Two-stage contraction at the degree-10 circle map, for Moore cofibres
-- and finite bouquets with map-level multiple inverses.
-- The normal-form HIT retains its Hopf attachment.
open import DeloopS3.Local.Kernel
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv ; preCompEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws using (lUnit ; rUnit ; assoc ; cong-∙)
open import Cubical.Foundations.Pointed using (Pointed₀)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_ ; _·_ ; _^_ ; ·-comm)
open import Cubical.Data.Sigma using (Σ-contractSnd ; Σ-cong-equiv-snd ; ΣPathP)
open import Cubical.Data.List.Base using (List ; [] ; _∷_)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.Data.Unit using (Unit ; tt ; isContr→≃Unit)
open import Cubical.HITs.Pushout.Base using (cofib ; inl ; inr ; push)
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.HITs.Susp.Base using (Susp ; north ; south ; merid ; suspFun)
open import Cubical.HITs.Wedge.Base using (_⋁_ ; _⋁∙ₗ_ ; proj⋁ᵣ)
import Cubical.HITs.Bouquet.Base as CB
open import Cubical.HITs.Wedge.Properties using (cofibInl-⋁)
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import Cubical.Homotopy.Hopf using (module S¹Hopf)
open import Cubical.HITs.Sn.Multiplication using (IsoSphereJoin)
open import Cubical.HITs.Sn.Properties using (sphereConnected)
open import Cubical.Homotopy.Connected using
  (isConnected ; isConnectedCofib ; isConnectedFunCancel'
  ; isConnected→isConnectedFun ; isConnectedSubtr ; isConnectedRetractFromIso)

-- The 1-by-1 certificate (2)(5) = (5)(2) = (10) is used on
-- actual loop power maps, not on the homology of a mixed sphere bouquet.
powLoop-+ : {X : Type} {x : X} (a b : ℕ) (p : x ≡ x)
  → powLoop (a + b) p ≡ powLoop a p ∙ powLoop b p
powLoop-+ zero b p = lUnit (powLoop b p)
powLoop-+ (suc a) b p = cong (p ∙_) (powLoop-+ a b p)
  ∙ assoc p (powLoop a p) (powLoop b p)

powLoop-· : {X : Type} {x : X} (a b : ℕ) (p : x ≡ x)
  → powLoop a (powLoop b p) ≡ powLoop (a · b) p
powLoop-· zero b p = refl
powLoop-· (suc a) b p = cong (powLoop b p ∙_) (powLoop-· a b p)
  ∙ sym (powLoop-+ b (a · b) p)

-- Two-sided composites really are required. This lemma makes no
-- inference from a graded matrix and does not assume commutativity.
factor-isEquiv : {X Y : Type} (f : X → Y) (g : Y → X)
  → isEquiv (f ∘ g) → isEquiv (g ∘ f) → isEquiv f
factor-isEquiv f g fg gf = isoToIsEquiv
  (iso f (g ∘ invEq (f ∘ g , fg)) (secEq (f ∘ g , fg))
    (λ x → invEq (congEquiv (g ∘ f , gf))
      (cong g (secEq (f ∘ g , fg) (f x)))))

local-factor : {m d b : ℕ} {Z : Type}
  → d · b ≡ m → Local m Z → Local d Z
local-factor {m} {d} {b} {Z} db lZ = powers→local λ z →
  factor-isEquiv (powLoop {x = z} d) (powLoop b)
    (subst isEquiv (sym (funExt (λ p →
      powLoop-· d b p ∙ cong (λ n → powLoop n p) db)))
      (local→powers lZ z))
    (subst isEquiv (sym (funExt (λ p →
      powLoop-· b d p ∙ cong (λ n → powLoop n p) (·-comm b d ∙ db))))
      (local→powers lZ z))

-- The denominator-clearing version of the certificate.
local-power : {m : ℕ} {Z : Type} → Local m Z → (k : ℕ) → Local (m ^ k) Z
local-power {m} {Z} lZ zero = powers→local λ z →
  subst isEquiv (sym (funExt (λ p → sym (rUnit p)))) (snd (idEquiv (z ≡ z)))
local-power {m} {Z} lZ (suc k) = powers→local λ z →
  subst isEquiv (funExt (powLoop-· m (m ^ k)))
    (snd (compEquiv
      (powLoop (m ^ k) , local→powers (local-power lZ k) z)
      (powLoop m , local→powers lZ z)))

local-divides-power : {m d b : ℕ} {Z : Type} (k : ℕ)
  → d · b ≡ m ^ k → Local m Z → Local d Z
local-divides-power k db lZ = local-factor db (local-power lZ k)

local10→local2 : {Z : Type} → Local 10 Z → Local 2 Z
local10→local2 = local-factor {b = 5} refl

Moore : ℕ → ℕ → Type
Moore d n = cofib (degSphere d n)
-- SphereFromCircle 1 = S²; SphereFromCircle 2 = S³.
BottomMoore TopMoore : Type
BottomMoore = Moore 2 1
TopMoore = Moore 10 2

-- This mapping-space formulation is stronger than merely asserting
-- pointwise nullhomotopies: it retains the coherences for the pullback.
LocalNull : ℕ → Type → Type₁
LocalNull m A = (Z : Type) → Local m Z
  → isEquiv (λ (z : Z) (_ : A) → z)

moore-local-null : {m d b : ℕ} (k n : ℕ)
  → d · b ≡ m ^ k → LocalNull m (Moore d n)
moore-local-null {d = d} k n db Z lZ = cofib-const-isEquiv
  (degSphere d n) (local-sphere (local-divides-power k db lZ) n)

bottom-local-null : LocalNull 10 BottomMoore
bottom-local-null Z lZ = cofib-const-isEquiv
  (degSphere 2 1) (local-sphere (local10→local2 lZ) 1)

top-local-null : LocalNull 10 TopMoore
top-local-null Z lZ = cofib-const-isEquiv
  (degSphere 10 2) (local-sphere lZ 2)

local-null→contr : {m : ℕ} {A : Type} → LocalNull m A → isContr (L m A)
local-null→contr {m} {A} null = unit-null→contr
  PT.∣ invEq constants η , sym (secEq constants η) ∣₁
  where
  constants : L m A ≃ (A → L m A)
  constants = (λ z _ → z) , null (L m A) (local-L m A)

bottom-contr : isContr (L 10 BottomMoore)
bottom-contr = local-null→contr bottom-local-null

top-contr : isContr (L 10 TopMoore)
top-contr = local-null→contr top-local-null

-- The other ordering of the cofibre mapping-space pullback.
-- The first projection below is LITERALLY restriction along inr.
cofib-restriction-Iso : {A E Z : Type} (a : A → E)
  → Iso (cofib a → Z)
      (Σ[ g ∈ (E → Z) ] fiber (λ (z : Z) (_ : A) → z) (g ∘ a))
Iso.fun (cofib-restriction-Iso a) h =
  h ∘ inr , h (inl tt) , (λ i x → h (push x i))
Iso.inv (cofib-restriction-Iso a) (g , z , p) (inl tt) = z
Iso.inv (cofib-restriction-Iso a) (g , z , p) (inr x) = g x
Iso.inv (cofib-restriction-Iso a) (g , z , p) (push x i) = p i x
Iso.sec (cofib-restriction-Iso a) (g , z , p) = refl
Iso.ret (cofib-restriction-Iso a) h = funExt λ
  { (inl tt) → refl ; (inr x) → refl ; (push x i) → refl }

cofib-inr-localEquiv : {m : ℕ} {A E : Type} (a : A → E)
  → LocalNull m A → LocalEquiv m (inr {f = λ (_ : A) → tt} {g = a})
cofib-inr-localEquiv a nullA Z lZ = snd (compEquiv
  (isoToEquiv (cofib-restriction-Iso a))
  (Σ-contractSnd λ g → equiv-proof (nullA Z lZ) (g ∘ a)))

-- Two-stage argument: remove A, then contract its actual
-- homotopy cofibre. There is no assertion that E was 2-connected.
two-stage-local-null : {m : ℕ} {A E : Type} (a : A → E)
  → LocalNull m A → LocalNull m (cofib a) → LocalNull m E
two-stage-local-null a nullA nullF Z lZ = snd (compEquiv
  ((λ z _ → z) , nullF Z lZ)
  ((λ h → h ∘ inr) , cofib-inr-localEquiv a nullA Z lZ))

two-stage-contr : {m : ℕ} {A E : Type} (a : A → E)
  → LocalNull m A → LocalNull m (cofib a) → isContr (L m E)
two-stage-contr a nullA nullF =
  local-null→contr (two-stage-local-null a nullA nullF)

local-null-equiv : {m : ℕ} {A B : Type} → A ≃ B
  → LocalNull m B → LocalNull m A
local-null-equiv e nullB Z lZ = snd (compEquiv
  ((λ z _ → z) , nullB Z lZ) (preCompEquiv e))

-- A bottom Moore map with top Moore cofibre contracts after localization.
-- Bridge.Profile.Contraction supplies this comparison for the I profile.
EI-from-bottom-cofibre : {E : Type} (a : BottomMoore → E)
  → cofib a ≃ TopMoore → isContr (L 10 E)
EI-from-bottom-cofibre a e = two-stage-contr a bottom-local-null
  (local-null-equiv e top-local-null)

EI-from-bottom-cofibre≃Unit : {E : Type} (a : BottomMoore → E)
  → cofib a ≃ TopMoore → L 10 E ≃ Unit
EI-from-bottom-cofibre≃Unit a e = isContr→≃Unit (EI-from-bottom-cofibre a e)

-- The finite choices may be made merely.
EI-from-merely-bottom-cofibre : {E : Type}
  → PT.∥ Σ[ a ∈ (BottomMoore → E) ] (cofib a ≃ TopMoore) ∥₁
  → isContr (L 10 E)
EI-from-merely-bottom-cofibre = PT.rec isPropIsContr
  λ { (a , e) → EI-from-bottom-cofibre a e }

-- Coning off two subspaces commutes. This is a HIT isomorphism,
-- not a calculation of homology groups.
cofib-swap-Iso : {A T B : Type} (a : A → B) (t : T → B)
  → Iso (cofib {B = cofib t} (inr ∘ a))
        (cofib {B = cofib a} (inr ∘ t))
Iso.fun (cofib-swap-Iso a t) (inl tt) = inr (inl tt)
Iso.fun (cofib-swap-Iso a t) (inr (inl tt)) = inl tt
Iso.fun (cofib-swap-Iso a t) (inr (inr b)) = inr (inr b)
Iso.fun (cofib-swap-Iso a t) (inr (push x i)) = push x i
Iso.fun (cofib-swap-Iso a t) (push x i) = inr (push x i)
Iso.inv (cofib-swap-Iso a t) (inl tt) = inr (inl tt)
Iso.inv (cofib-swap-Iso a t) (inr (inl tt)) = inl tt
Iso.inv (cofib-swap-Iso a t) (inr (inr b)) = inr (inr b)
Iso.inv (cofib-swap-Iso a t) (inr (push x i)) = push x i
Iso.inv (cofib-swap-Iso a t) (push x i) = inr (push x i)
Iso.sec (cofib-swap-Iso a t) (inl tt) = refl
Iso.sec (cofib-swap-Iso a t) (inr (inl tt)) = refl
Iso.sec (cofib-swap-Iso a t) (inr (inr b)) = refl
Iso.sec (cofib-swap-Iso a t) (inr (push x i)) = refl
Iso.sec (cofib-swap-Iso a t) (push x i) = refl
Iso.ret (cofib-swap-Iso a t) (inl tt) = refl
Iso.ret (cofib-swap-Iso a t) (inr (inl tt)) = refl
Iso.ret (cofib-swap-Iso a t) (inr (inr b)) = refl
Iso.ret (cofib-swap-Iso a t) (inr (push x i)) = refl
Iso.ret (cofib-swap-Iso a t) (push x i) = refl

-- The quotient works for ANY Moore component h.
-- Thus no value of k, no Thom square and no additivity of precomposition
-- with the Hopf map enters the localization argument.
module BottomAttachment (h : SphereFromCircle 2 → BottomMoore) where
  A∙ S³∙ : Pointed₀
  A∙ = BottomMoore , h north
  S³∙ = SphereFromCircle 2 , north

  Skeleton : Type
  Skeleton = A∙ ⋁ S³∙

  left : SphereFromCircle 2 → Skeleton
  left x = inl (h x)

  right : SphereFromCircle 2 → Skeleton
  right x = inr (degSphere 10 2 x)

  bridge : left north ≡ right north
  bridge = push tt

  -- Pinch sum h + 10s on the suspension model S³ = Susp S².
  -- Closing the left meridian along the base meridian makes its poles
  -- coincide; the wedge path then leads to the right summand.
  left-loop : SphereFromCircle 1 → left north ≡ left north
  left-loop x = cong left (merid x) ∙ sym (cong left (merid north))

  attaching : SphereFromCircle 2 → Skeleton
  attaching north = left north
  attaching south = right south
  attaching (merid x i) =
    ((left-loop x ∙ bridge) ∙ cong right (merid x)) i

  Space : Type
  Space = cofib attaching

  bottom-inclusion : BottomMoore → Space
  bottom-inclusion x = inr (inl x)

  collapse : Skeleton → SphereFromCircle 2
  collapse = proj⋁ᵣ

  collapse-left-loop : (x : SphereFromCircle 1)
    → cong collapse (left-loop x) ≡ refl
  collapse-left-loop x =
    cong-∙ collapse (cong left (merid x)) (sym (cong left (merid north)))
    ∙ sym (lUnit refl)

  collapse-attaching-merid : (x : SphereFromCircle 1)
    → cong collapse ((left-loop x ∙ bridge) ∙ cong right (merid x))
      ≡ merid (degSphere 10 1 x)
  collapse-attaching-merid x =
    cong-∙ collapse (left-loop x ∙ bridge) (cong right (merid x))
    ∙ cong (_∙ merid (degSphere 10 1 x))
      (cong-∙ collapse (left-loop x) bridge
       ∙ cong (_∙ refl) (collapse-left-loop x)
       ∙ sym (lUnit refl))
    ∙ sym (lUnit (merid (degSphere 10 1 x)))

  collapse-attaching : collapse ∘ attaching ≡ degSphere 10 2
  collapse-attaching = funExt λ
    { north → refl ; south → refl
    ; (merid x i) j → collapse-attaching-merid x j i }

  collapse-cofib-equiv : cofib {B = Skeleton} inl ≃ SphereFromCircle 2
  collapse-cofib-equiv = isoToEquiv (cofibInl-⋁ {A = A∙} {B = S³∙})

  collapse-agrees : (w : Skeleton)
    → fst collapse-cofib-equiv (inr w) ≡ collapse w
  collapse-agrees (inl a) = refl
  collapse-agrees (inr x) = refl
  collapse-agrees (push tt i) = refl

  bottom-cofibre≃TopMoore : cofib bottom-inclusion ≃ TopMoore
  bottom-cofibre≃TopMoore = compEquiv
    (isoToEquiv (cofib-swap-Iso inl attaching))
    (pushoutEquiv (λ _ → tt) (inr ∘ attaching)
      (λ _ → tt) (degSphere 10 2)
      (idEquiv (SphereFromCircle 2)) (idEquiv Unit)
      collapse-cofib-equiv refl
      (funExt λ x → collapse-agrees (attaching x)
        ∙ funExt⁻ collapse-attaching x))

  localized-contr : isContr (L 10 Space)
  localized-contr = EI-from-bottom-cofibre bottom-inclusion
    bottom-cofibre≃TopMoore

-- The complex Hopf map, using exactly the join/fibration construction
-- underlying Cubical.Homotopy.HopfInvariant.HopfMap.HopfMap. We import
-- its geometric ingredients, not the Thom/cohomology-operation proofs.
hopf : SphereFromCircle 2 → SphereFromCircle 1
hopf x = fst (S¹Hopf.JoinS¹S¹→TotalHopf (Iso.inv (IsoSphereJoin 1 1) x))

-- The normal-form HIT, distinct from the geometric pushout Assembly.Final.EI.
-- Cells (1,0,1,2,1): d(b)=2a and d(u)=ιη+10s. The actual Hopf map
-- remains in the attaching term; this is not the false Hopf-free wedge.
module EIModel = BottomAttachment (inr ∘ hopf)

EI : Type
EI = EIModel.Space

EI-bottom-inclusion : BottomMoore → EI
EI-bottom-inclusion = EIModel.bottom-inclusion

EI-bottom-cofibre≃TopMoore : cofib EI-bottom-inclusion ≃ TopMoore
EI-bottom-cofibre≃TopMoore = EIModel.bottom-cofibre≃TopMoore

EI-contr : isContr (L 10 EI)
EI-contr = EIModel.localized-contr

EI-localized≃Unit : L 10 EI ≃ Unit
EI-localized≃Unit = isContr→≃Unit EI-contr

-- Library connectivity index 4 means 2-connected (contractible
-- 2-truncation). This concerns the cofibre, NOT the unmodified EI.
top-2-connected : isConnected 4 TopMoore
top-2-connected = isConnectedCofib 2
  (isConnectedFunCancel' (degSphere 10 2) (λ _ → tt) 3
    (isConnected→isConnectedFun 4 (sphereConnected 3))
    (isConnected→isConnectedFun 3 (isConnectedSubtr 3 1 (sphereConnected 3))))

EI-bottom-cofibre-2-connected : isConnected 4 (cofib EI-bottom-inclusion)
EI-bottom-cofibre-2-connected = isConnectedRetractFromIso 4
  (equivToIso EI-bottom-cofibre≃TopMoore) top-2-connected

-- Finite two-stage contraction: degree-d Moore spaces with d dividing 10^N,
-- followed by an S³-bouquet map with two-sided multiple-inverse homotopies.

unit-local-null : {m : ℕ} → LocalNull m Unit
unit-local-null Z _ = isoToIsEquiv (iso (λ z _ → z) (λ h → h tt)
  (λ h → funExt λ { tt → refl }) (λ _ → refl))

wedge-local-null : {m : ℕ} {A B : Pointed₀}
  → LocalNull m (fst A) → LocalNull m (fst B) → LocalNull m (A ⋁ B)
wedge-local-null {A = A} {B = B} nullA nullB =
  two-stage-local-null inl nullA
    (local-null-equiv (isoToEquiv (cofibInl-⋁ {A = A} {B = B})) nullB)

record PrimaryDegree (m : ℕ) : Type where
  constructor primaryDegree
  field
    degree multiplier exponent : ℕ
    divides-power : degree · multiplier ≡ m ^ exponent

MooreBouquet : (m : ℕ) → List (PrimaryDegree m) → Pointed₀
MooreBouquet m [] = Unit , tt
MooreBouquet m (d ∷ ds) =
  (Moore (PrimaryDegree.degree d) 1 , inl tt) ⋁∙ₗ MooreBouquet m ds

moore-bouquet-local-null : {m : ℕ} (ds : List (PrimaryDegree m))
  → LocalNull m (fst (MooreBouquet m ds))
moore-bouquet-local-null [] = unit-local-null
moore-bouquet-local-null (d ∷ ds) = wedge-local-null
  (moore-local-null (PrimaryDegree.exponent d) 1 (PrimaryDegree.divides-power d))
  (moore-bouquet-local-null ds)

-- A finite bouquet model suited to the suspension-locality lemma:
-- suspend the finite circle bouquet n times. In the second stage n=2.
-- All spheres in each bouquet have the same dimension.
SphereBouquet : ℕ → ℕ → Type
SphereBouquet zero k = CB.Bouquet (Fin k)
SphereBouquet (suc n) k = Susp (SphereBouquet n k)

circle-bouquet-degree : (m k : ℕ) → CB.Bouquet (Fin k) → CB.Bouquet (Fin k)
circle-bouquet-degree m k CB.base = CB.base
circle-bouquet-degree m k (CB.loop a i) = powLoop m (CB.loop a) i

bouquet-degree : (m n k : ℕ) → SphereBouquet n k → SphereBouquet n k
bouquet-degree m zero k = circle-bouquet-degree m k
bouquet-degree m (suc n) k = suspFun (bouquet-degree m n k)

circle-bouquet-maps-Iso : {Z : Type} (k : ℕ)
  → Iso (CB.Bouquet (Fin k) → Z) (Σ[ z ∈ Z ] (Fin k → z ≡ z))
Iso.fun (circle-bouquet-maps-Iso k) f = f CB.base , λ a → cong f (CB.loop a)
Iso.inv (circle-bouquet-maps-Iso k) (z , p) CB.base = z
Iso.inv (circle-bouquet-maps-Iso k) (z , p) (CB.loop a i) = p a i
Iso.sec (circle-bouquet-maps-Iso k) (z , p) = refl
Iso.ret (circle-bouquet-maps-Iso k) f = funExt λ
  { CB.base → refl ; (CB.loop a i) → refl }

local-circle-bouquet : {m : ℕ} {Z : Type} → Local m Z → (k : ℕ)
  → isEquiv (λ (f : CB.Bouquet (Fin k) → Z) → f ∘ circle-bouquet-degree m k)
local-circle-bouquet {m} {Z} lZ k =
  subst isEquiv (funExt agrees) (snd conjugate)
  where
  maps = circle-bouquet-maps-Iso {Z = Z} k

  total : (Σ[ z ∈ Z ] (Fin k → z ≡ z)) ≃ (Σ[ z ∈ Z ] (Fin k → z ≡ z))
  total = Σ-cong-equiv-snd λ z → equivΠCod λ _ → powLoop m , local→powers lZ z

  conjugate : (CB.Bouquet (Fin k) → Z) ≃ (CB.Bouquet (Fin k) → Z)
  conjugate = compEquiv (isoToEquiv maps)
    (compEquiv total (isoToEquiv (invIso maps)))

  agrees : (f : CB.Bouquet (Fin k) → Z)
    → fst conjugate f ≡ f ∘ circle-bouquet-degree m k
  agrees f = cong (Iso.inv maps)
    (ΣPathP (refl , funExt λ a → sym (cong-powLoop f m (CB.loop a))))
    ∙ Iso.ret maps (f ∘ circle-bouquet-degree m k)

local-bouquet : {m : ℕ} {Z : Type} → Local m Z → (n k : ℕ)
  → isEquiv (λ (f : SphereBouquet n k → Z) → f ∘ bouquet-degree m n k)
local-bouquet lZ zero k = local-circle-bouquet lZ k
local-bouquet {m} lZ (suc n) k = susp-preEquiv (bouquet-degree m n k)
  (λ x y → local-bouquet (local-path lZ x y) n k)

-- This record requires two map-level homotopies, not just identities
-- between the corresponding integer matrices.
record SphereMultipleInverse (m n p q : ℕ)
  (D : SphereBouquet n p → SphereBouquet n q) : Type where
  field
    exponent : ℕ
    B : SphereBouquet n q → SphereBouquet n p
    DB : D ∘ B ≡ bouquet-degree (m ^ exponent) n q
    BD : B ∘ D ≡ bouquet-degree (m ^ exponent) n p

sphere-multiple-inverse→localEquiv : {m n p q : ℕ}
  (D : SphereBouquet n p → SphereBouquet n q)
  → SphereMultipleInverse m n p q D → LocalEquiv m D
sphere-multiple-inverse→localEquiv {m} {n} {p} {q} D cert Z lZ =
  factor-isEquiv (λ f → f ∘ D) (λ f → f ∘ B)
    (subst isEquiv (sym (cong (λ d (f : SphereBouquet n p → Z) → f ∘ d) BD))
      (local-bouquet (local-power lZ exponent) n p))
    (subst isEquiv (sym (cong (λ d (f : SphereBouquet n q → Z) → f ∘ d) DB))
      (local-bouquet (local-power lZ exponent) n q))
  where
  open SphereMultipleInverse cert

-- Two-stage data for degree-10 localization: a primary Moore bouquet
-- and an identified cofibre of an S³-bouquet map with a multiple inverse.
record TwoStage10 (E : Type) : Type where
  field
    bottom-degrees : List (PrimaryDegree 10)
    a : fst (MooreBouquet 10 bottom-degrees) → E
    p q : ℕ
    D : SphereBouquet 2 p → SphereBouquet 2 q
    multiple-inverse : SphereMultipleInverse 10 2 p q D
    cofibre-comparison : cofib a ≃ cofib D

two-stage10-contr : {E : Type} → TwoStage10 E → isContr (L 10 E)
two-stage10-contr dataE = two-stage-contr a
  (moore-bouquet-local-null bottom-degrees)
  (local-null-equiv cofibre-comparison λ Z lZ →
    cofib-const-isEquiv D (sphere-multiple-inverse→localEquiv D multiple-inverse Z lZ))
  where
  open TwoStage10 dataE

merely-two-stage10-contr : {E : Type} → PT.∥ TwoStage10 E ∥₁ → isContr (L 10 E)
merely-two-stage10-contr = PT.rec isPropIsContr two-stage10-contr

-- Bridge.Profile.Contraction uses the bottom-cofibre interface for the
-- geometric I profile; it does not require an equivalence with the HIT EI.
