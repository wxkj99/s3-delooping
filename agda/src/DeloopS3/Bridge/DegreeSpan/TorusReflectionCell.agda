{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TorusReflectionCell where

-- A direct reflection of the actual single torus attachment.
-- The boundary homotopy is free, not based.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (_≃_ ; invEq)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPath→Square ; Square→compPath)
open import Cubical.Data.Nat using (zero ; suc)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Bool using (Bool ; true ; false)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.HITs.Susp using
  (Susp ; north ; south ; merid ; toSusp ; suspFun ; S¹→SuspBool ;
   SuspBool→S¹ ; Susp≃joinBool)
open import Cubical.HITs.Pushout using (inl ; inr ; push ; cofib)
import Cubical.HITs.Join as Join
open import Cubical.HITs.Wedge using
  (⋁gen ; Iso-⋁genFinSuc-⋁genFin⋁ ; SuspBouquet→Bouquet)
open import Cubical.HITs.SphereBouquet using
  (SphereBouquet ; sphereBouquetSuspIso₀)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using (module RoseProduct)
open import DeloopS3.Bridge.DegreeSpan.ProjectH2Sparse using
  (cell-attaching ; cell-attachment ; cell-attaching-beta ; suspension-chart-inverse-cell)
import DeloopS3.Bridge.DegreeSpan.ReflectedAttachment as R

B : Type
B = SphereBouquet 1 (Fin 2)

point : B
point = inl tt

fibre first : Fin 2
fibre = fzero
first = fsuc fzero

petalReflection : Fin 2 → S¹ → S¹
petalReflection (zero , _) s = s
petalReflection (suc zero , _) s = R.reflection s
petalReflection (suc (suc n) , ()) s

petalReflection-point : (k : Fin 2) → petalReflection k base ≡ base
petalReflection-point (zero , _) = refl
petalReflection-point (suc zero , _) = refl
petalReflection-point (suc (suc n) , ())

petal : Fin 2 → S¹ → B
petal k s = inr (k , s)

reflectedSpoke : (k : Fin 2) → point ≡ petal k (petalReflection k base)
reflectedSpoke (zero , _) = push fibre
reflectedSpoke (suc zero , _) = push first
reflectedSpoke (suc (suc n) , ())

L : B → B
L (inl tt) = inl tt
L (inr (k , s)) = petal k (petalReflection k s)
L (push k i) = reflectedSpoke k i

L-point : L point ≡ point
L-point = refl

L-fibre : (s : S¹) → L (petal fibre s) ≡ petal fibre s
L-fibre s = refl

L-first : (s : S¹) → L (petal first s) ≡ petal first (R.reflection s)
L-first s = refl

-- Keep the conjugating spokes explicit.
p : (k : Fin 2) → point ≡ inr (k , base)
p k = push k

u : (k : Fin 2) → Path B (inr (k , base)) (inr (k , base))
u k i = inr (k , loop i)

a b : point ≡ point
a = p first ∙ u first ∙ sym (p first)
b = p fibre ∙ u fibre ∙ sym (p fibre)

module RP = RoseProduct 1

shift : RP.Rose → B
shift = Iso.inv Iso-⋁genFinSuc-⋁genFin⋁ ∘ inl

petalLift : ⋁gen (Fin 1) (λ _ → Susp Bool , north) → B
petalLift = shift ∘ Iso.fun sphereBouquetSuspIso₀

-- Exposed version of the existing target chart, with its comparison proved.
T : RP.Wedge → B
T (inl x) = shift (fst RP.suspension-chart x)
T (inr y) = inr (fibre , SuspBool→S¹ y)
T (push tt i) = push fibre i

abstract
  unit-double : {X : Type} {x y : X} (q : x ≡ y)
    → refl ∙∙ q ∙∙ refl ≡ q
  unit-double q = doubleCompPath-elim refl q refl
    ∙ sym (rUnit (refl ∙ q)) ∙ sym (lUnit q)

  target-agrees : fst RP.target-chart ≡ T
  target-agrees = funExt λ
    { (inl x) → refl
    ; (inr y) → refl
    ; (push tt i) → λ j →
      cong (cong (Iso.inv Iso-⋁genFinSuc-⋁genFin⋁))
        (unit-double (push tt)) j i }

vertex : Bool → RP.Vertices
vertex v = inr (fzero , v)

Aloop : RP.Vertices → point ≡ point
Aloop v = cong (T ∘ inl) (toSusp (RP.Vertices , inl tt) v)

Bloop : Bool → Path B (inr (fibre , base)) (inr (fibre , base))
Bloop v = cong (T ∘ inr) (toSusp (Bool , true) v)

abstract
  circle-sigma : cong SuspBool→S¹ (toSusp (Bool , true) false) ≡ loop
  circle-sigma = cong-∙ SuspBool→S¹ (merid false) (sym (merid true))
    ∙ sym (rUnit loop)

  A-false : Aloop (vertex false) ≡ a
  A-false =
    cong-∙ (T ∘ inl) (merid (vertex false)) (sym (merid (inl tt)))
    ∙ sym (rUnit (cong (T ∘ inl) (merid (vertex false))))
    ∙ cong-∙∙ petalLift (push fzero)
        (λ i → inr (fzero , toSusp (Bool , true) false i)) (sym (push fzero))
    ∙ cong (λ q → p first ∙∙ q ∙∙ sym (p first))
        (cong (cong (petal first)) circle-sigma)
    ∙ doubleCompPath-elim' (p first) (u first) (sym (p first))

  A-point : Aloop (inl tt) ≡ refl
  A-point = cong (cong (T ∘ inl)) (rCancel (merid (inl tt)))

  A-true : Aloop (vertex true) ≡ refl
  A-true = sym (cong Aloop (push fzero)) ∙ A-point

  B-false : Bloop false ≡ u fibre
  B-false = cong (cong (petal fibre)) circle-sigma

  B-true : Bloop true ≡ refl
  B-true = cong (cong (T ∘ inr)) (rCancel (merid true))

-- The following algebra is in an arbitrary groupoid, not its abelianization.
abstract
  join-word : {X : Type} {x y : X} (e : x ≡ y)
    (v : y ≡ y) (q : x ≡ x)
    → sym (refl ∙∙ sym e ∙∙ q) ∙ (v ∙∙ sym e ∙∙ q)
      ≡ sym q ∙ (e ∙ v ∙ sym e) ∙ q
  join-word {X} {x} {y} e v q =
    cong₂ (λ (r s : Path X y x) → sym r ∙ s)
      (doubleCompPath-elim' refl (sym e) q ∙ sym (lUnit (sym e ∙ q)))
      (doubleCompPath-elim' v (sym e) q)
    ∙ cong (_∙ (v ∙ sym e ∙ q)) (symDistr (sym e) q)
    ∙ sym (assoc (sym q) e (v ∙ sym e ∙ q))
    ∙ cong (sym q ∙_)
        (cong (e ∙_) (assoc v (sym e) q) ∙ assoc e (v ∙ sym e) q)

G : Join.join RP.Vertices Bool → B
G = T ∘ RP.W

Jv : RP.Vertices → Path (Join.join RP.Vertices Bool)
  (Join.inr true) (Join.inr false)
Jv v = sym (Join.push v true) ∙ Join.push v false

abstract
  push-image : (v : RP.Vertices) (w : Bool)
    → cong G (Join.push v w) ≡ Bloop w ∙∙ sym (p fibre) ∙∙ Aloop v
  push-image v w = cong-∙∙ T
    (λ i → inr (toSusp (Bool , true) w i))
    (sym (push tt))
    (λ i → inl (toSusp (RP.Vertices , inl tt) v i))

  meridian-image : (v : RP.Vertices)
    → cong G (Jv v) ≡ sym (Aloop v) ∙ b ∙ Aloop v
  meridian-image v =
    cong-∙ G (sym (Join.push v true)) (Join.push v false)
    ∙ cong₂ (λ (r s : Path B (inr (fibre , base)) point) → sym r ∙ s)
        (push-image v true
          ∙ cong (λ q → q ∙∙ sym (p fibre) ∙∙ Aloop v) B-true)
        (push-image v false
          ∙ cong (λ q → q ∙∙ sym (p fibre) ∙∙ Aloop v) B-false)
    ∙ join-word (p fibre) (u fibre) (Aloop v)

  meridian-false : cong G (Jv (vertex false)) ≡ sym a ∙ b ∙ a
  meridian-false = meridian-image (vertex false)
    ∙ cong (λ q → sym q ∙ b ∙ q) A-false

  meridian-true : cong G (Jv (vertex true)) ≡ b
  meridian-true = meridian-image (vertex true)
    ∙ cong (λ q → sym q ∙ b ∙ q) A-true
    ∙ sym (lUnit (b ∙ refl)) ∙ sym (rUnit b)

sourceCircle : S¹ → Join.join RP.Vertices Bool
sourceCircle = fst Susp≃joinBool ∘ suspFun vertex ∘ S¹→SuspBool

δ : S¹ → B
δ = G ∘ sourceCircle

-- The convention forced by the actual source and join constructors.
c : point ≡ point
c = (sym a ∙ b ∙ a) ∙ sym b

standard : S¹ → B
standard base = point
standard (loop i) = c i

α : Fin 1 × S¹ → B
α = cell-attaching 1

abstract
  delta-loop : cong δ loop ≡ c
  delta-loop =
    cong-∙ (G ∘ fst Susp≃joinBool ∘ suspFun vertex)
      (merid false) (sym (merid true))
    ∙ cong₂ (λ (r s : point ≡ point) → r ∙ sym s) meridian-false meridian-true

  delta-standard : (s : S¹) → δ s ≡ standard s
  delta-standard base = refl
  delta-standard (loop i) j = delta-loop j i

  alpha-delta : (s : S¹) → α (fzero , s) ≡ δ s
  alpha-delta s = cell-attaching-beta 1 fzero s
    ∙ cong (fst RP.target-chart ∘ RP.W ∘ fst Susp≃joinBool)
        (suspension-chart-inverse-cell 1 fzero s)
    ∙ funExt⁻ target-agrees (RP.W (sourceCircle s))

  alpha-standard : (s : S¹) → α (fzero , s) ≡ standard s
  alpha-standard s = alpha-delta s ∙ delta-standard s

  alpha-point : α (fzero , base) ≡ point
  alpha-point = cell-attaching-beta 1 fzero base
    ∙ cong RP.attaching (sym (push fzero)) ∙ RP.attaching-point

abstract
  spoke-inverse : {X : Type} {x y : X} (e : x ≡ y) (v : y ≡ y)
    → sym (e ∙ v ∙ sym e) ≡ e ∙ sym v ∙ sym e
  spoke-inverse e v = symDistr e (v ∙ sym e)
    ∙ cong (_∙ sym e) (symDistr v (sym e))
    ∙ sym (assoc e (sym v) (sym e))

  L-a : cong L a ≡ sym a
  L-a = cong-∙ L (p first) (u first ∙ sym (p first))
    ∙ cong (p first ∙_) (cong-∙ L (u first) (sym (p first)))
    ∙ sym (spoke-inverse (p first) (u first))

  L-b : cong L b ≡ b
  L-b = cong-∙ L (p fibre) (u fibre ∙ sym (p fibre))
    ∙ cong (p fibre ∙_) (cong-∙ L (u fibre) (sym (p fibre)))

  L-c : cong L c ≡ (a ∙ b ∙ sym a) ∙ sym b
  L-c = cong-∙ L (sym a ∙ b ∙ a) (sym b)
    ∙ cong (_∙ sym (cong L b))
        (cong-∙ L (sym a) (b ∙ a)
          ∙ cong (sym (cong L a) ∙_) (cong-∙ L b a))
    ∙ cong₂ (λ (q r : point ≡ point) → (sym q ∙ r ∙ q) ∙ sym r) L-a L-b

  inverse-word : {X : Type} {x : X} (q r : x ≡ x)
    → sym ((sym q ∙ r ∙ q) ∙ sym r) ≡ r ∙ sym q ∙ sym r ∙ q
  inverse-word q r = symDistr (sym q ∙ r ∙ q) (sym r)
    ∙ cong (r ∙_) (spoke-inverse (sym q) r)

  word-compat : {X : Type} {x : X} (q r : x ≡ x)
    → ((q ∙ r ∙ sym q) ∙ sym r) ∙ q
      ≡ q ∙ sym ((sym q ∙ r ∙ q) ∙ sym r)
  word-compat q r =
    sym (assoc (q ∙ r ∙ sym q) (sym r) q)
    ∙ sym (assoc q (r ∙ sym q) (sym r ∙ q))
    ∙ cong (q ∙_) (sym (assoc r (sym q) (sym r ∙ q)))
    ∙ cong (q ∙_) (sym (inverse-word q r))

  boundary-word : cong L c ∙ a ≡ a ∙ sym c
  boundary-word = cong (_∙ a) L-c ∙ word-compat a b

  standard-H : (s : S¹) → L (standard s) ≡ standard (R.reflection s)
  standard-H base = a
  standard-H (loop i) j = compPath→Square
    {p = cong L c} {q = sym c} {r = a} {s = a} boundary-word i j

-- Transport the free homotopy along the proved, actual chart comparison.
abstract
  H : (k : Fin 1) (s : S¹) → L (α (k , s)) ≡ α (fzero , R.reflection s)
  H (zero , tt) s = cong L (alpha-standard s)
    ∙ standard-H s ∙ sym (alpha-standard (R.reflection s))
  H (suc n , ()) s
  
  chart-point : α (fzero , base) ≡ point
  chart-point = alpha-standard base

  H-base : H fzero base ≡ cong L chart-point ∙ a ∙ sym chart-point
  H-base = refl

  alpha-loop-square :
    cong (λ s → α (fzero , s)) loop ∙ chart-point ≡ chart-point ∙ c
  alpha-loop-square = Square→compPath
    {p = cong (λ s → α (fzero , s)) loop} {q = c}
    {r = chart-point} {s = chart-point}
    (λ i j → alpha-standard (loop i) j)

  alpha-loop-normalization :
    sym chart-point ∙ cong (λ s → α (fzero , s)) loop ∙ chart-point ≡ c
  alpha-loop-normalization = cong (sym chart-point ∙_) alpha-loop-square
    ∙ assoc (sym chart-point) chart-point c
    ∙ cong (_∙ c) (lCancel chart-point) ∙ sym (lUnit c)


-- The exact CW e is used together with its secEq-dependent comm.
module Reflected = R.ReflectedAttachment α α L H
module Direct = Reflected.Direct
module Stage = Direct.ActualStage (cell-attachment 1) (cell-attachment 1)

open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)
open import Cubical.Data.Int using (ℤ ; negsuc)
open import Cubical.CW.Base using (cofibCW)
open import Cubical.CW.Map using (cellMap ; realiseCellMap ; module prefunctoriality)
open import Cubical.CW.Instances.SphereBouquetMap using (hasCWskelSphereBouquet/)
open import Cubical.HITs.SphereBouquet using ()
  renaming (BouquetIso-gen to BouquetIso-gen2)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal)
open import Cubical.HITs.Sn.Degree using (degree)
open import DeloopS3.Bridge.CellularPushout.Cellular using (restrictCell)

reflectedTop : cofib RP.attaching → cofib RP.attaching
reflectedTop = Stage.stageTop

reflectedCellular : cellMap RP.skeleton RP.skeleton
SequenceMap.map reflectedCellular zero ()
SequenceMap.map reflectedCellular (suc zero) _ = tt
SequenceMap.map reflectedCellular (suc (suc zero)) = L
SequenceMap.map reflectedCellular (suc (suc (suc n))) = reflectedTop
SequenceMap.comm reflectedCellular zero ()
SequenceMap.comm reflectedCellular (suc zero) tt = sym L-point
SequenceMap.comm reflectedCellular (suc (suc zero)) x = Stage.comm x
SequenceMap.comm reflectedCellular (suc (suc (suc n))) x = refl


actualQuotient : cofibCW 2 RP.skeleton → cofibCW 2 RP.skeleton
actualQuotient = prefunctoriality.fn+1/fn 3
  (restrictCell reflectedCellular 3) (2 , <ᵗsuc {m = 2})

-- This is the library cellular quotient, not a separately chosen model.
actualBouquetQuotient : SphereBouquet 2 (Fin 1) → SphereBouquet 2 (Fin 1)
actualBouquetQuotient = prefunctoriality.bouquetFunct 3
  (restrictCell reflectedCellular 3) (2 , <ᵗsuc {m = 2})

abstract
  actualQuotient-Q : actualQuotient ≡ Stage.Q
  actualQuotient-Q = funExt λ
    { (inl tt) → refl ; (inr z) → refl ; (push x i) → refl }


  actualBouquetQuotient-stage : actualBouquetQuotient ≡ Stage.quotient
  actualBouquetQuotient-stage =
    cong (λ (q : cofibCW 2 RP.skeleton → cofibCW 2 RP.skeleton) →
      Stage.CTBy ∘ q ∘ Iso.inv (BouquetIso-gen2 2 1 α (cell-attachment 1)))
      actualQuotient-Q


  reflectedCellular-quotient : actualBouquetQuotient ≡ R.pointedSusp R.reflection∙
  reflectedCellular-quotient = actualBouquetQuotient-stage
    ∙ Direct.bouquet-square (cell-attachment 1) (cell-attachment 1)


  -- Keep the degree calculation generic: do not normalize the concrete CW
  -- equivalence inside the degree algorithm merely to compare endpoints.
  quotient-sign : (q : SphereBouquet 2 (Fin 1) → SphereBouquet 2 (Fin 1))
    → q ≡ R.pointedSusp R.reflection∙
    → degree 2 (λ s → pickPetal fzero (q (inr (fzero , s)))) ≡ negsuc 0
  quotient-sign q eq =
    cong (λ (g : SphereBouquet 2 (Fin 1) → SphereBouquet 2 (Fin 1)) →
      degree 2 (λ s → pickPetal fzero (g (inr (fzero , s))))) eq
    ∙ R.pointedSusp-degree R.reflection∙ ∙ R.reflection-degree

  reflectedCellular-degree :
    degree 2 (λ s → pickPetal fzero (actualBouquetQuotient (inr (fzero , s))))
      ≡ negsuc 0
  reflectedCellular-degree = quotient-sign actualBouquetQuotient reflectedCellular-quotient

  reflectedCellular-realise-top : (x : cofib RP.attaching)
    → realiseCellMap reflectedCellular
        (fst (snd (hasCWskelSphereBouquet/ RP.attaching)) x)
      ≡ fst (snd (hasCWskelSphereBouquet/ RP.attaching)) (reflectedTop x)
  reflectedCellular-realise-top x = refl

-- TorusReflectionH2 constructs marked realization agreement and transfers
-- this cellular coefficient to the action of reflection on torus H₂.

