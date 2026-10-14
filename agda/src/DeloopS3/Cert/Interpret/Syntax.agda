{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cert.Interpret.Syntax where

-- Finite certificate syntax, well-formedness, and Boolean-check reflection.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ; zero; suc; _≡ᵇ_; _<ᵇ_)
open import Cubical.Data.Bool using (Bool; true; false; not; _and_; _or_; if_then_else_; false≢true)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Relation.Nullary using (Dec; yes; no)
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as C
open import DeloopS3.Groups.TablePermutation public using
  (and-left; and-right; natEq-sound; natEq-refl; _∈_; here; there;
   all-sound; member-sound; member-complete; map-member; map-member⁻;
   listEq-sound; listEq-refl; tableEq-sound; tableEq-refl;
   findIndex-witness; at; at-member; member-index; at-nth)

private variable X Y : Type

-- A right-associated conjunction, without an extra final "and true".
-- This also decomposes the existing Check.checkStep literally.
conjoin : List Bool → Bool
conjoin [] = true
conjoin (b ∷ []) = b
conjoin (b ∷ c ∷ bs) = b and conjoin (c ∷ bs)

abstract
  test-true : (bs : List Bool) (i : ℕ) → conjoin bs ≡ true
    → P.nth true bs i ≡ true
  test-true [] i p = refl
  test-true (b ∷ []) zero p = p
  test-true (b ∷ []) (suc i) p = refl
  test-true (b ∷ c ∷ bs) zero p = and-left p
  test-true (b ∷ c ∷ bs) (suc i) p =
    test-true (c ∷ bs) i (and-right {a = b} p)

  and-intro : {a b : Bool} → a ≡ true → b ≡ true → a and b ≡ true
  and-intro p q i = p i and q i

  bool-dec : (b : Bool) → Dec (b ≡ true)
  bool-dec true = yes refl
  bool-dec false = no false≢true

record RawChecks (ct : C.Certificate) : Type where
  field
    group-ok              : C.checkGroup ct ≡ true
    subgroup-ok           : C.checkSubgroup ct ≡ true
    cosets-ok             : C.checkCosets ct ≡ true
    action-a-ok           : C.checkAction ct (P.fwd 1) ≡ true
    action-b-ok           : C.checkAction ct (P.fwd 2) ≡ true
    action-a-inverse-ok   : C.checkAction ct (P.bwd 1) ≡ true
    action-b-inverse-ok   : C.checkAction ct (P.bwd 2) ≡ true
    graph-ok              : C.checkGraph ct ≡ true
    labels-ok             : P.all (C.checkLabel ct) (C.labels ct) ≡ true
    boundary-partition-ok : C.checkBoundaryPartition ct ≡ true
    boundaries-ok         : P.all (C.checkBoundary ct) (C.boundaries ct) ≡ true

inScope : List ℕ → P.Word → Bool
inScope gs = P.all (λ t → P.member _≡ᵇ_ (P.number t) gs)

scopedWord : ℕ → List ℕ → P.Word → Bool
scopedWord n gs w = P.wordValid n w and inScope gs w

record WellFormed (n : ℕ) (S : C.State) : Type where
  field
    alive-distinct : P.unique _≡ᵇ_ (C.alive S) ≡ true
    alive-range : P.all (λ g → (0 <ᵇ g) and (g <ᵇ suc n)) (C.alive S) ≡ true
    ids-distinct : P.unique _≡ᵇ_ (P.map C.faceId (C.faces S)) ≡ true
    orders-positive : P.all (λ f → 0 <ᵇ C.faceOrder f) (C.faces S) ≡ true
    words-in-scope : P.all (λ f → scopedWord n (C.alive S) (C.faceWord f)) (C.faces S) ≡ true
open WellFormed public

wfTests : ℕ → C.State → List Bool
wfTests n S =
  P.unique _≡ᵇ_ (C.alive S) ∷
  P.all (λ g → (0 <ᵇ g) and (g <ᵇ suc n)) (C.alive S) ∷
  P.unique _≡ᵇ_ (P.map C.faceId (C.faces S)) ∷
  P.all (λ f → 0 <ᵇ C.faceOrder f) (C.faces S) ∷
  P.all (λ f → scopedWord n (C.alive S) (C.faceWord f)) (C.faces S) ∷ []

wfB : ℕ → C.State → Bool
wfB n S = conjoin (wfTests n S)

abstract
  wf-reflect : {n : ℕ} {S : C.State} → wfB n S ≡ true → WellFormed n S
  wf-reflect {n} {S} p = record
    { alive-distinct = test-true (wfTests n S) 0 p
    ; alive-range = test-true (wfTests n S) 1 p
    ; ids-distinct = test-true (wfTests n S) 2 p
    ; orders-positive = test-true (wfTests n S) 3 p
    ; words-in-scope = test-true (wfTests n S) 4 p }

  wf-reify : {n : ℕ} {S : C.State} → WellFormed n S → wfB n S ≡ true
  wf-reify w = and-intro (alive-distinct w) (and-intro (alive-range w)
    (and-intro (ids-distinct w) (and-intro (orders-positive w) (words-in-scope w))))

record Basis2 : Type where
  constructor basis2
  field
    oldInNew : List P.Word
    newInOld : List P.Word
    faceOrder : List ℕ
open Basis2 public

data Move : Type where
  cancel : C.Step → Move
  basis₂ : Basis2 → Move
  unshear : Move
  gauge : List P.Z → Move

record Frame : Type where
  constructor frame
  field
    instruction : Move
    next : C.State
open Frame public

record Program : Type where
  constructor program
  field
    initial : C.State
    frames : List Frame
open Program public

-- Paired positional lookup: neither an absent ID nor a short value list
-- can accidentally select a later/default image. Accepted data checks both.
lookupBy : X → List ℕ → List X → ℕ → X
lookupBy d [] ws g = d
lookupBy d (h ∷ hs) [] g = d
lookupBy d (h ∷ hs) (w ∷ ws) g =
  if g ≡ᵇ h then w else lookupBy d hs ws g

image : List ℕ → List P.Word → ℕ → P.Word
image = lookupBy []

substLetter : List ℕ → List P.Word → P.Letter → P.Word
substLetter gs ws (P.fwd g) = image gs ws g
substLetter gs ws (P.bwd g) = P.inverseWord (image gs ws g)

substAll : List ℕ → List P.Word → P.Word → P.Word
substAll gs ws w = P.reduce (P.concatMap (substLetter gs ws) w)

windLetter : List ℕ → List P.Z → P.Letter → P.Z
windLetter gs zs (P.fwd g) = lookupBy (P.pos 0) gs zs g
windLetter gs zs (P.bwd g) = P.znegate (lookupBy (P.pos 0) gs zs g)

wind : List ℕ → List P.Z → P.Word → P.Z
wind gs zs w = P.zsum (P.map (windLetter gs zs) w)

twoGenerators : List ℕ
twoGenerators = 1 ∷ 2 ∷ []

rebaseFaces : List ℕ → List P.Word → ℕ → List C.Face → List C.Face
rebaseFaces gs ws i [] = []
rebaseFaces gs ws i (f ∷ fs) =
  C.face i (C.faceOrder f) (C.faceWeight f)
    (substAll gs ws (C.faceWord f)) (C.faceH f)
  ∷ rebaseFaces gs ws (suc i) fs

-- Failed face selection is total but cannot pass the exhaustive-ID check
-- together with the source/target well-formedness and three-face checks.
basisState : C.State → Basis2 → C.State
basisState S b with C.getFaces (faceOrder b) (C.faces S)
... | P.nothing = C.state twoGenerators []
... | P.just fs = C.state twoGenerators (rebaseFaces (C.alive S) (oldInNew b) 0 fs)

unshearFace : C.Face → C.Face
unshearFace f = C.face (C.faceId f) (C.faceOrder f) (C.effective f) (C.faceWord f) (P.pos 0)

unshearState : C.State → C.State
unshearState S = C.state (C.alive S) (P.map unshearFace (C.faces S))

gaugeFace : List ℕ → List P.Z → C.Face → C.Face
gaugeFace gs zs f = C.face (C.faceId f) (C.faceOrder f)
  (C.faceWeight f P.+z P.scale (C.faceOrder f) (wind gs zs (C.faceWord f)))
  (C.faceWord f) (C.faceH f)

gaugeState : C.State → List P.Z → C.State
gaugeState S zs = C.state (C.alive S) (P.map (gaugeFace (C.alive S) zs) (C.faces S))

basisTests : ℕ → C.State → Basis2 → List Bool
basisTests n S b =
  (P.length gs ≡ᵇ 2) ∷ (P.length (C.faces S) ≡ᵇ 3) ∷
  (P.length (oldInNew b) ≡ᵇ 2) ∷ (P.length (newInOld b) ≡ᵇ 2) ∷
  P.all (scopedWord 2 twoGenerators) (oldInNew b) ∷
  P.all (scopedWord n gs) (newInOld b) ∷
  P.all (λ g → P.wordEq (substAll twoGenerators (newInOld b) (image gs (oldInNew b) g)) (P.fwd g ∷ [])) gs ∷
  P.all (λ i → P.wordEq (substAll gs (oldInNew b) (image twoGenerators (newInOld b) i)) (P.fwd i ∷ [])) twoGenerators ∷
  (P.length (faceOrder b) ≡ᵇ 3) ∷ P.unique _≡ᵇ_ (faceOrder b) ∷
  P.setEq _≡ᵇ_ (faceOrder b) (P.map C.faceId (C.faces S)) ∷ []
  where gs = C.alive S

checkBasis : ℕ → C.State → Basis2 → Bool
checkBasis n S b = conjoin (basisTests n S b)

moveClause : C.Certificate → C.State → Move → C.State → Bool
moveClause ct S (cancel s) S′ = C.checkStep ct S s S′
moveClause ct S (basis₂ b) S′ = checkBasis (suc (C.index ct)) S b and C.stateEq (basisState S b) S′
moveClause ct S unshear S′ = C.stateEq (unshearState S) S′
moveClause ct S (gauge zs) S′ = (P.length zs ≡ᵇ P.length (C.alive S)) and C.stateEq (gaugeState S zs) S′

checkMove : C.Certificate → C.State → Move → C.State → Bool
checkMove ct S m S′ = wfB n S and wfB n S′ and moveClause ct S m S′
  where n = suc (C.index ct)

checkRun : C.Certificate → C.State → List Frame → Bool
checkRun ct S [] = true
checkRun ct S (f ∷ fs) = checkMove ct S (instruction f) (next f) and checkRun ct (next f) fs

record CheckedProgram (ct : C.Certificate) (P : Program) : Type where
  field
    initial-wf : wfB (suc (C.index ct)) (initial P) ≡ true
    moves-ok : checkRun ct (initial P) (frames P) ≡ true
open CheckedProgram public

endState : C.State → List Frame → C.State
endState S [] = S
endState S (f ∷ fs) = endState (next f) fs

finish : Program → C.State
finish P = endState (initial P) (frames P)

abstract
  checkMove-dec : (ct : C.Certificate) (S : C.State) (m : Move) (S′ : C.State)
    → Dec (checkMove ct S m S′ ≡ true)
  checkMove-dec ct S m S′ = bool-dec (checkMove ct S m S′)

  checkMove-source : {ct : C.Certificate} {S S′ : C.State} {m : Move}
    → checkMove ct S m S′ ≡ true → WellFormed (suc (C.index ct)) S
  checkMove-source p = wf-reflect (and-left p)

  checkMove-target : {ct : C.Certificate} {S S′ : C.State} {m : Move}
    → checkMove ct S m S′ ≡ true → WellFormed (suc (C.index ct)) S′
  checkMove-target {ct} {S} p = wf-reflect
    (and-left (and-right {a = wfB (suc (C.index ct)) S} p))

  checkMove-clause : {ct : C.Certificate} {S S′ : C.State} {m : Move}
    → checkMove ct S m S′ ≡ true → moveClause ct S m S′ ≡ true
  checkMove-clause {ct} {S} {S′} p =
    and-right {a = wfB (suc (C.index ct)) S′}
      (and-right {a = wfB (suc (C.index ct)) S} p)

  checkRun-head : {ct : C.Certificate} {S : C.State} {f : Frame} {fs : List Frame}
    → checkRun ct S (f ∷ fs) ≡ true → checkMove ct S (instruction f) (next f) ≡ true
  checkRun-head p = and-left p

  checkRun-tail : {ct : C.Certificate} {S : C.State} {f : Frame} {fs : List Frame}
    → checkRun ct S (f ∷ fs) ≡ true → checkRun ct (next f) fs ≡ true
  checkRun-tail {ct} {S} {f} p = and-right {a = checkMove ct S (instruction f) (next f)} p

-- Literal equality reflection, including the wire records needed for snapshots.
abstract
  zEq-sound : (x y : P.Z) → P.zEq x y ≡ true → x ≡ y
  zEq-sound (P.pos x) (P.pos y) p = cong P.pos (natEq-sound x y p)
  zEq-sound (P.neg x) (P.neg y) p = cong P.neg (natEq-sound x y p)
  zEq-sound (P.pos x) (P.neg y) p = Empty.rec (false≢true p)
  zEq-sound (P.neg x) (P.pos y) p = Empty.rec (false≢true p)

  zEq-refl : (x : P.Z) → P.zEq x x ≡ true
  zEq-refl (P.pos x) = natEq-refl x
  zEq-refl (P.neg x) = natEq-refl x

  letterEq-sound : (x y : P.Letter) → P.letterEq x y ≡ true → x ≡ y
  letterEq-sound (P.fwd x) (P.fwd y) p = cong P.fwd (natEq-sound x y p)
  letterEq-sound (P.bwd x) (P.bwd y) p = cong P.bwd (natEq-sound x y p)
  letterEq-sound (P.fwd x) (P.bwd y) p = Empty.rec (false≢true p)
  letterEq-sound (P.bwd x) (P.fwd y) p = Empty.rec (false≢true p)

  letterEq-refl : (x : P.Letter) → P.letterEq x x ≡ true
  letterEq-refl (P.fwd x) = natEq-refl x
  letterEq-refl (P.bwd x) = natEq-refl x

  wordEq-sound : (x y : P.Word) → P.wordEq x y ≡ true → x ≡ y
  wordEq-sound = listEq-sound P.letterEq letterEq-sound

  wordEq-refl : (x : P.Word) → P.wordEq x x ≡ true
  wordEq-refl = listEq-refl P.letterEq letterEq-refl

faceEqTests : C.Face → C.Face → List Bool
faceEqTests x y = (C.faceId x ≡ᵇ C.faceId y) ∷ (C.faceOrder x ≡ᵇ C.faceOrder y) ∷
  P.zEq (C.faceWeight x) (C.faceWeight y) ∷ P.wordEq (C.faceWord x) (C.faceWord y) ∷
  P.zEq (C.faceH x) (C.faceH y) ∷ []

abstract
  faceEq-sound : (x y : C.Face) → C.faceEq x y ≡ true → x ≡ y
  faceEq-sound x y p i = C.face
    (natEq-sound (C.faceId x) (C.faceId y) (test-true (faceEqTests x y) 0 p) i)
    (natEq-sound (C.faceOrder x) (C.faceOrder y) (test-true (faceEqTests x y) 1 p) i)
    (zEq-sound (C.faceWeight x) (C.faceWeight y) (test-true (faceEqTests x y) 2 p) i)
    (wordEq-sound (C.faceWord x) (C.faceWord y) (test-true (faceEqTests x y) 3 p) i)
    (zEq-sound (C.faceH x) (C.faceH y) (test-true (faceEqTests x y) 4 p) i)

  faceEq-refl : (x : C.Face) → C.faceEq x x ≡ true
  faceEq-refl x i = natEq-refl (C.faceId x) i and natEq-refl (C.faceOrder x) i
    and zEq-refl (C.faceWeight x) i and wordEq-refl (C.faceWord x) i and zEq-refl (C.faceH x) i

  stateEq-sound : (x y : C.State) → C.stateEq x y ≡ true → x ≡ y
  stateEq-sound x y p = cong₂ C.state (tableEq-sound (C.alive x) (C.alive y) (and-left p))
    (listEq-sound C.faceEq faceEq-sound (C.faces x) (C.faces y) (and-right {a = P.tableEq (C.alive x) (C.alive y)} p))

  stateEq-refl : (x : C.State) → C.stateEq x x ≡ true
  stateEq-refl x = and-intro (tableEq-refl (C.alive x)) (listEq-refl C.faceEq faceEq-refl (C.faces x))

stepEqTests : C.Step → C.Step → List Bool
stepEqTests x y = (C.removedBoundary x ≡ᵇ C.removedBoundary y) ∷
  (C.removedGenerator x ≡ᵇ C.removedGenerator y) ∷
  P.wordEq (C.relationWord x) (C.relationWord y) ∷
  P.zEq (C.relationH x) (C.relationH y) ∷ P.zEq (C.relationWeight x) (C.relationWeight y) ∷
  P.wordEq (C.replacement x) (C.replacement y) ∷ P.zEq (C.replacementH x) (C.replacementH y) ∷ []

stepEq : C.Step → C.Step → Bool
stepEq x y = conjoin (stepEqTests x y)

basis2Eq : Basis2 → Basis2 → Bool
basis2Eq x y = P.listEq P.wordEq (oldInNew x) (oldInNew y)
  and P.listEq P.wordEq (newInOld x) (newInOld y) and P.tableEq (faceOrder x) (faceOrder y)

moveEq : Move → Move → Bool
moveEq (cancel x) (cancel y) = stepEq x y
moveEq (basis₂ x) (basis₂ y) = basis2Eq x y
moveEq unshear unshear = true
moveEq (gauge x) (gauge y) = P.listEq P.zEq x y
moveEq _ _ = false

frameEq : Frame → Frame → Bool
frameEq x y = moveEq (instruction x) (instruction y) and C.stateEq (next x) (next y)

programEq : Program → Program → Bool
programEq x y = C.stateEq (initial x) (initial y) and P.listEq frameEq (frames x) (frames y)

abstract
  stepEq-sound : (x y : C.Step) → stepEq x y ≡ true → x ≡ y
  stepEq-sound x y p i = C.step
    (natEq-sound (C.removedBoundary x) (C.removedBoundary y) (test-true (stepEqTests x y) 0 p) i)
    (natEq-sound (C.removedGenerator x) (C.removedGenerator y) (test-true (stepEqTests x y) 1 p) i)
    (wordEq-sound (C.relationWord x) (C.relationWord y) (test-true (stepEqTests x y) 2 p) i)
    (zEq-sound (C.relationH x) (C.relationH y) (test-true (stepEqTests x y) 3 p) i)
    (zEq-sound (C.relationWeight x) (C.relationWeight y) (test-true (stepEqTests x y) 4 p) i)
    (wordEq-sound (C.replacement x) (C.replacement y) (test-true (stepEqTests x y) 5 p) i)
    (zEq-sound (C.replacementH x) (C.replacementH y) (test-true (stepEqTests x y) 6 p) i)

  stepEq-refl : (x : C.Step) → stepEq x x ≡ true
  stepEq-refl x i = natEq-refl (C.removedBoundary x) i and natEq-refl (C.removedGenerator x) i
    and wordEq-refl (C.relationWord x) i and zEq-refl (C.relationH x) i
    and zEq-refl (C.relationWeight x) i and wordEq-refl (C.replacement x) i and zEq-refl (C.replacementH x) i

  basis2Eq-sound : (x y : Basis2) → basis2Eq x y ≡ true → x ≡ y
  basis2Eq-sound x y p i = basis2
    (listEq-sound P.wordEq wordEq-sound (oldInNew x) (oldInNew y) (and-left p) i)
    (listEq-sound P.wordEq wordEq-sound (newInOld x) (newInOld y) (and-left q) i)
    (tableEq-sound (faceOrder x) (faceOrder y) (and-right {a = P.listEq P.wordEq (newInOld x) (newInOld y)} q) i)
    where
    q : P.listEq P.wordEq (newInOld x) (newInOld y) and P.tableEq (faceOrder x) (faceOrder y) ≡ true
    q = and-right {a = P.listEq P.wordEq (oldInNew x) (oldInNew y)} p

  basis2Eq-refl : (x : Basis2) → basis2Eq x x ≡ true
  basis2Eq-refl x = and-intro (listEq-refl P.wordEq wordEq-refl (oldInNew x))
    (and-intro (listEq-refl P.wordEq wordEq-refl (newInOld x)) (tableEq-refl (faceOrder x)))

  moveEq-sound : (x y : Move) → moveEq x y ≡ true → x ≡ y
  moveEq-sound (cancel x) (cancel y) p = cong cancel (stepEq-sound x y p)
  moveEq-sound (basis₂ x) (basis₂ y) p = cong basis₂ (basis2Eq-sound x y p)
  moveEq-sound unshear unshear p = refl
  moveEq-sound (gauge x) (gauge y) p = cong gauge (listEq-sound P.zEq zEq-sound x y p)
  moveEq-sound (cancel _) (basis₂ _) p = Empty.rec (false≢true p)
  moveEq-sound (cancel _) unshear p = Empty.rec (false≢true p)
  moveEq-sound (cancel _) (gauge _) p = Empty.rec (false≢true p)
  moveEq-sound (basis₂ _) (cancel _) p = Empty.rec (false≢true p)
  moveEq-sound (basis₂ _) unshear p = Empty.rec (false≢true p)
  moveEq-sound (basis₂ _) (gauge _) p = Empty.rec (false≢true p)
  moveEq-sound unshear (cancel _) p = Empty.rec (false≢true p)
  moveEq-sound unshear (basis₂ _) p = Empty.rec (false≢true p)
  moveEq-sound unshear (gauge _) p = Empty.rec (false≢true p)
  moveEq-sound (gauge _) (cancel _) p = Empty.rec (false≢true p)
  moveEq-sound (gauge _) (basis₂ _) p = Empty.rec (false≢true p)
  moveEq-sound (gauge _) unshear p = Empty.rec (false≢true p)

  moveEq-refl : (x : Move) → moveEq x x ≡ true
  moveEq-refl (cancel x) = stepEq-refl x
  moveEq-refl (basis₂ x) = basis2Eq-refl x
  moveEq-refl unshear = refl
  moveEq-refl (gauge x) = listEq-refl P.zEq zEq-refl x

  frameEq-sound : (x y : Frame) → frameEq x y ≡ true → x ≡ y
  frameEq-sound x y p = cong₂ frame (moveEq-sound (instruction x) (instruction y) (and-left p))
    (stateEq-sound (next x) (next y) (and-right {a = moveEq (instruction x) (instruction y)} p))

  frameEq-refl : (x : Frame) → frameEq x x ≡ true
  frameEq-refl x = and-intro (moveEq-refl (instruction x)) (stateEq-refl (next x))

  programEq-sound : (x y : Program) → programEq x y ≡ true → x ≡ y
  programEq-sound x y p = cong₂ program (stateEq-sound (initial x) (initial y) (and-left p))
    (listEq-sound frameEq frameEq-sound (frames x) (frames y) (and-right {a = C.stateEq (initial x) (initial y)} p))

  programEq-refl : (x : Program) → programEq x x ≡ true
  programEq-refl x = and-intro (stateEq-refl (initial x)) (listEq-refl frameEq frameEq-refl (frames x))

  eq-reify : (eq : X → X → Bool) → ((x : X) → eq x x ≡ true)
    → {x y : X} → x ≡ y → eq x y ≡ true
  eq-reify eq r {x} p = subst (λ y → eq x y ≡ true) p (r x)

  eq-dec : (eq : X → X → Bool)
    → ((x y : X) → eq x y ≡ true → x ≡ y)
    → ((x : X) → eq x x ≡ true) → (x y : X) → Dec (x ≡ y)
  eq-dec eq sound r x y with bool-dec (eq x y)
  ... | yes p = yes (sound x y p)
  ... | no p = no (λ e → p (eq-reify eq r e))

basis2Eq-reify : {x y : Basis2} → x ≡ y → basis2Eq x y ≡ true
basis2Eq-reify = eq-reify basis2Eq basis2Eq-refl
moveEq-reify : {x y : Move} → x ≡ y → moveEq x y ≡ true
moveEq-reify = eq-reify moveEq moveEq-refl
frameEq-reify : {x y : Frame} → x ≡ y → frameEq x y ≡ true
frameEq-reify = eq-reify frameEq frameEq-refl
programEq-reify : {x y : Program} → x ≡ y → programEq x y ≡ true
programEq-reify = eq-reify programEq programEq-refl

basis2-dec : (x y : Basis2) → Dec (x ≡ y)
basis2-dec = eq-dec basis2Eq basis2Eq-sound basis2Eq-refl
move-dec : (x y : Move) → Dec (x ≡ y)
move-dec = eq-dec moveEq moveEq-sound moveEq-refl
frame-dec : (x y : Frame) → Dec (x ≡ y)
frame-dec = eq-dec frameEq frameEq-sound frameEq-refl
program-dec : (x y : Program) → Dec (x ≡ y)
program-dec = eq-dec programEq programEq-sound programEq-refl

-- Generic list lemmas for advance-wf. They concern predicates on generator
-- numbers, so inversion and free reduction preserve them without group theory.
abstract
  all-intro : (p : X → Bool) (xs : List X)
    → ((x : X) → x ∈ xs → p x ≡ true) → P.all p xs ≡ true
  all-intro p [] h = refl
  all-intro p (x ∷ xs) h = and-intro (h x here) (all-intro p xs (λ y m → h y (there m)))

  all-map-intro : (f : X → Y) (p : Y → Bool) (xs : List X)
    → ((x : X) → x ∈ xs → p (f x) ≡ true) → P.all p (P.map f xs) ≡ true
  all-map-intro f p [] h = refl
  all-map-intro f p (x ∷ xs) h = and-intro (h x here)
    (all-map-intro f p xs (λ y m → h y (there m)))

  filter-member : (p : X → Bool) (xs : List X) {x : X}
    → x ∈ P.filter p xs → x ∈ xs
  filter-member p [] ()
  filter-member p (y ∷ ys) m with p y
  ... | true with m
  ...   | here = here
  ...   | there q = there (filter-member p ys q)
  filter-member p (y ∷ ys) m | false = there (filter-member p ys m)

  filter-member-intro : (p : X → Bool) (xs : List X) {x : X}
    → x ∈ xs → p x ≡ true → x ∈ P.filter p xs
  filter-member-intro p (x ∷ xs) here e with p x
  ... | true = here
  ... | false = Empty.rec (false≢true e)
  filter-member-intro p (y ∷ ys) (there m) e with p y
  ... | true = there (filter-member-intro p ys m e)
  ... | false = filter-member-intro p ys m e

  all-filter : (p q : X → Bool) (xs : List X)
    → P.all q xs ≡ true → P.all q (P.filter p xs) ≡ true
  all-filter p q xs h = all-intro q (P.filter p xs)
    (λ x m → all-sound q h (filter-member p xs m))

  not-true : {b : Bool} → (b ≡ true → ⊥) → not b ≡ true
  not-true {false} h = refl
  not-true {true} h = Empty.rec (h refl)

  not-member-filter-map : (f : X → ℕ) (p : X → Bool) (xs : List X) (k : ℕ)
    → not (P.member _≡ᵇ_ k (P.map f xs)) ≡ true
    → not (P.member _≡ᵇ_ k (P.map f (P.filter p xs))) ≡ true
  not-member-filter-map f p xs k h = not-true λ e → false≢true
    (sym (cong not (member-complete _≡ᵇ_ natEq-refl (old e))) ∙ h)
    where
    old : P.member _≡ᵇ_ k (P.map f (P.filter p xs)) ≡ true → k ∈ P.map f xs
    old e = let w = map-member⁻ f (P.filter p xs) (member-sound _≡ᵇ_ natEq-sound k (P.map f (P.filter p xs)) e)
      in subst (λ k → k ∈ P.map f xs) (w .snd .snd)
        (map-member f (filter-member p xs (w .snd .fst)))

  unique-filter-map : (f : X → ℕ) (p : X → Bool) (xs : List X)
    → P.unique _≡ᵇ_ (P.map f xs) ≡ true
    → P.unique _≡ᵇ_ (P.map f (P.filter p xs)) ≡ true
  unique-filter-map f p [] h = refl
  unique-filter-map f p (x ∷ xs) h with p x
  ... | true = and-intro (not-member-filter-map f p xs (f x) (and-left h))
    (unique-filter-map f p xs (and-right {a = not (P.member _≡ᵇ_ (f x) (P.map f xs))} h))
  ... | false = unique-filter-map f p xs
    (and-right {a = not (P.member _≡ᵇ_ (f x) (P.map f xs))} h)

  map-id : (xs : List X) → P.map (λ x → x) xs ≡ xs
  map-id [] = refl
  map-id (x ∷ xs) = cong (x ∷_) (map-id xs)

  map-map : (f : Y → ℕ) (g : X → Y) (xs : List X)
    → P.map f (P.map g xs) ≡ P.map (λ x → f (g x)) xs
  map-map f g [] = refl
  map-map f g (x ∷ xs) = cong (f (g x) ∷_) (map-map f g xs)

  unique-filter : (p : ℕ → Bool) (xs : List ℕ)
    → P.unique _≡ᵇ_ xs ≡ true → P.unique _≡ᵇ_ (P.filter p xs) ≡ true
  unique-filter p xs h = subst (λ ys → P.unique _≡ᵇ_ ys ≡ true) (map-id (P.filter p xs))
    (unique-filter-map (λ x → x) p xs
      (subst (λ ys → P.unique _≡ᵇ_ ys ≡ true) (sym (map-id xs)) h))

  all-append : (p : X → Bool) (xs ys : List X)
    → P.all p xs ≡ true → P.all p ys ≡ true → P.all p (xs P.++ ys) ≡ true
  all-append p [] ys hx hy = hy
  all-append p (x ∷ xs) ys hx hy = and-intro (and-left hx)
    (all-append p xs ys (and-right {a = p x} hx) hy)

  all-revAcc : (p : X → Bool) (xs ys : List X)
    → P.all p xs ≡ true → P.all p ys ≡ true → P.all p (P.revAcc xs ys) ≡ true
  all-revAcc p [] ys hx hy = hy
  all-revAcc p (x ∷ xs) ys hx hy = all-revAcc p xs (x ∷ ys)
    (and-right {a = p x} hx) (and-intro (and-left hx) hy)

  number-flip : (t : P.Letter) → P.number (P.flip t) ≡ P.number t
  number-flip (P.fwd _) = refl
  number-flip (P.bwd _) = refl

  inverse-all : (p : ℕ → Bool) (w : P.Word)
    → P.all (λ t → p (P.number t)) w ≡ true
    → P.all (λ t → p (P.number t)) (P.inverseWord w) ≡ true
  inverse-all p w h = all-map-intro P.flip (λ t → p (P.number t)) (P.rev w)
    (λ t m → cong p (number-flip t) ∙ all-sound (λ t → p (P.number t))
      (all-revAcc (λ t → p (P.number t)) w [] h refl) m)

  push-all : (p : P.Letter → Bool) (t : P.Letter) (w : P.Word)
    → p t ≡ true → P.all p w ≡ true → P.all p (P.push t w) ≡ true
  push-all p t [] ht hw = and-intro ht refl
  push-all p t (u ∷ us) ht hw with P.letterEq t (P.flip u)
  ... | true = and-right {a = p u} hw
  ... | false = and-intro ht hw

  reduceAcc-all : (p : P.Letter → Bool) (w stack : P.Word)
    → P.all p w ≡ true → P.all p stack ≡ true → P.all p (P.reduceAcc w stack) ≡ true
  reduceAcc-all p [] stack hw hs = all-revAcc p stack [] hs refl
  reduceAcc-all p (t ∷ ts) stack hw hs = reduceAcc-all p ts (P.push t stack)
    (and-right {a = p t} hw) (push-all p t stack (and-left hw) hs)

  reduce-all : (p : P.Letter → Bool) (w : P.Word)
    → P.all p w ≡ true → P.all p (P.reduce w) ≡ true
  reduce-all p w h = reduceAcc-all p w [] h refl

  substituteLetter-all : (p : ℕ → Bool) (k : ℕ) (r : P.Word) (t : P.Letter)
    → P.all (λ t → p (P.number t)) r ≡ true
    → ((P.number t ≡ᵇ k) ≡ false → p (P.number t) ≡ true)
    → P.all (λ t → p (P.number t)) (P.substituteLetter k r t) ≡ true
  substituteLetter-all p k r (P.fwd g) hr ht with g ≡ᵇ k
  ... | true = hr
  ... | false = and-intro (ht refl) refl
  substituteLetter-all p k r (P.bwd g) hr ht with g ≡ᵇ k
  ... | true = inverse-all p r hr
  ... | false = and-intro (ht refl) refl

  concatMap-all : (f : X → P.Word) (p : P.Letter → Bool) (xs : List X)
    → ((x : X) → x ∈ xs → P.all p (f x) ≡ true)
    → P.all p (P.concatMap f xs) ≡ true
  concatMap-all f p [] h = refl
  concatMap-all f p (x ∷ xs) h = all-append p (f x) (P.concatMap f xs) (h x here)
    (concatMap-all f p xs (λ y m → h y (there m)))

  replace-all : (p : ℕ → Bool) (w : P.Word) (k : ℕ) (r : P.Word)
    → P.all (λ t → p (P.number t)) r ≡ true
    → ((t : P.Letter) → t ∈ w → (P.number t ≡ᵇ k) ≡ false → p (P.number t) ≡ true)
    → P.all (λ t → p (P.number t)) (P.replace w k r) ≡ true
  replace-all p w k r hr hw = reduce-all (λ t → p (P.number t)) (P.concatMap (P.substituteLetter k r) w)
    (concatMap-all (P.substituteLetter k r) (λ t → p (P.number t)) w
      (λ t m → substituteLetter-all p k r t hr (hw t m)))

  occurrences-zero : (k : ℕ) (w : P.Word) → (P.occurrences k w ≡ᵇ 0) ≡ true
    → P.all (λ t → not (P.number t ≡ᵇ k)) w ≡ true
  occurrences-zero k [] h = refl
  occurrences-zero k (t ∷ ts) h with P.number t ≡ᵇ k
  ... | true = Empty.rec (false≢true h)
  ... | false = occurrences-zero k ts h

abstract
  member-filter-keep : (k : ℕ) (gs : List ℕ) (g : ℕ)
    → P.member _≡ᵇ_ g gs ≡ true → not (g ≡ᵇ k) ≡ true
    → P.member _≡ᵇ_ g (P.filter (λ j → not (j ≡ᵇ k)) gs) ≡ true
  member-filter-keep k gs g m e = member-complete _≡ᵇ_ natEq-refl
    (filter-member-intro (λ j → not (j ≡ᵇ k)) gs (member-sound _≡ᵇ_ natEq-sound g gs m) e)

  replace-scoped : (n : ℕ) (gs : List ℕ) (k : ℕ) (r w : P.Word)
    → P.wordValid n r ≡ true → inScope gs r ≡ true
    → (P.occurrences k r ≡ᵇ 0) ≡ true
    → scopedWord n gs w ≡ true
    → scopedWord n (P.filter (λ g → not (g ≡ᵇ k)) gs) (P.replace w k r) ≡ true
  replace-scoped n gs k r w vr sr zr sw = and-intro valid scoped
    where
    gs′ : List ℕ
    gs′ = P.filter (λ g → not (g ≡ᵇ k)) gs
    valid : P.wordValid n (P.replace w k r) ≡ true
    valid = replace-all (λ g → (0 <ᵇ g) and (g <ᵇ suc n)) w k r vr
      (λ t m e → all-sound (λ t → (0 <ᵇ P.number t) and (P.number t <ᵇ suc n)) (and-left sw) m)
    replacement-scoped : inScope gs′ r ≡ true
    replacement-scoped = all-intro (λ t → P.member _≡ᵇ_ (P.number t) gs′) r
      (λ t m → member-filter-keep k gs (P.number t)
        (all-sound (λ t → P.member _≡ᵇ_ (P.number t) gs) sr m)
        (all-sound (λ t → not (P.number t ≡ᵇ k)) (occurrences-zero k r zr) m))
    scoped : inScope gs′ (P.replace w k r) ≡ true
    scoped = replace-all (λ g → P.member _≡ᵇ_ g gs′) w k r replacement-scoped
      (λ t m e → member-filter-keep k gs (P.number t)
        (all-sound (λ t → P.member _≡ᵇ_ (P.number t) gs)
          (and-right {a = P.wordValid n w} sw) m) (cong not e))

  advance-computed-wf : {n : ℕ} {S : C.State} (s : C.Step)
    → WellFormed n S
    → (P.occurrences (C.removedGenerator s) (C.replacement s) ≡ᵇ 0) ≡ true
    → P.wordValid n (C.replacement s) ≡ true
    → inScope (C.alive S) (C.replacement s) ≡ true
    → WellFormed n (C.advance S s)
  advance-computed-wf {n} {S} s wf zr vr sr = record
    { alive-distinct = unique-filter keep (C.alive S) (alive-distinct wf)
    ; alive-range = all-filter keep (λ g → (0 <ᵇ g) and (g <ᵇ suc n)) (C.alive S) (alive-range wf)
    ; ids-distinct = subst (λ is → P.unique _≡ᵇ_ is ≡ true)
        (sym (map-map C.faceId (C.rewriteFace s) kept))
        (unique-filter-map C.faceId keepFace (C.faces S) (ids-distinct wf))
    ; orders-positive = all-map-intro (C.rewriteFace s) (λ f → 0 <ᵇ C.faceOrder f) kept
        (λ f m → all-sound (λ f → 0 <ᵇ C.faceOrder f) (orders-positive wf)
          (filter-member keepFace (C.faces S) m))
    ; words-in-scope = all-map-intro (C.rewriteFace s)
        (λ f → scopedWord n (P.filter keep (C.alive S)) (C.faceWord f)) kept
        (λ f m → replace-scoped n (C.alive S) (C.removedGenerator s) (C.replacement s) (C.faceWord f)
          vr sr zr (all-sound (λ f → scopedWord n (C.alive S) (C.faceWord f)) (words-in-scope wf)
            (filter-member keepFace (C.faces S) m))) }
    where
    keep : ℕ → Bool
    keep = λ g → not (g ≡ᵇ C.removedGenerator s)
    keepFace : C.Face → Bool
    keepFace = λ f → not (C.faceId f ≡ᵇ C.removedBoundary s)
    kept : List C.Face
    kept = P.filter keepFace (C.faces S)

-- Exact decomposition of Check.checkStep's successful-lookup branch.
stepTests : C.Certificate → C.State → C.Step → C.State → C.Face → List Bool
stepTests ct S s S′ f =
  (C.faceOrder f ≡ᵇ 1) ∷ P.member _≡ᵇ_ (C.removedGenerator s) (C.alive S) ∷
  (P.occurrences (C.removedGenerator s) (C.faceWord f) ≡ᵇ 1) ∷
  P.wordEq (C.relationWord s) (C.faceWord f) ∷ P.zEq (C.relationH s) (C.faceH f) ∷
  P.zEq (C.relationWeight s) (C.faceWeight f) ∷
  (P.occurrences (C.removedGenerator s) (C.replacement s) ≡ᵇ 0) ∷
  P.wordValid (suc (C.index ct)) (C.replacement s) ∷ inScope (C.alive S) (C.replacement s) ∷
  P.wordEq (P.replace (C.faceWord f) (C.removedGenerator s) (C.replacement s)) [] ∷
  P.zEq (C.faceH f P.+z (P.exponent (C.removedGenerator s) (C.faceWord f) P.*z C.replacementH s)) (C.faceWeight f) ∷
  P.tableEq (P.evaluate (C.degree ct) (C.replacement s) (C.images ct)) (P.generator (C.images ct) (C.removedGenerator s)) ∷
  C.stateEq (C.advance S s) S′ ∷ []

record StepFacts (ct : C.Certificate) (S : C.State) (s : C.Step) (S′ : C.State) : Type where
  field
    found : C.Face
    found-ok : C.getFace (C.removedBoundary s) (C.faces S) ≡ P.just found
    tests-ok : conjoin (stepTests ct S s S′ found) ≡ true
open StepFacts public

stepClause : C.Certificate → C.State → C.Step → C.State → P.Maybe C.Face → Bool
stepClause ct S s S′ P.nothing = false
stepClause ct S s S′ (P.just f) = conjoin (stepTests ct S s S′ f)

abstract
  stepClause-check : (ct : C.Certificate) (S : C.State) (s : C.Step) (S′ : C.State)
    → stepClause ct S s S′ (C.getFace (C.removedBoundary s) (C.faces S)) ≡ C.checkStep ct S s S′
  stepClause-check ct S s S′ with C.getFace (C.removedBoundary s) (C.faces S)
  ... | P.nothing = refl
  ... | P.just f = refl

  checkStep-reflect : {ct : C.Certificate} {S S′ : C.State} {s : C.Step}
    → C.checkStep ct S s S′ ≡ true → StepFacts ct S s S′
  checkStep-reflect {ct} {S} {S′} {s} p = extract (C.getFace (C.removedBoundary s) (C.faces S)) refl (stepClause-check ct S s S′ ∙ p)
    where
    extract : (mf : P.Maybe C.Face)
      → C.getFace (C.removedBoundary s) (C.faces S) ≡ mf
      → stepClause ct S s S′ mf ≡ true → StepFacts ct S s S′
    extract P.nothing e q = Empty.rec (false≢true q)
    extract (P.just f) e q = record { found = f ; found-ok = e ; tests-ok = q }

  advance-wf : {n : ℕ} {S S′ : C.State} {ct : C.Certificate} {s : C.Step}
    → WellFormed n S → C.checkStep ct S s S′ ≡ true
    → n ≡ suc (C.index ct) → WellFormed n S′
  advance-wf {n} {S} {S′} {ct} {s} wf ok bound =
    subst (WellFormed n) (stateEq-sound (C.advance S s) S′ (test-true ts 12 pf))
      (advance-computed-wf s wf (test-true ts 6 pf)
        (subst (λ k → P.wordValid k (C.replacement s) ≡ true) (sym bound) (test-true ts 7 pf))
        (test-true ts 8 pf))
    where
    facts : StepFacts ct S s S′
    facts = checkStep-reflect {ct = ct} {S = S} {S′ = S′} {s = s} ok
    ts : List Bool
    ts = stepTests ct S s S′ (found facts)
    pf : conjoin ts ≡ true
    pf = tests-ok facts

rawChecksTests : C.Certificate → List Bool
rawChecksTests ct = C.checkGroup ct ∷ C.checkSubgroup ct ∷ C.checkCosets ct ∷
  C.checkAction ct (P.fwd 1) ∷ C.checkAction ct (P.fwd 2) ∷
  C.checkAction ct (P.bwd 1) ∷ C.checkAction ct (P.bwd 2) ∷
  C.checkGraph ct ∷ P.all (C.checkLabel ct) (C.labels ct) ∷
  C.checkBoundaryPartition ct ∷ P.all (C.checkBoundary ct) (C.boundaries ct) ∷ []

rawChecksB : C.Certificate → Bool
rawChecksB ct = conjoin (rawChecksTests ct)

checkedProgramB : C.Certificate → Program → Bool
checkedProgramB ct p = wfB (suc (C.index ct)) (initial p) and checkRun ct (initial p) (frames p)

abstract
  rawChecks-reflect : {ct : C.Certificate} → rawChecksB ct ≡ true → RawChecks ct
  rawChecks-reflect {ct} p = record
    { group-ok = test-true (rawChecksTests ct) 0 p
    ; subgroup-ok = test-true (rawChecksTests ct) 1 p
    ; cosets-ok = test-true (rawChecksTests ct) 2 p
    ; action-a-ok = test-true (rawChecksTests ct) 3 p
    ; action-b-ok = test-true (rawChecksTests ct) 4 p
    ; action-a-inverse-ok = test-true (rawChecksTests ct) 5 p
    ; action-b-inverse-ok = test-true (rawChecksTests ct) 6 p
    ; graph-ok = test-true (rawChecksTests ct) 7 p
    ; labels-ok = test-true (rawChecksTests ct) 8 p
    ; boundary-partition-ok = test-true (rawChecksTests ct) 9 p
    ; boundaries-ok = test-true (rawChecksTests ct) 10 p }

  rawChecks-reify : {ct : C.Certificate} → RawChecks ct → rawChecksB ct ≡ true
  rawChecks-reify p i = RawChecks.group-ok p i and RawChecks.subgroup-ok p i
    and RawChecks.cosets-ok p i and RawChecks.action-a-ok p i and RawChecks.action-b-ok p i
    and RawChecks.action-a-inverse-ok p i and RawChecks.action-b-inverse-ok p i
    and RawChecks.graph-ok p i and RawChecks.labels-ok p i
    and RawChecks.boundary-partition-ok p i and RawChecks.boundaries-ok p i

  checkedProgram-reflect : {ct : C.Certificate} {p : Program}
    → checkedProgramB ct p ≡ true → CheckedProgram ct p
  checkedProgram-reflect {ct} {p} h = record
    { initial-wf = and-left h
    ; moves-ok = and-right {a = wfB (suc (C.index ct)) (initial p)} h }

  checkedProgram-reify : {ct : C.Certificate} {p : Program}
    → CheckedProgram ct p → checkedProgramB ct p ≡ true
  checkedProgram-reify h = and-intro (initial-wf h) (moves-ok h)

open import Cubical.Data.Bool.Properties using (isSetBool)

abstract
  isPropWellFormed : {n : ℕ} {S : C.State} → isProp (WellFormed n S)
  isPropWellFormed u v i = record
    { alive-distinct = isSetBool _ _ (alive-distinct u) (alive-distinct v) i
    ; alive-range = isSetBool _ _ (alive-range u) (alive-range v) i
    ; ids-distinct = isSetBool _ _ (ids-distinct u) (ids-distinct v) i
    ; orders-positive = isSetBool _ _ (orders-positive u) (orders-positive v) i
    ; words-in-scope = isSetBool _ _ (words-in-scope u) (words-in-scope v) i }

  isPropRawChecks : {ct : C.Certificate} → isProp (RawChecks ct)
  isPropRawChecks u v i = record
    { group-ok = isSetBool _ _ (RawChecks.group-ok u) (RawChecks.group-ok v) i
    ; subgroup-ok = isSetBool _ _ (RawChecks.subgroup-ok u) (RawChecks.subgroup-ok v) i
    ; cosets-ok = isSetBool _ _ (RawChecks.cosets-ok u) (RawChecks.cosets-ok v) i
    ; action-a-ok = isSetBool _ _ (RawChecks.action-a-ok u) (RawChecks.action-a-ok v) i
    ; action-b-ok = isSetBool _ _ (RawChecks.action-b-ok u) (RawChecks.action-b-ok v) i
    ; action-a-inverse-ok = isSetBool _ _ (RawChecks.action-a-inverse-ok u) (RawChecks.action-a-inverse-ok v) i
    ; action-b-inverse-ok = isSetBool _ _ (RawChecks.action-b-inverse-ok u) (RawChecks.action-b-inverse-ok v) i
    ; graph-ok = isSetBool _ _ (RawChecks.graph-ok u) (RawChecks.graph-ok v) i
    ; labels-ok = isSetBool _ _ (RawChecks.labels-ok u) (RawChecks.labels-ok v) i
    ; boundary-partition-ok = isSetBool _ _ (RawChecks.boundary-partition-ok u) (RawChecks.boundary-partition-ok v) i
    ; boundaries-ok = isSetBool _ _ (RawChecks.boundaries-ok u) (RawChecks.boundaries-ok v) i }

  isPropCheckedProgram : {ct : C.Certificate} {p : Program} → isProp (CheckedProgram ct p)
  isPropCheckedProgram u v i = record
    { initial-wf = isSetBool _ _ (initial-wf u) (initial-wf v) i
    ; moves-ok = isSetBool _ _ (moves-ok u) (moves-ok v) i }
