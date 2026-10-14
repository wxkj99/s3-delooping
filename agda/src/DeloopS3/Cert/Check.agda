{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cert.Check where

open import DeloopS3.Cert.Perm public

-- All functions below are total Boolean decision procedures. Supplemental
-- tables/snapshots emitted by gen/generate.py are checked, never trusted.
-- Boundary string IDs are injectively interned as natural numbers.
data Kind : Type where
  A B C : Kind

kindEq : Kind → Kind → Bool
kindEq A A = true
kindEq B B = true
kindEq C C = true
kindEq _ _ = false

record Edge : Type where
  constructor edge
  field vertex letter : ℕ
open Edge public

edgeEq : Edge → Edge → Bool
edgeEq x y = (vertex x ≡ᵇ vertex y) and (letter x ≡ᵇ letter y)

record Label : Type where
  constructor label
  field key : Edge
        word : Word
open Label public

record Actions : Type where
  constructor actions
  field a⁺ b⁺ a⁻ b⁻ : Table
open Actions public

actTable : Actions → Letter → Table
actTable ac (fwd 1) = a⁺ ac
actTable ac (fwd 2) = b⁺ ac
actTable ac (bwd 1) = a⁻ ac
actTable ac (bwd 2) = b⁻ ac
actTable ac _ = []

act : Actions → ℕ → Letter → ℕ
act ac i t = apply (actTable ac t) i

record Boundary : Type where
  constructor boundary
  field bid : ℕ
        kind : Kind
        orbit : List ℕ
        orbitLength order : ℕ
        boundaryWord : Word
        hPower weight : Z
        mark : Table
open Boundary public

record Certificate : Type where
  field degree groupOrder subgroupOrder index : ℕ
        regular : Bool
        a b c : Table
        orders : List ℕ
        reps : List Word
        representatives : List Table
        action : Actions
        tree : List Edge
        labels : List Label
        images : List Table
        boundaries : List Boundary
        group subgroup : List Table
open Certificate public

baseGenerators : Certificate → List Table
baseGenerators ct = a ct ∷ b ct ∷ []

-- replay.py 46-48,81. Exact positive order equals cyclic closure cardinality.
checkGroup : Certificate → Bool
checkGroup ct = all (isPerm (degree ct)) (a ct ∷ b ct ∷ c ct ∷ [])
  and tableEq (compose (compose (a ct) (b ct)) (c ct)) (identity (degree ct))
  and (length (group ct) ≡ᵇ groupOrder ct)
  and closureEq (degree ct) (suc (groupOrder ct)) (baseGenerators ct) (group ct)
  and listEq _≡ᵇ_ (orders ct) (2 ∷ 3 ∷ (if degree ct ≡ᵇ 4 then 4 else 5) ∷ [])
  and exactOrder (degree ct) (a ct) (nth 0 (orders ct) 0)
  and exactOrder (degree ct) (b ct) (nth 0 (orders ct) 1)
  and exactOrder (degree ct) (c ct) (nth 0 (orders ct) 2)

axis : Certificate → Table
axis ct = if degree ct ≡ᵇ 4 then c ct else b ct

cyclic : Certificate → List Table
cyclic ct = map (power (degree ct) (axis ct))
  (range (if degree ct ≡ᵇ 4 then nth 0 (orders ct) 2 else nth 0 (orders ct) 1))

conjugate : Table → Table → Table
conjugate g x = compose (compose g x) (inverse g)

normalizes : Certificate → Table → Bool
normalizes ct g = setEq tableEq (map (conjugate g) (cyclic ct)) (cyclic ct)

-- replay.py 49-51. Normalizer is recomputed over the verified full group.
checkSubgroup : Certificate → Bool
checkSubgroup ct = unique tableEq (subgroup ct)
  and setEq tableEq (subgroup ct)
    (if regular ct then identity (degree ct) ∷ [] else filter (normalizes ct) (group ct))
  and (length (subgroup ct) ≡ᵇ subgroupOrder ct)
  and (index ct · subgroupOrder ct ≡ᵇ groupOrder ct)

rep : Certificate → ℕ → Table
rep ct i = nth [] (representatives ct) i

coset : Certificate → Table → List Table
coset ct r = map (λ h → compose h r) (subgroup ct)

cosets : Certificate → List (List Table)
cosets ct = map (coset ct) (representatives ct)

-- replay.py 52-55. Explicit representatives avoid repeated word evaluation.
checkCosets : Certificate → Bool
checkCosets ct = (0 <ᵇ index ct)
  and (length (reps ct) ≡ᵇ index ct)
  and all (wordValid 2) (reps ct)
  and listEq tableEq (map (λ w → evaluate (degree ct) w (baseGenerators ct)) (reps ct)) (representatives ct)
  and tableEq (rep ct 0) (identity (degree ct))
  and unique (setEq tableEq) (cosets ct)
  and (length (cosets ct) ≡ᵇ index ct)
  and setEq tableEq (concatMap (λ x → x) (cosets ct)) (group ct)

-- replay.py 56-59, separately for the four signed generators.
checkAction : Certificate → Letter → Bool
checkAction ct t = isPerm (index ct) (actTable (action ct) t)
  and all (λ i → setEq tableEq
    (coset ct (compose (rep ct i) (letterImage (baseGenerators ct) t)))
    (coset ct (rep ct (act (action ct) i t)))) (range (index ct))

allKeys : ℕ → List Edge
allKeys n = concatMap (λ i → edge i 1 ∷ edge i 2 ∷ []) (range n)

-- Missing labels return [] only as a total lookup default. checkGraph
-- separately proves there is exactly one label for each of the 2N keys.
labelAt : List Label → Edge → Word
labelAt [] e = []
labelAt (l ∷ ls) e = if edgeEq (key l) e then word l else labelAt ls e

-- Union by component relabeling: rejects a cycle at each tree edge and
-- requires one component at the end. Equivalent to replay's union-find.
joinTree : Actions → List Edge → List ℕ → Bool
joinTree ac [] components = all (λ x → x ≡ᵇ nth 0 components 0) components
joinTree ac (e ∷ es) components =
  not (x ≡ᵇ y) and joinTree ac es (map (λ z → if z ≡ᵇ x then y else z) components)
  where
  x = nth (length components) components (vertex e)
  y = nth (length components) components (act ac (vertex e) (fwd (letter e)))

labelGenerator : Label → ℕ
labelGenerator l = number (nth (fwd 0) (word l) 0)

checkGraph : Certificate → Bool
checkGraph ct = unique edgeEq (map key (labels ct))
  and setEq edgeEq (map key (labels ct)) (allKeys (index ct))
  and unique edgeEq (tree ct)
  and (length (tree ct) ≡ᵇ (index ct ∸ 1))
  and all (λ e → member edgeEq e (allKeys (index ct))) (tree ct)
  and joinTree (action ct) (tree ct) (range (index ct))
  and setEq edgeEq (map key (filter (λ l → wordEq (word l) []) (labels ct))) (tree ct)
  and (length (images ct) ≡ᵇ suc (index ct))
  and all (isPerm (degree ct)) (images ct)
  and all (λ l → wordValid (suc (index ct)) (word l)) (labels ct)
  -- The certificates actually use singleton positive labels off the tree.
  -- This strengthens replay.py's test of the first signed entry.
  and all (λ l → wordEq (word l) [] or wordEq (word l) (fwd (labelGenerator l) ∷ [])) (labels ct)
  and unique _≡ᵇ_ nonempty
  and setEq _≡ᵇ_ nonempty (oneTo (suc (index ct)))
  where
  nonempty = map labelGenerator (filter (λ l → not (wordEq (word l) [])) (labels ct))

-- replay.py 72-74. Schreier words have their specified group values.
checkLabel : Certificate → Label → Bool
checkLabel ct l = tableEq
  (compose (compose (rep ct (vertex (key l))) (generator (baseGenerators ct) (letter (key l))))
    (inverse (rep ct (act (action ct) (vertex (key l)) (fwd (letter (key l)))))))
  (evaluate (degree ct) (word l) (images ct))

liftLetter : Certificate → ℕ → Letter → Word
liftLetter ct i (fwd t) = labelAt (labels ct) (edge i t)
liftLetter ct i (bwd t) = inverseWord (labelAt (labels ct) (edge (act (action ct) i (bwd t)) t))

liftAcc : Certificate → ℕ → Word → Word → Pair ℕ Word
liftAcc ct i [] out = i , reduce out
liftAcc ct i (t ∷ ts) out = liftAcc ct (act (action ct) i t) ts (out ++ liftLetter ct i t)

liftWord : Certificate → ℕ → Word → Pair ℕ Word
liftWord ct i w = liftAcc ct i w []

kindWord : Kind → Word
kindWord A = fwd 1 ∷ []
kindWord B = fwd 2 ∷ []
kindWord C = bwd 2 ∷ bwd 1 ∷ []

kindIndex : Kind → ℕ
kindIndex A = 0
kindIndex B = 1
kindIndex C = 2

kindGenerator : Certificate → Kind → Table
kindGenerator ct A = a ct
kindGenerator ct B = b ct
kindGenerator ct C = c ct

kindWeight : Certificate → Kind → Z
kindWeight ct A = pos 1
kindWeight ct B = pos 1
kindWeight ct C = pos 1 -z pos (nth 0 (orders ct) 2)

rotate : List ℕ → List ℕ
rotate [] = []
rotate (x ∷ xs) = xs ++ x ∷ []

-- replay.py 80-91, including orbit disjointness and exhaustiveness.
checkBoundaryPartition : Certificate → Bool
checkBoundaryPartition ct = unique _≡ᵇ_ (map bid (boundaries ct))
  and all check (A ∷ B ∷ C ∷ [])
  where
  check : Kind → Bool
  check k = unique _≡ᵇ_ vertices and setEq _≡ᵇ_ vertices (range (index ct))
    where vertices = concatMap orbit (filter (λ b → kindEq (kind b) k) (boundaries ct))

checkBoundary : Certificate → Boundary → Bool
checkBoundary ct bd = (0 <ᵇ length (orbit bd))
  and all (λ i → i <ᵇ index ct) (orbit bd)
  and tableEq (map (λ i → fst (liftWord ct i (kindWord (kind bd)))) (orbit bd)) (rotate (orbit bd))
  and (length (orbit bd) ≡ᵇ orbitLength bd)
  and (orbitLength bd · order bd ≡ᵇ nth 0 (orders ct) (kindIndex (kind bd)))
  and zEq (weight bd) (kindWeight ct (kind bd))
  and zEq (hPower bd) (pos 0)
  and (fst lifted ≡ᵇ start)
  and wordEq (snd lifted) (boundaryWord bd)
  and wordValid (suc (index ct)) (boundaryWord bd)
  and tableEq actualMark (mark bd)
  and tableEq (mark bd) (evaluate (degree ct) (boundaryWord bd) (images ct))
  where
  start = nth (index ct) (orbit bd) 0
  lifted = liftWord ct start (concatMap (λ w → w) (replicate (orbitLength bd) (kindWord (kind bd))))
  actualMark = conjugate (rep ct start) (power (degree ct) (kindGenerator ct (kind bd)) (orbitLength bd))

record Face : Type where
  constructor face
  field faceId faceOrder : ℕ
        faceWeight : Z
        faceWord : Word
        faceH : Z
open Face public

faceOf : Boundary → Face
faceOf bd = face (bid bd) (order bd) (weight bd) (boundaryWord bd) (hPower bd)

faceEq : Face → Face → Bool
faceEq x y = (faceId x ≡ᵇ faceId y) and (faceOrder x ≡ᵇ faceOrder y)
  and zEq (faceWeight x) (faceWeight y) and wordEq (faceWord x) (faceWord y) and zEq (faceH x) (faceH y)

record State : Type where
  constructor state
  field alive : List ℕ
        faces : List Face
open State public

stateEq : State → State → Bool
stateEq x y = tableEq (alive x) (alive y) and listEq faceEq (faces x) (faces y)

initialState : Certificate → State
initialState ct = state (oneTo (suc (index ct))) (map faceOf (boundaries ct))

record Step : Type where
  constructor step
  field removedBoundary removedGenerator : ℕ
        relationWord : Word
        relationH relationWeight : Z
        replacement : Word
        replacementH : Z
open Step public

getFace : ℕ → List Face → Maybe Face
getFace k [] = nothing
getFace k (f ∷ fs) = if faceId f ≡ᵇ k then just f else getFace k fs

rewriteFace : Step → Face → Face
rewriteFace s f = face (faceId f) (faceOrder f) (faceWeight f)
  (replace (faceWord f) (removedGenerator s) (replacement s))
  (faceH f +z (exponent (removedGenerator s) (faceWord f) *z replacementH s))

advance : State → Step → State
advance st s = state
  (filter (λ k → not (k ≡ᵇ removedGenerator s)) (alive st))
  (map (rewriteFace s) (filter (λ f → not (faceId f ≡ᵇ removedBoundary s)) (faces st)))

-- replay.py 92-106. Each snapshot is checked against the computed next
-- state, including EVERY remaining word, h-power, order and weight.
checkStep : Certificate → State → Step → State → Bool
checkStep ct st s next with getFace (removedBoundary s) (faces st)
... | nothing = false
... | just f = (faceOrder f ≡ᵇ 1)
  and member _≡ᵇ_ (removedGenerator s) (alive st)
  and (occurrences (removedGenerator s) (faceWord f) ≡ᵇ 1)
  and wordEq (relationWord s) (faceWord f)
  and zEq (relationH s) (faceH f)
  and zEq (relationWeight s) (faceWeight f)
  and (occurrences (removedGenerator s) (replacement s) ≡ᵇ 0)
  and wordValid (suc (index ct)) (replacement s)
  and all (λ t → member _≡ᵇ_ (number t) (alive st)) (replacement s)
  and wordEq (replace (faceWord f) (removedGenerator s) (replacement s)) []
  and zEq (faceH f +z (exponent (removedGenerator s) (faceWord f) *z replacementH s)) (faceWeight f)
  and tableEq (evaluate (degree ct) (replacement s) (images ct)) (generator (images ct) (removedGenerator s))
  and stateEq (advance st s) next

effective : Face → Z
effective f = faceWeight f -z scale (faceOrder f) (faceH f)

record Remaining : Type where
  constructor remaining
  field residual : Boundary
        effectiveWeight : Z
open Remaining public

checkRemaining : State → List ℕ → List Remaining → Bool
checkRemaining st survivors rs = tableEq (alive st) survivors
  and listEq faceEq (faces st) (map (λ r → faceOf (residual r)) rs)
  and all (λ r → zEq (effectiveWeight r) (effective (faceOf (residual r)))) rs

-- replay.py 112-114, plus agreement with the normalized JSON fields.
checkRegular : State → ℕ → Z → Bool
checkRegular (state [] (f ∷ [])) retained euler = wordEq (faceWord f) []
  and (faceOrder f ≡ᵇ 1) and zEq (effective f) (pos 2)
  and (faceId f ≡ᵇ retained) and zEq euler (pos 2)
checkRegular _ _ _ = false

record Normalization : Type where
  constructor normalization
  field ordered : List ℕ
        uvw : List Word
        before gauge after : List Z
        marks : List Table
        e : ℕ
open Normalization public

getFaces : List ℕ → List Face → Maybe (List Face)
getFaces [] fs = just []
getFaces (i ∷ is) fs with getFace i fs | getFaces is fs
... | just f | just rest = just (f ∷ rest)
... | _ | _ = nothing

weightsWithGauge : List Face → List Z → List Z
weightsWithGauge (f ∷ fs) (t ∷ ts) = (effective f +z scale (faceOrder f) t) ∷ weightsWithGauge fs ts
weightsWithGauge _ _ = []

product : ℕ → List Table → Table
product n [] = identity n
product n (p ∷ ps) = compose p (product n ps)

-- replay.py 116-123; also explicitly checks the requested mark product
-- and exact orders (2,2,e), which replay.py only implies indirectly.
checkNormalization : Certificate → State → Normalization → Bool
checkNormalization ct st out with getFaces (ordered out) (faces st)
... | nothing = false
... | just fs = (length fs ≡ᵇ 3)
  and unique _≡ᵇ_ (ordered out)
  and setEq _≡ᵇ_ (ordered out) (map faceId (faces st))
  and listEq wordEq (uvw out) (map faceWord fs)
  and wordEq (reduce (concatMap (λ w → w) (uvw out))) []
  and listEq zEq (before out) (map effective fs)
  and (length (gauge out) ≡ᵇ 3)
  and zEq (zsum (gauge out)) (pos 0)
  and listEq zEq (weightsWithGauge fs (gauge out)) (after out)
  and listEq zEq (after out) (pos 1 ∷ pos 1 ∷ (pos 1 -z pos (e out)) ∷ [])
  and listEq _≡ᵇ_ (map faceOrder fs) (2 ∷ 2 ∷ e out ∷ [])
  and listEq tableEq (map (λ w → evaluate (degree ct) w (images ct)) (uvw out)) (marks out)
  and closureEq (degree ct) (suc (subgroupOrder ct)) (marks out) (subgroup ct)
  and tableEq (product (degree ct) (marks out)) (identity (degree ct))
  and exactOrder (degree ct) (nth [] (marks out) 0) 2
  and exactOrder (degree ct) (nth [] (marks out) 1) 2
  and exactOrder (degree ct) (nth [] (marks out) 2) (e out)
