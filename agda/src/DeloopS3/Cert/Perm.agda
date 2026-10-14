{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cert.Perm where

open import Cubical.Foundations.Prelude public using (Type; _≡_; refl)
open import Cubical.Data.Nat.Base public
  using (ℕ; zero; suc; _+_; _·_; _∸_; _<ᵇ_; _≡ᵇ_)
open import Cubical.Data.Bool.Base public
  using (Bool; true; false; not; _and_; _or_; if_then_else_)
open import Cubical.Data.List.Base public using (List; []; _∷_)

private variable A B : Type

infixr 5 _++_
_++_ : List A → List A → List A
[] ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

map : (A → B) → List A → List B
map f [] = []
map f (x ∷ xs) = f x ∷ map f xs

concatMap : (A → List B) → List A → List B
concatMap f [] = []
concatMap f (x ∷ xs) = f x ++ concatMap f xs

length : List A → ℕ
length [] = 0
length (_ ∷ xs) = suc (length xs)

all any : (A → Bool) → List A → Bool
all f [] = true
all f (x ∷ xs) = f x and all f xs
any f [] = false
any f (x ∷ xs) = f x or any f xs

filter : (A → Bool) → List A → List A
filter f [] = []
filter f (x ∷ xs) = if f x then x ∷ filter f xs else filter f xs

listEq : (A → A → Bool) → List A → List A → Bool
listEq eq [] [] = true
listEq eq (x ∷ xs) (y ∷ ys) = eq x y and listEq eq xs ys
listEq eq _ _ = false

member : (A → A → Bool) → A → List A → Bool
member eq x = any (eq x)

unique : (A → A → Bool) → List A → Bool
unique eq [] = true
unique eq (x ∷ xs) = not (member eq x xs) and unique eq xs

setEq : (A → A → Bool) → List A → List A → Bool
setEq eq xs ys = all (λ x → member eq x ys) xs and all (λ y → member eq y xs) ys

range : ℕ → List ℕ
range zero = []
range (suc n) = 0 ∷ map suc (range n)

oneTo : ℕ → List ℕ
oneTo n = map suc (range n)

nth : A → List A → ℕ → A
nth d [] i = d
nth d (x ∷ xs) zero = x
nth d (x ∷ xs) (suc i) = nth d xs i

revAcc : List A → List A → List A
revAcc [] ys = ys
revAcc (x ∷ xs) ys = revAcc xs (x ∷ ys)

rev : List A → List A
rev xs = revAcc xs []

replicate : ℕ → A → List A
replicate zero x = []
replicate (suc n) x = x ∷ replicate n x

record Pair (A B : Type) : Type where
  constructor _,_
  field fst : A
        snd : B
open Pair public
infixr 4 _,_

data Maybe (A : Type) : Type where
  nothing : Maybe A
  just : A → Maybe A

-- Canonical integers: neg n means -(n+1); there is no negative zero.
data Z : Type where
  pos neg : ℕ → Z

znegate : Z → Z
znegate (pos zero) = pos 0
znegate (pos (suc n)) = neg n
znegate (neg n) = pos (suc n)

zdiff : ℕ → ℕ → Z
zdiff n zero = pos n
zdiff zero (suc m) = neg m
zdiff (suc n) (suc m) = zdiff n m

infixl 6 _+z_ _-z_
infixl 7 _*z_
_+z_ : Z → Z → Z
pos n +z pos m = pos (n + m)
pos n +z neg m = zdiff n (suc m)
neg n +z pos m = zdiff m (suc n)
neg n +z neg m = neg (suc (n + m))

_-z_ : Z → Z → Z
x -z y = x +z znegate y

scale : ℕ → Z → Z
scale zero z = pos 0
scale (suc n) z = z +z scale n z

_*z_ : Z → Z → Z
pos n *z z = scale n z
neg n *z z = znegate (scale (suc n) z)

zEq : Z → Z → Bool
zEq (pos n) (pos m) = n ≡ᵇ m
zEq (neg n) (neg m) = n ≡ᵇ m
zEq _ _ = false

zsum : List Z → Z
zsum [] = pos 0
zsum (z ∷ zs) = z +z zsum zs

-- Generator numbers are positive (1-based); wordValid rejects zero.
data Letter : Type where
  fwd bwd : ℕ → Letter
Word = List Letter

number : Letter → ℕ
number (fwd k) = k
number (bwd k) = k

flip : Letter → Letter
flip (fwd k) = bwd k
flip (bwd k) = fwd k

letterEq : Letter → Letter → Bool
letterEq (fwd i) (fwd j) = i ≡ᵇ j
letterEq (bwd i) (bwd j) = i ≡ᵇ j
letterEq _ _ = false

wordEq : Word → Word → Bool
wordEq = listEq letterEq

wordValid : ℕ → Word → Bool
wordValid n = all (λ t → (0 <ᵇ number t) and (number t <ᵇ suc n))

inverseWord : Word → Word
inverseWord w = map flip (rev w)

-- Stack reduction, in the same left-to-right convention as replay.py.
push : Letter → Word → Word
push t [] = t ∷ []
push t (u ∷ us) = if letterEq t (flip u) then us else t ∷ u ∷ us

reduceAcc : Word → Word → Word
reduceAcc [] stack = rev stack
reduceAcc (t ∷ ts) stack = reduceAcc ts (push t stack)

reduce : Word → Word
reduce w = reduceAcc w []

substituteLetter : ℕ → Word → Letter → Word
substituteLetter k r (fwd t) = if t ≡ᵇ k then r else fwd t ∷ []
substituteLetter k r (bwd t) = if t ≡ᵇ k then inverseWord r else bwd t ∷ []

replace : Word → ℕ → Word → Word
replace w k r = reduce (concatMap (substituteLetter k r) w)

occurrences : ℕ → Word → ℕ
occurrences k w = length (filter (λ t → number t ≡ᵇ k) w)

exponentLetter : ℕ → Letter → Z
exponentLetter k (fwd t) = if t ≡ᵇ k then pos 1 else pos 0
exponentLetter k (bwd t) = if t ≡ᵇ k then neg 0 else pos 0

exponent : ℕ → Word → Z
exponent k w = zsum (map (exponentLetter k) w)

-- The computational wire format is a list table [p(0),...,p(n-1)].
-- isPerm checks its length and that it contains each element of Fin n once.
-- No use of an unchecked default lookup can make an invalid table pass it.
Table = List ℕ

tableEq : Table → Table → Bool
tableEq = listEq _≡ᵇ_

isPerm : ℕ → Table → Bool
isPerm n xs = (length xs ≡ᵇ n) and unique _≡ᵇ_ xs and setEq _≡ᵇ_ xs (range n)

record Permutation (n : ℕ) : Type where
  constructor certified
  field table : Table
        valid : isPerm n table ≡ true
open Permutation public

identity : ℕ → Table
identity = range

apply : Table → ℕ → ℕ
apply xs i = nth (length xs) xs i

-- compose p q = p ∘ q, exactly replay.py's convention.
compose : Table → Table → Table
compose p q = map (apply p) q

findIndex : ℕ → Table → ℕ
findIndex y [] = 0
findIndex y (x ∷ xs) = if x ≡ᵇ y then 0 else suc (findIndex y xs)

inverse : Table → Table
inverse p = map (λ y → findIndex y p) (range (length p))

power : ℕ → Table → ℕ → Table
power n p zero = identity n
power n p (suc k) = compose (power n p k) p

generator : List Table → ℕ → Table
generator gs k = nth [] gs (k ∸ 1)

letterImage : List Table → Letter → Table
letterImage gs (fwd k) = generator gs k
letterImage gs (bwd k) = inverse (generator gs k)

evaluateAcc : Word → List Table → Table → Table
evaluateAcc [] gs v = v
evaluateAcc (t ∷ ts) gs v = evaluateAcc ts gs (compose v (letterImage gs t))

evaluate : ℕ → Word → List Table → Table
evaluate n w gs = evaluateAcc w gs (identity n)

exactOrder : ℕ → Table → ℕ → Bool
exactOrder n p d = (0 <ᵇ d) and tableEq (power n p d) (identity n)
  and all (λ k → not (tableEq (power n p k) (identity n))) (oneTo (d ∸ 1))

-- Bounded work-list closure. Fuel exhaustion is failure, NOT a partial answer.
-- Every new element is enqueued once. A successful run is the full closure.
insertFresh : List Table → Pair (List Table) (List Table) → Pair (List Table) (List Table)
insertFresh [] st = st
insertFresh (x ∷ xs) (todo , seen) =
  if member tableEq x seen
  then insertFresh xs (todo , seen)
  else insertFresh xs (x ∷ todo , x ∷ seen)

visit : ℕ → List Table → List Table → List Table → Maybe (List Table)
visit fuel gs [] seen = just seen
visit zero gs (_ ∷ _) seen = nothing
visit (suc fuel) gs (x ∷ todo) seen = next (insertFresh (map (compose x) gs) (todo , seen))
  where
  next : Pair (List Table) (List Table) → Maybe (List Table)
  next (todo′ , seen′) = visit fuel gs todo′ seen′

closure : ℕ → ℕ → List Table → Maybe (List Table)
closure n fuel gs = visit fuel gs (identity n ∷ []) (identity n ∷ [])

closureEq : ℕ → ℕ → List Table → List Table → Bool
closureEq n fuel gs expected with closure n fuel gs
... | nothing = false
... | just actual = unique tableEq expected and setEq tableEq actual expected

-- Intrinsically finite vector API, in addition to the JSON-friendly tables.
data Fin : ℕ → Type where
  fzero : {n : ℕ} → Fin (suc n)
  fsuc : {n : ℕ} → Fin n → Fin (suc n)

data Vec (A : Type) : ℕ → Type where
  vnil : Vec A 0
  _v∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)
infixr 5 _v∷_

finNat : {n : ℕ} → Fin n → ℕ
finNat fzero = 0
finNat (fsuc i) = suc (finNat i)

lookupVec : {n : ℕ} → Vec A n → Fin n → A
lookupVec (x v∷ xs) fzero = x
lookupVec (x v∷ xs) (fsuc i) = lookupVec xs i

mapVec : {n : ℕ} → (A → B) → Vec A n → Vec B n
mapVec f vnil = vnil
mapVec f (x v∷ xs) = f x v∷ mapVec f xs

tabulate : {n : ℕ} → (Fin n → A) → Vec A n
tabulate {n = zero} f = vnil
tabulate {n = suc n} f = f fzero v∷ tabulate (λ i → f (fsuc i))

FiniteMap : ℕ → Type
FiniteMap n = Vec (Fin n) n

composeFin : {n : ℕ} → FiniteMap n → FiniteMap n → FiniteMap n
composeFin p q = mapVec (lookupVec p) q

findFin : {n k : ℕ} → (Fin n → Bool) → Vec (Fin n) k → Fin n → Fin n
findFin f vnil fallback = fallback
findFin f (x v∷ xs) fallback = if f x then x else findFin f xs fallback

inverseFin : {n : ℕ} → FiniteMap n → FiniteMap n
inverseFin p = tabulate (λ y → findFin (λ x → finNat (lookupVec p x) ≡ᵇ finNat y) (tabulate (λ x → x)) y)

vecList : {n : ℕ} → Vec A n → List A
vecList vnil = []
vecList (x v∷ xs) = x ∷ vecList xs

finiteTable : {n : ℕ} → FiniteMap n → Table
finiteTable p = map finNat (vecList p)

-- Composition/inverse of FiniteMaps are permutation operations precisely
-- when isPerm n (finiteTable p) holds; no bijectivity is silently assumed.
