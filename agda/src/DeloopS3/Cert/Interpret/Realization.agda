{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cert.Interpret.Realization where

-- Realization of signed words and certificate states in untruncated pushout spans.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
import Cubical.Data.Nat as N
open import Cubical.Data.Bool using (Bool; true; false; if_then_else_; not; false≢true)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc; toℕ)
import Cubical.Data.Empty as Empty
open import Cubical.Relation.Nullary using (yes; no)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emloop-comp; emloop-sym; emloop-1g; emsquash)
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import Cubical.HITs.Pushout.Base using (Pushout; inl; inr; push)
import Cubical.HITs.Pushout.Properties as Pushout
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
open import DeloopS3.Cert.Interpret.Syntax
open import DeloopS3.Move.CancelMinimal public using (C; 0C; _+C_; mulC; T²)
import DeloopS3.Move.CancelLoopCell as Cell
import DeloopS3.Move.CancelGeneral as General
import DeloopS3.Cover.Orientation.CircleModel as Circle

private variable
  ℓ ℓ′ ℓO ℓL ℓR ℓO′ ℓL′ ℓR′ : Level

-- Wire neg n is -(n+1), never -n.
int : P.Z → Z.ℤ
int (P.pos n) = Z.pos n
int (P.neg n) = Z.negsuc n

sumInt : List P.Z → Z.ℤ
sumInt [] = Z.pos 0
sumInt (z ∷ zs) = int z Z.+ sumInt zs

abstract
  int-negate : (z : P.Z) → int (P.znegate z) ≡ Z.- int z
  int-negate (P.pos zero) = refl
  int-negate (P.pos (suc n)) = refl
  int-negate (P.neg n) = refl

  int-diff : (n m : ℕ) → int (P.zdiff n m) ≡ n Z.ℕ- m
  int-diff n zero = refl
  int-diff zero (suc m) = refl
  int-diff (suc n) (suc m) = int-diff n m

  int-add : (x y : P.Z) → int (x P.+z y) ≡ int x Z.+ int y
  int-add (P.pos n) (P.pos m) = Z.pos+ n m
  int-add (P.pos n) (P.neg m) = int-diff n (suc m) ∙ Z.pos- n (suc m)
  int-add (P.neg n) (P.pos m) = int-diff m (suc n) ∙ Z.pos- m (suc n)
    ∙ Z.+Comm (Z.pos m) (Z.negsuc n)
  int-add (P.neg n) (P.neg m) =
    cong Z.negsuc (sym (N.+-suc n m)) ∙ sym (Z.negsuc+negsuc-def n {k = m})

  int-subtract : (x y : P.Z) → int (x P.-z y) ≡ int x Z.- int y
  int-subtract x y = int-add x (P.znegate y) ∙ cong (int x Z.+_) (int-negate y)

  int-scale : (n : ℕ) (z : P.Z) → int (P.scale n z) ≡ Z.pos n Z.· int z
  int-scale zero z = refl
  int-scale (suc n) z = int-add z (P.scale n z) ∙ cong (int z Z.+_) (int-scale n z)

  int-multiply : (x y : P.Z) → int (x P.*z y) ≡ int x Z.· int y
  int-multiply (P.pos n) y = int-scale n y
  int-multiply (P.neg n) y = int-negate (P.scale (suc n) y)
    ∙ cong Z.-_ (int-scale (suc n) y) ∙ Z.-DistL· (Z.pos (suc n)) (int y)

  int-zsum : (zs : List P.Z) → int (P.zsum zs) ≡ sumInt zs
  int-zsum [] = refl
  int-zsum (z ∷ zs) = int-add z (P.zsum zs) ∙ cong (int z Z.+_) (int-zsum zs)

-- All word laws below are in an arbitrary type, with right-associated
-- concatenation and a final refl. An environment is a loop for every ID.
evalLetter : {X : Type ℓ} {a : X} (gs : ℕ → a ≡ a) → P.Letter → a ≡ a
evalLetter gs (P.fwd g) = gs g
evalLetter gs (P.bwd g) = sym (gs g)

evalWord : {X : Type ℓ} {a : X} (gs : ℕ → a ≡ a) → P.Word → a ≡ a
evalWord gs [] = refl
evalWord gs (t ∷ ts) = evalLetter gs t ∙ evalWord gs ts

stackEval : {X : Type ℓ} {a : X} (gs : ℕ → a ≡ a) → P.Word → a ≡ a
stackEval gs [] = refl
stackEval gs (t ∷ ts) = stackEval gs ts ∙ evalLetter gs t

module WordLaws {X : Type ℓ} {a : X} (gs : ℕ → a ≡ a) where
  abstract
    eval-flip : (t : P.Letter) → evalLetter gs (P.flip t) ≡ sym (evalLetter gs t)
    eval-flip (P.fwd _) = refl
    eval-flip (P.bwd _) = refl

    eval-append : (v w : P.Word) → evalWord gs (v P.++ w) ≡ evalWord gs v ∙ evalWord gs w
    eval-append [] w = lUnit (evalWord gs w)
    eval-append (t ∷ ts) w = cong (evalLetter gs t ∙_) (eval-append ts w)
      ∙ assoc (evalLetter gs t) (evalWord gs ts) (evalWord gs w)

    eval-revAcc : (w s : P.Word) → evalWord gs (P.revAcc w s) ≡ stackEval gs w ∙ evalWord gs s
    eval-revAcc [] s = lUnit (evalWord gs s)
    eval-revAcc (t ∷ ts) s = eval-revAcc ts (t ∷ s)
      ∙ assoc (stackEval gs ts) (evalLetter gs t) (evalWord gs s)

    eval-inverseAcc : (w s : P.Word)
      → evalWord gs (P.map P.flip (P.revAcc w s))
        ≡ sym (evalWord gs w) ∙ evalWord gs (P.map P.flip s)
    eval-inverseAcc [] s = lUnit (evalWord gs (P.map P.flip s))
    eval-inverseAcc (t ∷ ts) s = eval-inverseAcc ts (t ∷ s)
      ∙ cong (λ p → sym (evalWord gs ts) ∙ (p ∙ evalWord gs (P.map P.flip s))) (eval-flip t)
      ∙ assoc (sym (evalWord gs ts)) (sym (evalLetter gs t)) (evalWord gs (P.map P.flip s))
      ∙ cong (_∙ evalWord gs (P.map P.flip s)) (sym (symDistr (evalLetter gs t) (evalWord gs ts)))

    eval-inverse : (w : P.Word) → evalWord gs (P.inverseWord w) ≡ sym (evalWord gs w)
    eval-inverse w = eval-inverseAcc w [] ∙ sym (rUnit (sym (evalWord gs w)))

    cancel-right : (p q : a ≡ a) → (p ∙ q) ∙ sym q ≡ p
    cancel-right p q = sym (assoc p q (sym q))
      ∙ cong (p ∙_) (rCancel q) ∙ sym (rUnit p)

    eval-push : (t : P.Letter) (s : P.Word)
      → stackEval gs (P.push t s) ≡ stackEval gs s ∙ evalLetter gs t
    eval-push t [] = refl
    eval-push t (u ∷ us) with bool-dec (P.letterEq t (P.flip u))
    ... | Cubical.Relation.Nullary.yes p =
      cong (stackEval gs) (cong (λ b → if b then us else t ∷ u ∷ us) p)
      ∙ sym (cancel-right (stackEval gs us) (evalLetter gs u))
      ∙ cong ((stackEval gs us ∙ evalLetter gs u) ∙_)
          (sym (cong (evalLetter gs) (letterEq-sound t (P.flip u) p) ∙ eval-flip u))
    ... | Cubical.Relation.Nullary.no p =
      cong (stackEval gs) (cong (λ b → if b then us else t ∷ u ∷ us) (false-test (P.letterEq t (P.flip u)) p))
      where
      false-test : (b : Bool) → (b ≡ true → Empty.⊥) → b ≡ false
      false-test false h = refl
      false-test true h = Empty.rec (h refl)

    -- The reversed stack invariant, factored through
    -- stackEval so each pop uses precisely one path cancellation.
    eval-reduceAcc : (w s : P.Word)
      → evalWord gs (P.reduceAcc w s) ≡ stackEval gs s ∙ evalWord gs w
    eval-reduceAcc [] s = eval-revAcc s []
    eval-reduceAcc (t ∷ ts) s = eval-reduceAcc ts (P.push t s)
      ∙ cong (_∙ evalWord gs ts) (eval-push t s)
      ∙ sym (assoc (stackEval gs s) (evalLetter gs t) (evalWord gs ts))

    eval-reduce : (w : P.Word) → evalWord gs (P.reduce w) ≡ evalWord gs w
    eval-reduce w = eval-reduceAcc w [] ∙ sym (lUnit (evalWord gs w))

    eval-concatMap : (f : P.Letter → P.Word) (hs : ℕ → a ≡ a)
      → ((t : P.Letter) → evalWord gs (f t) ≡ evalLetter hs t)
      → (w : P.Word) → evalWord gs (P.concatMap f w) ≡ evalWord hs w
    eval-concatMap f hs h [] = refl
    eval-concatMap f hs h (t ∷ ts) = eval-append (f t) (P.concatMap f ts)
      ∙ cong₂ _∙_ (h t) (eval-concatMap f hs h ts)

    eval-substAll : (ids : List ℕ) (ws : List P.Word) (w : P.Word)
      → evalWord gs (substAll ids ws w)
        ≡ evalWord (λ g → evalWord gs (image ids ws g)) w
    eval-substAll ids ws w = eval-reduce (P.concatMap (substLetter ids ws) w)
      ∙ eval-concatMap (substLetter ids ws) (λ g → evalWord gs (image ids ws g)) letter w
      where
      letter : (t : P.Letter) → evalWord gs (substLetter ids ws t)
        ≡ evalLetter (λ g → evalWord gs (image ids ws g)) t
      letter (P.fwd g) = refl
      letter (P.bwd g) = eval-inverse (image ids ws g)

  replacedEnv : ℕ → P.Word → ℕ → a ≡ a
  replacedEnv x r g = if g ≡ᵇ x then evalWord gs r else gs g

  abstract
    eval-substituteLetter : (x : ℕ) (r : P.Word) (t : P.Letter)
      → evalWord gs (P.substituteLetter x r t) ≡ evalLetter (replacedEnv x r) t
    eval-substituteLetter x r (P.fwd g) with g ≡ᵇ x
    ... | true = refl
    ... | false = sym (rUnit (gs g))
    eval-substituteLetter x r (P.bwd g) with g ≡ᵇ x
    ... | true = eval-inverse r
    ... | false = sym (rUnit (sym (gs g)))

    eval-replace : (w : P.Word) (x : ℕ) (r : P.Word)
      → evalWord gs (P.replace w x r) ≡ evalWord (replacedEnv x r) w
    eval-replace w x r = eval-reduce (P.concatMap (P.substituteLetter x r) w)
      ∙ eval-concatMap (P.substituteLetter x r) (replacedEnv x r) (eval-substituteLetter x r) w

open WordLaws public

-- Fin is the library SumFin, matching Syntax's finite positional lookup.
-- Names are labels; repeated names still denote distinct petals.
data Rose (gs : List ℕ) : Type where
  root : Rose gs
  petal : Fin (P.length gs) → root ≡ root

roseRec : {X : Type ℓ} {gs : List ℕ} (b : X) → (Fin (P.length gs) → b ≡ b) → Rose gs → X
roseRec b ps root = b
roseRec b ps (petal i j) = ps i j

lookupLoop : {X : Type ℓ} {a : X} (gs : List ℕ) → (Fin (P.length gs) → a ≡ a) → ℕ → a ≡ a
lookupLoop [] ps g = refl
lookupLoop (h ∷ hs) ps g = if g ≡ᵇ h then ps fzero else lookupLoop hs (ps ∘ fsuc) g

loopAt : (gs : List ℕ) → ℕ → Path (Rose gs) root root
loopAt gs = lookupLoop gs petal

roseWord : (gs : List ℕ) → P.Word → Path (Rose gs) root root
roseWord gs = evalWord (loopAt gs)

circleRec : {X : Type ℓ} (b : X) → b ≡ b → S¹ → X
circleRec b p base = b
circleRec b p (loop i) = p i

wordCircle : (gs : List ℕ) → P.Word → C → Rose gs
wordCircle gs w = circleRec root (roseWord gs w) ∘ Circle.CToCircle

wordCircle-base : (gs : List ℕ) (w : P.Word) → wordCircle gs w 0C ≡ root
wordCircle-base gs w = refl

abstract
  wordCircle-loop : (gs : List ℕ) (w : P.Word)
    → cong (wordCircle gs w) Circle.hC ≡ roseWord gs w
  wordCircle-loop gs w = cong (cong (circleRec root (roseWord gs w))) (sym (lUnit loop))

record Span (ℓO ℓL ℓR : Level) : Type (ℓ-suc (ℓ-max ℓO (ℓ-max ℓL ℓR))) where
  field
    O : Type ℓO
    L : Type ℓL
    R : Type ℓR
    left : O → L
    right : O → R

record SpanEquiv (D : Span ℓO ℓL ℓR) (E : Span ℓO′ ℓL′ ℓR′)
  : Type (ℓ-max (ℓ-max ℓO (ℓ-max ℓL ℓR)) (ℓ-max ℓO′ (ℓ-max ℓL′ ℓR′))) where
  field
    -- `overlap` is reserved by Agda (overlapping instances).
    overlapEquiv : Span.O D ≃ Span.O E
    leftVertex : Span.L D ≃ Span.L E
    rightVertex : Span.R D ≃ Span.R E
    leftSquare : (a : Span.O D) → equivFun leftVertex (Span.left D a)
      ≡ Span.left E (equivFun overlapEquiv a)
    rightSquare : (a : Span.O D) → equivFun rightVertex (Span.right D a)
      ≡ Span.right E (equivFun overlapEquiv a)


FaceIx : Ch.State → Type
FaceIx S = Fin (P.length (Ch.faces S))

faceAt : (S : Ch.State) → FaceIx S → Ch.Face
faceAt S = at (Ch.faces S)

L O R : Ch.State → Type
L S = Rose (Ch.alive S) × C
O S = FaceIx S × T²
R S = FaceIx S × C

left : (S : Ch.State) → O S → L S
left S (i , u , t) = wordCircle (Ch.alive S) (Ch.faceWord (faceAt S i)) u ,
  t +C mulC (int (Ch.faceH (faceAt S i))) u

right : (S : Ch.State) → O S → R S
right S (i , u , t) = i ,
  mulC (int (Ch.faceWeight (faceAt S i))) u +C mulC (Z.pos (Ch.faceOrder (faceAt S i))) t

T : Ch.State → Type
T S = Pushout (left S) (right S)


diagram : Ch.State → Span ℓ-zero ℓ-zero ℓ-zero
diagram S = record { O = O S ; L = L S ; R = R S ; left = left S ; right = right S }

Total : Span ℓO ℓL ℓR → Type (ℓ-max ℓO (ℓ-max ℓL ℓR))
Total D = Pushout (Span.left D) (Span.right D)

module SpanMap {D : Span ℓO ℓL ℓR} {E : Span ℓO′ ℓL′ ℓR′} (e : SpanEquiv D E) where
  open SpanEquiv e
  abstract
    spanEquiv : Total D ≃ Total E
    spanEquiv = Pushout.pushoutEquiv (Span.left D) (Span.right D) (Span.left E) (Span.right E)
      overlapEquiv leftVertex rightVertex (funExt leftSquare) (funExt rightSquare)

    spanEquiv-inl : (x : Span.L D) → equivFun spanEquiv (inl x) ≡ inl (equivFun leftVertex x)
    spanEquiv-inl x = refl

    spanEquiv-inr : (x : Span.R D) → equivFun spanEquiv (inr x) ≡ inr (equivFun rightVertex x)
    spanEquiv-inr x = refl

    spanEquiv-push : (a : Span.O D)
      → PathP (λ j → spanEquiv-inl (Span.left D a) j ≡ spanEquiv-inr (Span.right D a) j)
          (cong (equivFun spanEquiv) (push a))
          (cong inl (leftSquare a) ∙∙ push (equivFun overlapEquiv a) ∙∙ sym (cong inr (rightSquare a)))
    spanEquiv-push a = refl
open SpanMap public

-- An actual signed list decomposition, not a free-group equality.
signedLetter : ℕ → Cell.Sign → P.Letter
signedLetter x Cell.plus = P.fwd x
signedLetter x Cell.minus = P.bwd x

record SingleOccurrence (x : ℕ) (w : P.Word) : Type where
  constructor singleOccurrence
  field
    prefix suffix : P.Word
    sign : Cell.Sign
    decomposition : w ≡ prefix P.++ (signedLetter x sign ∷ suffix)
    prefix-absent : P.all (λ t → not (P.number t ≡ᵇ x)) prefix ≡ true
    suffix-absent : P.all (λ t → not (P.number t ≡ᵇ x)) suffix ≡ true

abstract
  prepend-single : (x : ℕ) (t : P.Letter) (ts : P.Word)
    → not (P.number t ≡ᵇ x) ≡ true → SingleOccurrence x ts → SingleOccurrence x (t ∷ ts)
  prepend-single x t ts e (singleOccurrence u v ε d hu hv) =
    singleOccurrence (t ∷ u) v ε (cong (t ∷_) d) (and-intro e hu) hv

abstract
  test-false : (b : Bool) → (b ≡ true → Empty.⊥) → b ≡ false
  test-false false h = refl
  test-false true h = Empty.rec (h refl)

  occurrences-cons-test : (x : ℕ) (t : P.Letter) (ts : P.Word) (b : Bool)
    → (P.number t ≡ᵇ x) ≡ b
    → (P.occurrences x (t ∷ ts) ≡ᵇ 1) ≡ true
    → ((if b then suc (P.occurrences x ts) else P.occurrences x ts) ≡ᵇ 1) ≡ true
  occurrences-cons-test x t ts true e h = sym (cong (λ b → P.length
    (if b then t ∷ P.filter (λ u → P.number u ≡ᵇ x) ts
          else P.filter (λ u → P.number u ≡ᵇ x) ts) ≡ᵇ 1) e) ∙ h
  occurrences-cons-test x t ts false e h = sym (cong (λ b → P.length
    (if b then t ∷ P.filter (λ u → P.number u ≡ᵇ x) ts
          else P.filter (λ u → P.number u ≡ᵇ x) ts) ≡ᵇ 1) e) ∙ h

  split-single : (x : ℕ) (w : P.Word)
    → (P.occurrences x w ≡ᵇ 1) ≡ true → SingleOccurrence x w
  split-single x [] p = Empty.rec (false≢true p)
  split-single x (P.fwd g ∷ ts) p with bool-dec (g ≡ᵇ x)
  ... | yes e = singleOccurrence [] ts Cell.plus
    (cong (λ g → P.fwd g ∷ ts) (natEq-sound g x e)) refl
    (occurrences-zero x ts (occurrences-cons-test x (P.fwd g) ts true e p))
  ... | no n = prepend-single x (P.fwd g) ts (cong not e)
    (split-single x ts (occurrences-cons-test x (P.fwd g) ts false e p))
    where
    e : (g ≡ᵇ x) ≡ false
    e = test-false (g ≡ᵇ x) n
  split-single x (P.bwd g ∷ ts) p with bool-dec (g ≡ᵇ x)
  ... | yes e = singleOccurrence [] ts Cell.minus
    (cong (λ g → P.bwd g ∷ ts) (natEq-sound g x e)) refl
    (occurrences-zero x ts (occurrences-cons-test x (P.bwd g) ts true e p))
  ... | no n = prepend-single x (P.bwd g) ts (cong not e)
    (split-single x ts (occurrences-cons-test x (P.bwd g) ts false e p))
    where
    e : (g ≡ᵇ x) ≡ false
    e = test-false (g ≡ᵇ x) n

-- Renaming is positional. The named version below derives the permutation
-- from Syntax's membership witnesses and uniqueness reflection.
module RenameRose (gs hs : List ℕ) (e : Fin (P.length gs) ≃ Fin (P.length hs)) where
  rename : Rose gs → Rose hs
  rename = roseRec root (petal ∘ equivFun e)

  unrename : Rose hs → Rose gs
  unrename = roseRec root (petal ∘ invEq e)

  abstract
    rename-section : (r : Rose hs) → rename (unrename r) ≡ r
    rename-section root = refl
    rename-section (petal p i) j = petal (secEq e p j) i

    rename-retraction : (r : Rose gs) → unrename (rename r) ≡ r
    rename-retraction root = refl
    rename-retraction (petal p i) j = petal (retEq e p j) i

    rename-Rose : Rose gs ≃ Rose hs
    rename-Rose = isoToEquiv (iso rename unrename rename-section rename-retraction)

    rename-root : equivFun rename-Rose root ≡ root
    rename-root = refl

    rename-petal : (p : Fin (P.length gs))
      → PathP (λ j → rename-root j ≡ rename-root j)
          (cong (equivFun rename-Rose) (petal p)) (petal (equivFun e p))
    rename-petal p = refl
open RenameRose public

module HeadSplit (x : ℕ) (gs : List ℕ) where
  include : Rose gs → Rose (x ∷ gs)
  include = roseRec root (petal ∘ fsuc)

  split : Rose (x ∷ gs) → Cell.AddLoop (Rose gs) root
  split root = Cell.incQ root
  split (petal fzero i) = Cell.x i
  split (petal (fsuc p) i) = Cell.incQ (petal p i)

  unsplit : Cell.AddLoop (Rose gs) root → Rose (x ∷ gs)
  unsplit (Cell.incQ r) = include r
  unsplit (Cell.x i) = petal fzero i

  abstract
    split-include : (r : Rose gs) → split (include r) ≡ Cell.incQ r
    split-include root = refl
    split-include (petal p i) = refl

    split-section : (r : Cell.AddLoop (Rose gs) root) → split (unsplit r) ≡ r
    split-section (Cell.incQ r) = split-include r
    split-section (Cell.x i) = refl

    split-retraction : (r : Rose (x ∷ gs)) → unsplit (split r) ≡ r
    split-retraction root = refl
    split-retraction (petal fzero i) = refl
    split-retraction (petal (fsuc p) i) = refl

    split-head-Rose : Rose (x ∷ gs) ≃ Cell.AddLoop (Rose gs) root
    split-head-Rose = isoToEquiv (iso split unsplit split-section split-retraction)

    split-root : equivFun split-head-Rose root ≡ Cell.incQ root
    split-root = refl

    split-new-petal : PathP (λ j → split-root j ≡ split-root j)
      (cong (equivFun split-head-Rose) (petal fzero)) Cell.x
    split-new-petal = refl

    split-old-petal : (p : Fin (P.length gs))
      → PathP (λ j → split-root j ≡ split-root j)
          (cong (equivFun split-head-Rose) (petal (fsuc p))) (cong Cell.incQ (petal p))
    split-old-petal p = refl
open HeadSplit public

-- The general functor on GraphWord makes its exponent comparison transparent.
mapGraphWord : {G H : Type} → (G → H) → General.GraphWord G → General.GraphWord H
mapGraphWord f General.emptyWord = General.emptyWord
mapGraphWord f (General.surviving p) = General.surviving (f p)
mapGraphWord f General.eliminated = General.eliminated
mapGraphWord f (General.concatWord u v) = General.concatWord (mapGraphWord f u) (mapGraphWord f v)
mapGraphWord f (General.reverseWord u) = General.reverseWord (mapGraphWord f u)

-- A total positional search; the fallback is emptyWord, not a spurious
-- surviving generator. Scoped data make the fallback unreachable.
lookupGraph : (gs : List ℕ) → ℕ → General.GraphWord (Fin (P.length gs))
lookupGraph [] g = General.emptyWord
lookupGraph (h ∷ hs) g = if g ≡ᵇ h then General.surviving fzero else mapGraphWord fsuc (lookupGraph hs g)

abstract
  exponent-mapGraph : {G H : Type} (f : G → H) (w : General.GraphWord G)
    → General.exponent-x (mapGraphWord f w) ≡ General.exponent-x w
  exponent-mapGraph f General.emptyWord = refl
  exponent-mapGraph f (General.surviving p) = refl
  exponent-mapGraph f General.eliminated = refl
  exponent-mapGraph f (General.concatWord u v) = cong₂ Z._+_ (exponent-mapGraph f u) (exponent-mapGraph f v)
  exponent-mapGraph f (General.reverseWord u) = cong Z.-_ (exponent-mapGraph f u)

abstract
  exponent-lookupGraph : (gs : List ℕ) (g : ℕ)
    → General.exponent-x (lookupGraph gs g) ≡ Z.pos 0
  exponent-lookupGraph [] g = refl
  exponent-lookupGraph (h ∷ hs) g with g ≡ᵇ h
  ... | true = refl
  ... | false = exponent-mapGraph fsuc (lookupGraph hs g) ∙ exponent-lookupGraph hs g

graphGenerator : (x : ℕ) (gs : List ℕ) → ℕ → General.GraphWord (Fin (P.length gs))
graphGenerator x gs g = if g ≡ᵇ x then General.eliminated else lookupGraph gs g

graphLetter : (x : ℕ) (gs : List ℕ) → P.Letter → General.GraphWord (Fin (P.length gs))
graphLetter x gs (P.fwd g) = graphGenerator x gs g
graphLetter x gs (P.bwd g) = General.reverseWord (graphGenerator x gs g)

listToGraphWord : (x : ℕ) (gs : List ℕ) → P.Word → General.GraphWord (Fin (P.length gs))
listToGraphWord x gs [] = General.emptyWord
listToGraphWord x gs (t ∷ ts) = General.concatWord (graphLetter x gs t) (listToGraphWord x gs ts)

abstract
  exponent-graphLetter : (x : ℕ) (gs : List ℕ) (t : P.Letter)
    → General.exponent-x (graphLetter x gs t) ≡ int (P.exponentLetter x t)
  exponent-graphLetter x gs (P.fwd g) with g ≡ᵇ x
  ... | true = refl
  ... | false = exponent-lookupGraph gs g
  exponent-graphLetter x gs (P.bwd g) with g ≡ᵇ x
  ... | true = refl
  ... | false = cong Z.-_ (exponent-lookupGraph gs g)

  exponent-listToGraphWord : (x : ℕ) (gs : List ℕ) (w : P.Word)
    → General.exponent-x (listToGraphWord x gs w) ≡ int (P.exponent x w)
  exponent-listToGraphWord x gs [] = refl
  exponent-listToGraphWord x gs (t ∷ ts) =
    cong₂ Z._+_ (exponent-graphLetter x gs t) (exponent-listToGraphWord x gs ts)
    ∙ sym (int-add (P.exponentLetter x t) (P.exponent x ts))

open import DeloopS3.Groups.TablePermutation using (unique-injective)

module NamedReindex (gs hs : List ℕ)
  (ug : P.unique _≡ᵇ_ gs ≡ true) (uh : P.unique _≡ᵇ_ hs ≡ true)
  (forward : (g : ℕ) → g ∈ gs → g ∈ hs)
  (backward : (g : ℕ) → g ∈ hs → g ∈ gs) where

  to : Fin (P.length gs) → Fin (P.length hs)
  to i = member-index (forward (at gs i) (at-member gs i)) .fst

  from : Fin (P.length hs) → Fin (P.length gs)
  from i = member-index (backward (at hs i) (at-member hs i)) .fst

  abstract
    to-name : (i : Fin (P.length gs)) → at hs (to i) ≡ at gs i
    to-name i = member-index (forward (at gs i) (at-member gs i)) .snd

    from-name : (i : Fin (P.length hs)) → at gs (from i) ≡ at hs i
    from-name i = member-index (backward (at hs i) (at-member hs i)) .snd

    namedReindex : Fin (P.length gs) ≃ Fin (P.length hs)
    namedReindex = isoToEquiv (iso to from
      (λ i → unique-injective _≡ᵇ_ natEq-refl hs uh (to (from i)) i (to-name (from i) ∙ from-name i))
      (λ i → unique-injective _≡ᵇ_ natEq-refl gs ug (from (to i)) i (from-name (to i) ∙ to-name i)))

    namedReindex-name : (i : Fin (P.length gs)) → at hs (equivFun namedReindex i) ≡ at gs i
    namedReindex-name = to-name
open NamedReindex public

survivors : ℕ → List ℕ → List ℕ
survivors x gs = P.filter (λ g → not (g ≡ᵇ x)) gs

abstract
  filter-self : {A : Type} (p : A → Bool) (xs : List A)
    → P.all p (P.filter p xs) ≡ true
  filter-self p [] = refl
  filter-self p (x ∷ xs) with bool-dec (p x)
  ... | yes e = subst (λ ys → P.all p ys ≡ true)
    (sym (cong (λ b → if b then x ∷ P.filter p xs else P.filter p xs) e))
    (and-intro e (filter-self p xs))
  ... | no n = subst (λ ys → P.all p ys ≡ true)
    (sym (cong (λ b → if b then x ∷ P.filter p xs else P.filter p xs) (test-false (p x) n)))
    (filter-self p xs)

  filter-satisfies : {A : Type} (p : A → Bool) (xs : List A) {x : A}
    → x ∈ P.filter p xs → p x ≡ true
  filter-satisfies p xs = all-sound p (filter-self p xs)

  survivors-absent : (x : ℕ) (gs : List ℕ) → not (P.member _≡ᵇ_ x (survivors x gs)) ≡ true
  survivors-absent x gs = not-true λ p → false≢true
    (sym (cong not (natEq-refl x)) ∙ filter-satisfies (λ g → not (g ≡ᵇ x)) gs
      (member-sound _≡ᵇ_ natEq-sound x (survivors x gs) p))

  front-unique : (x : ℕ) (gs : List ℕ) → P.unique _≡ᵇ_ gs ≡ true
    → P.unique _≡ᵇ_ (x ∷ survivors x gs) ≡ true
  front-unique x gs u = and-intro (survivors-absent x gs)
    (unique-filter (λ g → not (g ≡ᵇ x)) gs u)

  front-forward : (x : ℕ) (gs : List ℕ) (g : ℕ) → g ∈ gs → g ∈ (x ∷ survivors x gs)
  front-forward x gs g m with bool-dec (g ≡ᵇ x)
  ... | yes e = subst (λ h → h ∈ (x ∷ survivors x gs)) (sym (natEq-sound g x e)) here
  ... | no n = there (filter-member-intro (λ g → not (g ≡ᵇ x)) gs m
    (cong not (test-false (g ≡ᵇ x) n)))

  front-backward : (x : ℕ) (gs : List ℕ) → x ∈ gs → (g : ℕ)
    → g ∈ (x ∷ survivors x gs) → g ∈ gs
  front-backward x gs m g here = m
  front-backward x gs m g (there q) = filter-member (λ g → not (g ≡ᵇ x)) gs q

  split-Rose : (x : ℕ) (gs : List ℕ) → P.unique _≡ᵇ_ gs ≡ true → x ∈ gs
    → Rose gs ≃ Cell.AddLoop (Rose (survivors x gs)) root
  split-Rose x gs u m = compEquiv
    (rename-Rose gs (x ∷ survivors x gs)
      (namedReindex gs (x ∷ survivors x gs) u (front-unique x gs u)
        (front-forward x gs) (front-backward x gs m)))
    (split-head-Rose x (survivors x gs))

  split-Rose-root : (x : ℕ) (gs : List ℕ) (u : P.unique _≡ᵇ_ gs ≡ true) (m : x ∈ gs)
    → equivFun (split-Rose x gs u m) root ≡ Cell.incQ root
  split-Rose-root x gs u m =
    cong (equivFun (split-head-Rose x (survivors x gs)))
      (rename-root gs (x ∷ survivors x gs)
        (namedReindex gs (x ∷ survivors x gs) u (front-unique x gs u)
          (front-forward x gs) (front-backward x gs m)))
    ∙ split-root x (survivors x gs)

-- Map-level word functoriality, including a total lookup with an explicit
-- refl fallback. No freeness, groupoid truncation, or decision axiom is used.
abstract
  eval-cong : {X : Type ℓ} {Y : Type ℓ′} {a : X}
    (f : X → Y) (gs : ℕ → a ≡ a) (w : P.Word)
    → cong f (evalWord gs w) ≡ evalWord (λ g → cong f (gs g)) w
  eval-cong f gs [] = refl
  eval-cong f gs (P.fwd g ∷ ts) = cong-∙ f (gs g) (evalWord gs ts)
    ∙ cong (cong f (gs g) ∙_) (eval-cong f gs ts)
  eval-cong f gs (P.bwd g ∷ ts) = cong-∙ f (sym (gs g)) (evalWord gs ts)
    ∙ cong (sym (cong f (gs g)) ∙_) (eval-cong f gs ts)

  lookup-cong : {X : Type ℓ} {Y : Type ℓ′} {a : X} (f : X → Y)
    (gs : List ℕ) (ps : Fin (P.length gs) → a ≡ a) (g : ℕ)
    → cong f (lookupLoop gs ps g) ≡ lookupLoop gs (λ p → cong f (ps p)) g
  lookup-cong f [] ps g = refl
  lookup-cong f (h ∷ hs) ps g with g ≡ᵇ h
  ... | true = refl
  ... | false = lookup-cong f hs (ps ∘ fsuc) g

petalWind : (gs : List ℕ) → List P.Z → Fin (P.length gs) → Z.ℤ
petalWind gs zs p = int (P.nth (P.pos 0) zs (toℕ p))

graphWind : (gs : List ℕ) → List P.Z → Rose gs → C
graphWind gs zs = roseRec 0C (λ p → emloop (petalWind gs zs p))

graphWind-base : (gs : List ℕ) (zs : List P.Z) → graphWind gs zs root ≡ 0C
graphWind-base gs zs = refl

abstract
  lookup-empty-windings : (gs : List ℕ) (g : ℕ) → lookupBy (P.pos 0) gs [] g ≡ P.pos 0
  lookup-empty-windings [] g = refl
  lookup-empty-windings (h ∷ hs) g = refl

abstract
  lookup-winding : (gs : List ℕ) (zs : List P.Z) (g : ℕ)
    → lookupLoop {X = C} {a = 0C} gs (λ p → emloop (petalWind gs zs p)) g
      ≡ emloop (int (lookupBy (P.pos 0) gs zs g))
  lookup-winding [] zs g = sym (emloop-1g ℤGroup)
  lookup-winding (h ∷ hs) [] g with g ≡ᵇ h
  ... | true = refl
  ... | false = lookup-winding hs [] g ∙ cong (emloop ∘ int) (lookup-empty-windings hs g)
  lookup-winding (h ∷ hs) (z ∷ zs) g with g ≡ᵇ h
  ... | true = refl
  ... | false = lookup-winding hs zs g

  wind-letter-sound : (gs : List ℕ) (zs : List P.Z) (t : P.Letter)
    → cong (graphWind gs zs) (evalLetter (loopAt gs) t) ≡ emloop (int (windLetter gs zs t))
  wind-letter-sound gs zs (P.fwd g) = lookup-cong (graphWind gs zs) gs petal g ∙ lookup-winding gs zs g
  wind-letter-sound gs zs (P.bwd g) =
    cong sym (lookup-cong (graphWind gs zs) gs petal g ∙ lookup-winding gs zs g)
    ∙ sym (emloop-sym ℤGroup (int (lookupBy (P.pos 0) gs zs g)))
    ∙ cong emloop (sym (int-negate (lookupBy (P.pos 0) gs zs g)))

  wind-eval : (gs : List ℕ) (zs : List P.Z) (w : P.Word)
    → cong (graphWind gs zs) (roseWord gs w) ≡ emloop (int (wind gs zs w))
  wind-eval gs zs [] = sym (emloop-1g ℤGroup)
  wind-eval gs zs (t ∷ ts) = cong-∙ (graphWind gs zs) (evalLetter (loopAt gs) t) (roseWord gs ts)
    ∙ cong₂ _∙_ (wind-letter-sound gs zs t) (wind-eval gs zs ts)
    ∙ sym (emloop-comp ℤGroup (int (windLetter gs zs t)) (int (wind gs zs ts)))
    ∙ cong emloop (sym (int-add (windLetter gs zs t) (wind gs zs ts)))

  -- Positive-model comparison: establish the equality on S¹ first, then
  -- use the actual retraction C → S¹ → C, preserving the based value.
  wind-on-circle : (gs : List ℕ) (zs : List P.Z) (w : P.Word) (u : S¹)
    → graphWind gs zs (circleRec root (roseWord gs w) u)
      ≡ mulC (int (wind gs zs w)) (Circle.circleToC u)
  wind-on-circle gs zs w base = refl
  wind-on-circle gs zs w (loop i) j =
    (wind-eval gs zs w ∙ cong emloop (sym (Z.·IdR (int (wind gs zs w))))) j i

  wind-sound : (gs : List ℕ) (zs : List P.Z) (w : P.Word) (u : C)
    → graphWind gs zs (wordCircle gs w u) ≡ mulC (int (wind gs zs w)) u
  wind-sound gs zs w u = wind-on-circle gs zs w (Circle.CToCircle u)
    ∙ cong (mulC (int (wind gs zs w))) (Circle.circle-retraction u)

  wind-sound-base : (gs : List ℕ) (zs : List P.Z) (w : P.Word)
    → wind-sound gs zs w 0C ≡ refl
  wind-sound-base gs zs w = sym (lUnit refl)

-- This is also a semantic translation of GraphWord, not only an integer
-- comparison: it respects evaluation in every pointed target.
evalGraphWord : {X : Type ℓ} {a : X} {G : Type} → (G → a ≡ a) → a ≡ a → General.GraphWord G → a ≡ a
evalGraphWord ps p General.emptyWord = refl
evalGraphWord ps p (General.surviving g) = ps g
evalGraphWord ps p General.eliminated = p
evalGraphWord ps p (General.concatWord u v) = evalGraphWord ps p u ∙ evalGraphWord ps p v
evalGraphWord ps p (General.reverseWord u) = sym (evalGraphWord ps p u)

abstract
  evalGraph-map : {X : Type ℓ} {a : X} {G H : Type}
    (ps : H → a ≡ a) (p : a ≡ a) (f : G → H) (w : General.GraphWord G)
    → evalGraphWord ps p (mapGraphWord f w) ≡ evalGraphWord (ps ∘ f) p w
  evalGraph-map ps p f General.emptyWord = refl
  evalGraph-map ps p f (General.surviving g) = refl
  evalGraph-map ps p f General.eliminated = refl
  evalGraph-map ps p f (General.concatWord u v) = cong₂ _∙_ (evalGraph-map ps p f u) (evalGraph-map ps p f v)
  evalGraph-map ps p f (General.reverseWord u) = cong sym (evalGraph-map ps p f u)

  evalGraph-lookup : {X : Type ℓ} {a : X} (gs : List ℕ)
    (ps : Fin (P.length gs) → a ≡ a) (p : a ≡ a) (g : ℕ)
    → evalGraphWord ps p (lookupGraph gs g) ≡ lookupLoop gs ps g
  evalGraph-lookup [] ps p g = refl
  evalGraph-lookup (h ∷ hs) ps p g with g ≡ᵇ h
  ... | true = refl
  ... | false = evalGraph-map ps p fsuc (lookupGraph hs g) ∙ evalGraph-lookup hs (ps ∘ fsuc) p g

  evalGraph-generator : {X : Type ℓ} {a : X} (x : ℕ) (gs : List ℕ)
    (ps : Fin (P.length gs) → a ≡ a) (p : a ≡ a) (g : ℕ)
    → evalGraphWord ps p (graphGenerator x gs g) ≡ (if g ≡ᵇ x then p else lookupLoop gs ps g)
  evalGraph-generator x gs ps p g with g ≡ᵇ x
  ... | true = refl
  ... | false = evalGraph-lookup gs ps p g

  evalGraph-letter : {X : Type ℓ} {a : X} (x : ℕ) (gs : List ℕ)
    (ps : Fin (P.length gs) → a ≡ a) (p : a ≡ a) (t : P.Letter)
    → evalGraphWord ps p (graphLetter x gs t)
      ≡ evalLetter (λ g → if g ≡ᵇ x then p else lookupLoop gs ps g) t
  evalGraph-letter x gs ps p (P.fwd g) = evalGraph-generator x gs ps p g
  evalGraph-letter x gs ps p (P.bwd g) = cong sym (evalGraph-generator x gs ps p g)

  eval-listToGraphWord : {X : Type ℓ} {a : X} (x : ℕ) (gs : List ℕ)
    (ps : Fin (P.length gs) → a ≡ a) (p : a ≡ a) (w : P.Word)
    → evalGraphWord ps p (listToGraphWord x gs w)
      ≡ evalWord (λ g → if g ≡ᵇ x then p else lookupLoop gs ps g) w
  eval-listToGraphWord x gs ps p [] = refl
  eval-listToGraphWord x gs ps p (t ∷ ts) =
    cong₂ _∙_ (evalGraph-letter x gs ps p t) (eval-listToGraphWord x gs ps p ts)

-- The finite lookup interface used to prescribe maps on named petals.
-- Uniqueness is essential: without it a name denotes its first occurrence.
abstract
  lookupLoop-at : {X : Type ℓ} {a : X} (gs : List ℕ)
    (ps : Fin (P.length gs) → a ≡ a) → P.unique _≡ᵇ_ gs ≡ true
    → (i : Fin (P.length gs)) → lookupLoop gs ps (at gs i) ≡ ps i
  lookupLoop-at [] ps u ()
  lookupLoop-at (g ∷ gs) ps u fzero = cong
    (λ b → if b then ps fzero else lookupLoop gs (ps ∘ fsuc) g) (natEq-refl g)
  lookupLoop-at (g ∷ gs) ps u (fsuc i) = cong
    (λ b → if b then ps fzero else lookupLoop gs (ps ∘ fsuc) (at gs i))
    (test-false (at gs i ≡ᵇ g) absent)
    ∙ lookupLoop-at gs (ps ∘ fsuc) (and-right {a = not (P.member _≡ᵇ_ g gs)} u) i
    where
    absent : (at gs i ≡ᵇ g) ≡ true → Empty.⊥
    absent e = false≢true
      (sym (cong not (member-complete _≡ᵇ_ natEq-refl
        (subst (λ h → h ∈ gs) (natEq-sound (at gs i) g e) (at-member gs i)))) ∙ and-left u)

  lookupLoop-member : {X : Type ℓ} {a : X} (gs : List ℕ)
    (ps : Fin (P.length gs) → a ≡ a) → P.unique _≡ᵇ_ gs ≡ true
    → (g : ℕ) (m : g ∈ gs) → lookupLoop gs ps g ≡ ps (member-index m .fst)
  lookupLoop-member gs ps u g m =
    sym (cong (lookupLoop gs ps) (member-index m .snd))
    ∙ lookupLoop-at gs ps u (member-index m .fst)

  loopAt-index : (gs : List ℕ) → P.unique _≡ᵇ_ gs ≡ true
    → (i : Fin (P.length gs)) → loopAt gs (at gs i) ≡ petal i
  loopAt-index gs = lookupLoop-at gs petal
