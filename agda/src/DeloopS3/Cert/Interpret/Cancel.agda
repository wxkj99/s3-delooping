{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cert.Interpret.Cancel where

-- Reflected primitive cancellation and retained torus seams.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Cubical.Data.Bool using (Bool; true; false; not; if_then_else_; false≢true)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc)
import Cubical.Data.Empty as Empty
import Cubical.Data.Int as Z
open import Cubical.HITs.Pushout.Base using (Pushout; inl; inr; push)
import Cubical.HITs.Pushout.Properties as PO
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
open import DeloopS3.Cert.Interpret.Syntax
open import DeloopS3.Cert.Interpret.Realization hiding (to; from; include; front-unique)
open import DeloopS3.Cert.Interpret.Realized public
import DeloopS3.Move.CancelLoopCell as Cell
import DeloopS3.Move.CancelGeneral as General
import DeloopS3.Move.PrimitiveTotal as Primitive
import DeloopS3.Move.PrimitiveTotalAffine as Affine

private variable
  ℓ ℓV ℓQ ℓA ℓD : Level

abstract
  not-to-false : (b : Bool) → not b ≡ true → b ≡ false
  not-to-false false h = refl
  not-to-false true h = Empty.rec (false≢true h)

  eval-absent-replace : {X : Type ℓ} {a : X} (gs : ℕ → a ≡ a)
    (x : ℕ) (r w : P.Word)
    → P.all (λ t → not (P.number t ≡ᵇ x)) w ≡ true
    → evalWord (replacedEnv gs x r) w ≡ evalWord gs w
  eval-absent-replace gs x r [] h = refl
  eval-absent-replace gs x r (t ∷ ts) h =
    cong₂ _∙_ letter (eval-absent-replace gs x r ts
      (and-right {a = not (P.number t ≡ᵇ x)} h))
    where
    letter : evalLetter (replacedEnv gs x r) t ≡ evalLetter gs t
    letter = helper t (and-left h)
      where
      helper : (t : P.Letter) → not (P.number t ≡ᵇ x) ≡ true
        → evalLetter (replacedEnv gs x r) t ≡ evalLetter gs t
      helper (P.fwd g) p = cong
        (λ b → if b then evalWord gs r else gs g) (not-to-false (g ≡ᵇ x) p)
      helper (P.bwd g) p = cong sym (cong
        (λ b → if b then evalWord gs r else gs g) (not-to-false (g ≡ᵇ x) p))

  eval-signed-letter : {X : Type ℓ} {a : X} (gs : ℕ → a ≡ a)
    (x : ℕ) (ε : Cell.Sign)
    → evalLetter gs (signedLetter x ε) ≡ Cell.power ε (gs x)
  eval-signed-letter gs x Cell.plus = refl
  eval-signed-letter gs x Cell.minus = refl

  eval-single : {X : Type ℓ} {a : X} (gs : ℕ → a ≡ a)
    (x : ℕ) (w : P.Word) (one : SingleOccurrence x w)
    → evalWord gs w ≡
      (evalWord gs (SingleOccurrence.prefix one) ∙ Cell.power (SingleOccurrence.sign one) (gs x))
        ∙ evalWord gs (SingleOccurrence.suffix one)
  eval-single gs x w one = cong (evalWord gs) (SingleOccurrence.decomposition one)
    ∙ eval-append gs pre (signedLetter x ε ∷ post)
    ∙ cong (λ p → evalWord gs pre ∙ (p ∙ evalWord gs post)) (eval-signed-letter gs x ε)
    ∙ assoc (evalWord gs pre) (Cell.power ε (gs x)) (evalWord gs post)
    where
    pre post : P.Word
    pre = SingleOccurrence.prefix one
    post = SingleOccurrence.suffix one
    ε : Cell.Sign
    ε = SingleOccurrence.sign one

-- Extract all semantic inputs from Cert.Check. No checkMove premise,
-- selected equivalence, or target well-formedness is accepted as evidence.
module Reflected (ct : Ch.Certificate) (S S′ : Ch.State) (s : Ch.Step)
  (wf : WellFormed (suc (Ch.index ct)) S)
  (ok : Ch.checkStep ct S s S′ ≡ true) where
  facts : StepFacts ct S s S′
  facts = checkStep-reflect {ct = ct} {S = S} {S′ = S′} {s = s} ok

  removed : Ch.Face
  removed = found facts

  x : ℕ
  x = Ch.removedGenerator s

  gs : List ℕ
  gs = survivors x (Ch.alive S)

  private
    ts : List Bool
    ts = stepTests ct S s S′ removed
    test : (i : ℕ) → P.nth true ts i ≡ true
    test i = test-true ts i (tests-ok facts)

  abstract
    order-one : Ch.faceOrder removed ≡ 1
    order-one = natEq-sound (Ch.faceOrder removed) 1 (test 0)

    generator-alive : x ∈ Ch.alive S
    generator-alive = member-sound _≡ᵇ_ natEq-sound x (Ch.alive S) (test 1)

    single : SingleOccurrence x (Ch.faceWord removed)
    single = split-single x (Ch.faceWord removed) (test 2)

    replacement-absent : P.all (λ t → not (P.number t ≡ᵇ x)) (Ch.replacement s) ≡ true
    replacement-absent = occurrences-zero x (Ch.replacement s) (test 6)

    replacement-scoped : inScope gs (Ch.replacement s) ≡ true
    replacement-scoped = all-intro (λ t → P.member _≡ᵇ_ (P.number t) gs) (Ch.replacement s)
      (λ t m → member-filter-keep x (Ch.alive S) (P.number t)
        (all-sound (λ t → P.member _≡ᵇ_ (P.number t) (Ch.alive S)) (test 8) m)
        (all-sound (λ t → not (P.number t ≡ᵇ x)) replacement-absent m))

    relation-reduces : P.replace (Ch.faceWord removed) x (Ch.replacement s) ≡ []
    relation-reduces = wordEq-sound _ [] (test 9)

    winding-equation : int (Ch.faceH removed)
      Z.+ (int (P.exponent x (Ch.faceWord removed)) Z.· int (Ch.replacementH s))
      ≡ int (Ch.faceWeight removed)
    winding-equation = sym (int-add (Ch.faceH removed)
        (P.exponent x (Ch.faceWord removed) P.*z Ch.replacementH s)
      ∙ cong (int (Ch.faceH removed) Z.+_)
        (int-multiply (P.exponent x (Ch.faceWord removed)) (Ch.replacementH s)))
      ∙ cong int (zEq-sound _ _ (test 10))

    snapshot : Ch.advance S s ≡ S′
    snapshot = stateEq-sound (Ch.advance S s) S′ (test 12)

    next-wf : WellFormed (suc (Ch.index ct)) S′
    next-wf = advance-wf {ct = ct} {s = s} wf ok refl

  prefix suffix : P.Word
  prefix = SingleOccurrence.prefix single
  suffix = SingleOccurrence.suffix single

  ε : Cell.Sign
  ε = SingleOccurrence.sign single

  L₀ R₀ : Path (Rose gs) root root
  L₀ = roseWord gs prefix
  R₀ = roseWord gs suffix

  replacement-loop : Path (Rose gs) root root
  replacement-loop = roseWord gs (Ch.replacement s)

  abstract
    replacement-filling : (L₀ ∙ Cell.power ε replacement-loop) ∙ R₀ ≡ refl
    replacement-filling = sym expanded
      ∙ sym (eval-replace (loopAt gs) (Ch.faceWord removed) x (Ch.replacement s))
      ∙ cong (evalWord (loopAt gs)) relation-reduces
      where
      env : ℕ → Path (Rose gs) root root
      env = replacedEnv (loopAt gs) x (Ch.replacement s)
      env-x : env x ≡ replacement-loop
      env-x = cong (λ b → if b then replacement-loop else loopAt gs x) (natEq-refl x)
      expanded : evalWord env (Ch.faceWord removed)
        ≡ (L₀ ∙ Cell.power ε replacement-loop) ∙ R₀
      expanded = eval-single env x (Ch.faceWord removed) single
        ∙ cong₂ _∙_
          (cong₂ _∙_
            (eval-absent-replace (loopAt gs) x (Ch.replacement s) prefix
              (SingleOccurrence.prefix-absent single))
            (cong (Cell.power ε) env-x))
          (eval-absent-replace (loopAt gs) x (Ch.replacement s) suffix
            (SingleOccurrence.suffix-absent single))

  graph-solution : Cell.Sign → Path (Rose gs) root root
  graph-solution Cell.plus = sym L₀ ∙ sym R₀
  graph-solution Cell.minus = R₀ ∙ L₀

  abstract
    graph-solution-fills : (sign : Cell.Sign)
      → (L₀ ∙ Cell.power sign (graph-solution sign)) ∙ R₀ ≡ refl
    graph-solution-fills Cell.plus = Cell.solve-plus L₀ R₀
    graph-solution-fills Cell.minus = Cell.solve-minus L₀ R₀

    -- Equality in the FULL loop-equation fibre, including the relation
    -- comparison. This is not merely an equality of π₁ classes.
    replacement-comparison : Path
      (Σ[ y ∈ Path (Rose gs) root root ] ((L₀ ∙ Cell.power ε y) ∙ R₀ ≡ refl))
      (replacement-loop , replacement-filling)
      (graph-solution ε , graph-solution-fills ε)
    replacement-comparison = sym (contract .snd (replacement-loop , replacement-filling))
      ∙ contract .snd (graph-solution ε , graph-solution-fills ε)
      where
      contract : isContr (Σ[ y ∈ Path (Rose gs) root root ]
        ((L₀ ∙ Cell.power ε y) ∙ R₀ ≡ refl))
      contract = Cell.solve-loop root L₀ R₀ ε

    replacement-formula : replacement-loop ≡ graph-solution ε
    replacement-formula = cong fst replacement-comparison

    -- The pre-existing k_v is the first summand, never overwritten.
    retained-face-winding : (f : Ch.Face)
      → int (Ch.faceH (Ch.rewriteFace s f))
        ≡ int (Ch.faceH f) Z.+
          (int (P.exponent x (Ch.faceWord f)) Z.· int (Ch.replacementH s))
    retained-face-winding f = int-add (Ch.faceH f)
      (P.exponent x (Ch.faceWord f) P.*z Ch.replacementH s)
      ∙ cong (int (Ch.faceH f) Z.+_)
        (int-multiply (P.exponent x (Ch.faceWord f)) (Ch.replacementH s))

-- Normalize BEFORE applying ReplaceLeft. The extra χ survives on the
-- entire overlap type, hence on its circle/torus instances and their cubes.
module CorrectedReplaceLeft
  {V : Type ℓV} {Q : Type ℓQ} {A : Type ℓA} {D : Type ℓD}
  (j : Q ≃ V) (r : V → Q) (H : (v : V) → equivFun j (r v) ≡ v)
  (uOld : A → V) (b : A → D) (uCanonical : A → Q)
  (χ : (a : A) → uCanonical a ≡ r (uOld a)) where
  module Rpl = General.ReplaceLeft j r H uOld b

  Canonical : Type (ℓ-max ℓA (ℓ-max ℓQ ℓD))
  Canonical = Pushout uCanonical b

  Staged : Type (ℓ-max ℓA (ℓ-max ℓV ℓD))
  Staged = Pushout uOld b

  normalize : Canonical → Rpl.O′
  normalize (inl q) = inl q
  normalize (inr d) = inr d
  normalize (push a i) = (cong inl (χ a) ∙ push a) i

  abstract
    normalize-isEquiv : isEquiv normalize
    normalize-isEquiv = subst isEquiv (funExt agrees) (e .snd)
      where
      e : Canonical ≃ Rpl.O′
      e = PO.pushoutEquiv uCanonical b (r ∘ uOld) b
        (idEquiv A) (idEquiv Q) (idEquiv D) (funExt χ) refl
      agrees : (z : Canonical) → equivFun e z ≡ normalize z
      agrees (inl q) = refl
      agrees (inr d) = refl
      agrees (push a i) k = sym (leftright (cong inl (χ a)) (push a)) k i

  stage-inl : V → Staged
  stage-inl = inl

  normalized-inl : Q → Rpl.O′
  normalized-inl = inl

  stage-push : (a : A) → Path Staged (stage-inl (uOld a)) (inr (b a))
  stage-push = push

  normalized-push : (a : A) → Path Rpl.O′ (normalized-inl (r (uOld a))) (inr (b a))
  normalized-push = push

  backward-seam : (a : A)
    → Path Staged (stage-inl (equivFun j (uCanonical a))) (inr (b a))
  backward-seam a = cong stage-inl (cong (equivFun j) (χ a) ∙ H (uOld a)) ∙ stage-push a

  backward : Canonical → Staged
  backward = Cell.PushoutUP.extend uCanonical b Staged
    ((inl ∘ equivFun j) , inr , backward-seam)

  abstract
    corrected-seam : (a : A)
      → cong (Rpl.F ∘ normalize) (push a) ≡ backward-seam a
    corrected-seam a = cong-∙ Rpl.F (cong normalized-inl (χ a)) (normalized-push a)
      ∙ assoc (cong stage-inl (cong (equivFun j) (χ a)))
          (cong stage-inl (H (uOld a))) (stage-push a)
      ∙ cong (_∙ stage-push a) (sym (cong-∙ stage-inl (cong (equivFun j) (χ a)) (H (uOld a))))

    backward-agrees : Rpl.F ∘ normalize ≡ backward
    backward-agrees k (inl q) = inl (equivFun j q)
    backward-agrees k (inr d) = inr d
    backward-agrees k (push a i) = corrected-seam a k i

    backward-isEquiv : isEquiv backward
    backward-isEquiv = subst isEquiv backward-agrees
      (compEquiv (normalize , normalize-isEquiv) Rpl.FEquiv .snd)

    backward-equiv : Canonical ≃ Staged
    backward-equiv = backward , backward-isEquiv

    forward-equiv : Staged ≃ Canonical
    forward-equiv = invEquiv backward-equiv

    back-rec : invEq forward-equiv ≡ Cell.PushoutUP.extend uCanonical b Staged
      ((inl ∘ equivFun j) , inr , backward-seam)
    back-rec = refl

abstract
  exponent-append : (x : ℕ) (v w : P.Word)
    → int (P.exponent x (v P.++ w)) ≡ int (P.exponent x v) Z.+ int (P.exponent x w)
  exponent-append x [] w = Z.pos0+ (int (P.exponent x w))
  exponent-append x (t ∷ ts) w = int-add (P.exponentLetter x t) (P.exponent x (ts P.++ w))
    ∙ cong (int (P.exponentLetter x t) Z.+_) (exponent-append x ts w)
    ∙ Z.+Assoc (int (P.exponentLetter x t)) (int (P.exponent x ts)) (int (P.exponent x w))
    ∙ cong (Z._+ int (P.exponent x w)) (sym (int-add (P.exponentLetter x t) (P.exponent x ts)))

  exponent-absent-letter : (x : ℕ) (t : P.Letter)
    → not (P.number t ≡ᵇ x) ≡ true → int (P.exponentLetter x t) ≡ Z.pos 0
  exponent-absent-letter x (P.fwd g) h = cong
    (λ b → int (if b then P.pos 1 else P.pos 0)) (not-to-false (g ≡ᵇ x) h)
  exponent-absent-letter x (P.bwd g) h = cong
    (λ b → int (if b then P.neg 0 else P.pos 0)) (not-to-false (g ≡ᵇ x) h)

  exponent-absent : (x : ℕ) (w : P.Word)
    → P.all (λ t → not (P.number t ≡ᵇ x)) w ≡ true → int (P.exponent x w) ≡ Z.pos 0
  exponent-absent x [] h = refl
  exponent-absent x (t ∷ ts) h = int-add (P.exponentLetter x t) (P.exponent x ts)
    ∙ cong₂ Z._+_ (exponent-absent-letter x t (and-left h))
      (exponent-absent x ts (and-right {a = not (P.number t ≡ᵇ x)} h))

  exponent-signed : (x : ℕ) (ε : Cell.Sign)
    → int (P.exponentLetter x (signedLetter x ε)) ≡ General.signInt ε
  exponent-signed x Cell.plus = cong
    (λ b → int (if b then P.pos 1 else P.pos 0)) (natEq-refl x)
  exponent-signed x Cell.minus = cong
    (λ b → int (if b then P.neg 0 else P.pos 0)) (natEq-refl x)

  exponent-single : (x : ℕ) (w : P.Word) (one : SingleOccurrence x w)
    → int (P.exponent x w) ≡ General.signInt (SingleOccurrence.sign one)
  exponent-single x w one = cong (int ∘ P.exponent x) (SingleOccurrence.decomposition one)
    ∙ exponent-append x pre (signedLetter x ε ∷ post)
    ∙ cong₂ Z._+_ (exponent-absent x pre (SingleOccurrence.prefix-absent one))
      (int-add (P.exponentLetter x (signedLetter x ε)) (P.exponent x post)
        ∙ cong₂ Z._+_ (exponent-signed x ε)
          (exponent-absent x post (SingleOccurrence.suffix-absent one)))
    ∙ sym (Z.pos0+ (General.signInt ε))
    where
    pre post : P.Word
    pre = SingleOccurrence.prefix one
    post = SingleOccurrence.suffix one
    ε : Cell.Sign
    ε = SingleOccurrence.sign one

  difference-solve : (k κ s : Z.ℤ) → k Z.+ κ ≡ s → κ ≡ s Z.- k
  difference-solve k κ s h =
    cong (κ Z.+_) (sym (Z.-Cancel k))
    ∙ Z.+Assoc κ k (Z.- k)
    ∙ cong (Z._+ (Z.- k)) (Z.+Comm κ k ∙ h)

  signed-difference-solve : (ε : Cell.Sign) (k κ s : Z.ℤ)
    → k Z.+ (General.signInt ε Z.· κ) ≡ s
    → κ ≡ General.signInt ε Z.· (s Z.- k)
  signed-difference-solve Cell.plus k κ s h = difference-solve k κ s h
  signed-difference-solve Cell.minus k κ s h = sym (Z.-Involutive κ)
    ∙ cong Z.-_ (difference-solve k (Z.- κ) s h)

module ReflectedCoordinates (ct : Ch.Certificate) (S S′ : Ch.State) (s : Ch.Step)
  (wf : WellFormed (suc (Ch.index ct)) S)
  (ok : Ch.checkStep ct S s S′ ≡ true) where
  open Reflected ct S S′ s wf ok
  module D = Primitive.Diagram (Rose gs) root L₀ R₀ ε
    (int (Ch.faceWeight removed)) (int (Ch.faceH removed))
  module Coord = Primitive.Coordinates (Rose gs) root L₀ R₀ ε
    (int (Ch.faceWeight removed)) (int (Ch.faceH removed))
  module Fwd = General.ForwardGraph (Rose gs) root L₀ R₀
    (int (Ch.faceWeight removed)) (int (Ch.faceH removed))
  module Words = Coord.Words (Fin (P.length gs)) petal

  κ : Z.ℤ
  κ = int (Ch.replacementH s)

  abstract
    replacementH-formula : κ ≡ General.signInt ε Z.· D.q
    replacementH-formula = signed-difference-solve ε
      (int (Ch.faceH removed)) κ (int (Ch.faceWeight removed))
      (cong (λ z → int (Ch.faceH removed) Z.+ (z Z.· κ))
          (sym (exponent-single x (Ch.faceWord removed) single))
        ∙ winding-equation)

  expected-generator : Fwd.point ≡ Fwd.point
  expected-generator = cong Fwd.graph replacement-loop ∙ Fwd.h κ

  abstract
    expected-solution : expected-generator ≡ Fwd.graph-solution ε
    expected-solution = by-sign ε replacement-formula replacementH-formula
      where
      by-sign : (sign : Cell.Sign) → replacement-loop ≡ graph-solution sign
        → κ ≡ General.signInt sign Z.· D.q
        → expected-generator ≡ Fwd.graph-solution sign
      by-sign Cell.plus p h = cong₂ _∙_
        (cong (cong Fwd.graph) p ∙ cong-∙ Fwd.graph (sym L₀) (sym R₀))
        (cong Fwd.h h)
      by-sign Cell.minus p h = cong₂ _∙_
        (cong (cong Fwd.graph) p ∙ cong-∙ Fwd.graph R₀ L₀)
        (cong Fwd.h h ∙ Fwd.h-negate D.q)

    deleted-generator-formula : Coord.deleted-generator ≡ expected-generator
    deleted-generator-formula = Coord.deleted-generator-formula ∙ sym expected-solution

    deleted-generator-fibre : cong snd Coord.deleted-generator ≡ emloop κ
    deleted-generator-fibre = Coord.deleted-generator-fibre ∙ cong emloop (sym replacementH-formula)

    retained-face-formula : (f : Ch.Face)
      → cong snd (Words.eval (listToGraphWord x gs (Ch.faceWord f)) ∙ Fwd.h (int (Ch.faceH f)))
        ≡ emloop (int (Ch.faceH (Ch.rewriteFace s f)))
    retained-face-formula f = Words.lifted-word-winding
        (listToGraphWord x gs (Ch.faceWord f)) (int (Ch.faceH f))
      ∙ cong emloop
        (cong (int (Ch.faceH f) Z.+_)
          (cong₂ Z._·_ (exponent-listToGraphWord x gs (Ch.faceWord f)) (sym replacementH-formula))
          ∙ sym (retained-face-winding f))

  -- Preserve the full primitive cell comparison as well as its first
  -- projection. The second projection is a path of relation witnesses.
  open Coord public using (deleted-generator-comparison)

-- A based, name-computing chart for the rose split. It is kept separate
-- from the abstract positional equivalence so its petal equations do not
-- require conversion to expand the latter's proof of equivalence.
open import Cubical.Relation.Nullary using (yes; no)

namedRose : {X : Type ℓ} (a : X) (gs : List ℕ) → (ℕ → a ≡ a) → Rose gs → X
namedRose a gs ps = roseRec a (λ i → ps (at gs i))

abstract
  namedRose-loop : {X : Type ℓ} (a : X) (gs : List ℕ) (ps : ℕ → a ≡ a)
    → P.unique _≡ᵇ_ gs ≡ true → (g : ℕ) → g ∈ gs
    → cong (namedRose a gs ps) (loopAt gs g) ≡ ps g
  namedRose-loop a gs ps unique g m = lookup-cong (namedRose a gs ps) gs petal g
    ∙ lookupLoop-member gs (λ i → ps (at gs i)) unique g m
    ∙ cong ps (member-index m .snd)

module NamedSplit (x : ℕ) (old : List ℕ)
  (unique : P.unique _≡ᵇ_ old ≡ true) (present : x ∈ old) where
  kept : List ℕ
  kept = survivors x old

  Q : Type
  Q = Rose kept

  A : Type
  A = Cell.AddLoop Q root

  unique-kept : P.unique _≡ᵇ_ kept ≡ true
  unique-kept = unique-filter (λ g → not (g ≡ᵇ x)) old unique

  generator : ℕ → Path A (Cell.incQ root) (Cell.incQ root)
  generator g = if g ≡ᵇ x then Cell.x else cong Cell.incQ (loopAt kept g)

  to : Rose old → A
  to = namedRose (Cell.incQ root) old generator

  include : Q → Rose old
  include = namedRose root kept (loopAt old)

  from : A → Rose old
  from (Cell.incQ a) = include a
  from (Cell.x i) = loopAt old x i

  abstract
    to-loop : (g : ℕ) → g ∈ old → cong to (loopAt old g) ≡ generator g
    to-loop = namedRose-loop (Cell.incQ root) old generator unique

    to-deleted : cong to (loopAt old x) ≡ Cell.x
    to-deleted = to-loop x present ∙ cong
      (λ b → if b then Cell.x else cong Cell.incQ (loopAt kept x)) (natEq-refl x)

    to-surviving : (g : ℕ) → g ∈ kept
      → cong to (loopAt old g) ≡ cong Cell.incQ (loopAt kept g)
    to-surviving g m = to-loop g (filter-member (λ g → not (g ≡ᵇ x)) old m)
      ∙ cong (λ b → if b then Cell.x else cong Cell.incQ (loopAt kept g))
        (not-to-false (g ≡ᵇ x) (filter-satisfies (λ g → not (g ≡ᵇ x)) old m))

    from-generator : (g : ℕ) → g ∈ old → cong from (generator g) ≡ loopAt old g
    from-generator g m with bool-dec (g ≡ᵇ x)
    ... | yes p = cong (cong from)
        (cong (λ b → if b then Cell.x else cong Cell.incQ (loopAt kept g)) p)
      ∙ cong (loopAt old) (sym (natEq-sound g x p))
    ... | no p = cong (cong from)
        (cong (λ b → if b then Cell.x else cong Cell.incQ (loopAt kept g)) e)
      ∙ namedRose-loop root kept (loopAt old) unique-kept g
        (filter-member-intro (λ g → not (g ≡ᵇ x)) old m (cong not e))
      where
      e : (g ≡ᵇ x) ≡ false
      e = test-false (g ≡ᵇ x) p

    to-include : (q : Q) → to (include q) ≡ Cell.incQ q
    to-include root = refl
    to-include (petal i k) j =
      (to-surviving (at kept i) (at-member kept i)
        ∙ cong (cong Cell.incQ) (loopAt-index kept unique-kept i)) j k

    chart-section : (a : A) → to (from a) ≡ a
    chart-section (Cell.incQ q) = to-include q
    chart-section (Cell.x i) j = to-deleted j i

    chart-retraction : (a : Rose old) → from (to a) ≡ a
    chart-retraction root = refl
    chart-retraction (petal i k) j =
      (from-generator (at old i) (at-member old i) ∙ loopAt-index old unique i) j k

    split-equiv : Rose old ≃ A
    split-equiv = isoToEquiv (iso to from chart-section chart-retraction)

    split-map : equivFun split-equiv ≡ to
    split-map = refl

    split-inverse : invEq split-equiv ≡ from
    split-inverse = refl

open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import DeloopS3.Move.CancelMinimal using (K; 0K; U; ω)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (assocₖ)
import DeloopS3.Cover.Orientation.CircleModel as Circle

abstract
  scoped-eval-agree : {X : Type ℓ} {a : X} (ids : List ℕ)
    (p q : ℕ → a ≡ a) → ((g : ℕ) → g ∈ ids → p g ≡ q g)
    → (w : P.Word) → inScope ids w ≡ true → evalWord p w ≡ evalWord q w
  scoped-eval-agree ids p q h [] scope = refl
  scoped-eval-agree ids p q h (P.fwd g ∷ ts) scope = cong₂ _∙_
    (h g (member-sound _≡ᵇ_ natEq-sound g ids (and-left scope)))
    (scoped-eval-agree ids p q h ts (and-right {a = P.member _≡ᵇ_ g ids} scope))
  scoped-eval-agree ids p q h (P.bwd g ∷ ts) scope = cong₂ _∙_
    (cong sym (h g (member-sound _≡ᵇ_ natEq-sound g ids (and-left scope))))
    (scoped-eval-agree ids p q h ts (and-right {a = P.member _≡ᵇ_ g ids} scope))

module ReflectedTorus (ct : Ch.Certificate) (S S′ : Ch.State) (s : Ch.Step)
  (wf : WellFormed (suc (Ch.index ct)) S)
  (ok : Ch.checkStep ct S s S′ ≡ true) where
  module Ref = Reflected ct S S′ s wf ok
  open Ref
  module RC = ReflectedCoordinates ct S S′ s wf ok
  module D = RC.D
  module Coord = RC.Coord
  module Fwd = RC.Fwd
  module Words = RC.Words
  module Split = NamedSplit x (Ch.alive S) (alive-distinct wf) generator-alive
  module Base = Cell.PrimitiveCancellation (Rose gs) root L₀ R₀ ε
  module TotalAffinity = Affine.Affine (Rose gs) root L₀ R₀ ε
    (int (Ch.faceWeight removed)) (int (Ch.faceH removed))

  abstract
    r-via-total : (a : D.oldGraph) (t : C)
      → D.r (inl (a , t)) ≡ D.total-cancel .fst (inl a , ω .fst t)
    r-via-total a t = sym (cong D.r (D.to-old-graph a t))
      ∙ D.r-hit (inl (a , t))
      ∙ cong (D.total-cancel .fst) (D.flatten-graph a t)

    r-affine : (a : D.oldGraph) (t : C)
      → D.r (inl (a , t))
        ≡ (D.r (inl (a , 0C)) .fst , t +C D.r (inl (a , 0C)) .snd)
    r-affine a t = r-via-total a t ∙ TotalAffinity.GraphAffinity.f-affine a t
      ∙ cong (λ z → z .fst , t +C z .snd) (sym (r-via-total a 0C))
  module Normal = Primitive.PointedGraphImage root
    (λ a → D.r (inl (a , 0C))) Fwd.graph (λ a → D.unit (a , 0C))

  normalized : Rose (Ch.alive S) → Rose gs × C
  normalized = Normal.normalized ∘ Split.to

  env : ℕ → Fwd.point ≡ Fwd.point
  env g = if g ≡ᵇ x then Coord.deleted-generator else cong Fwd.graph (loopAt gs g)

  abstract
    normal-generator : (g : ℕ) → cong Normal.normalized (Split.generator g) ≡ env g
    normal-generator g with g ≡ᵇ x
    ... | true = refl
    ... | false = refl

    normal-loop : (g : ℕ) → g ∈ Ch.alive S
      → cong normalized (loopAt (Ch.alive S) g) ≡ env g
    normal-loop g m = cong (cong Normal.normalized) (Split.to-loop g m) ∙ normal-generator g

    normal-word : (w : P.Word) → inScope (Ch.alive S) w ≡ true
      → cong normalized (roseWord (Ch.alive S) w) ≡ evalWord env w
    normal-word w scope = eval-cong normalized (loopAt (Ch.alive S)) w
      ∙ scoped-eval-agree (Ch.alive S) (λ g → cong normalized (loopAt (Ch.alive S) g))
        env normal-loop w scope

    graph-env : (g : ℕ) → cong fst (env g) ≡ replacedEnv (loopAt gs) x (Ch.replacement s) g
    graph-env g with g ≡ᵇ x
    ... | true = cong (cong fst) RC.deleted-generator-formula
      ∙ cong-∙ fst (cong Fwd.graph replacement-loop) (Fwd.h RC.κ)
      ∙ sym (rUnit replacement-loop)
    ... | false = refl

    graph-word : (w : P.Word) → inScope (Ch.alive S) w ≡ true
      → cong (fst ∘ normalized) (roseWord (Ch.alive S) w)
        ≡ roseWord gs (P.replace w x (Ch.replacement s))
    graph-word w scope = cong (cong fst) (normal-word w scope)
      ∙ eval-cong fst env w
      ∙ cong (λ hs → evalWord hs w) (funExt graph-env)
      ∙ sym (eval-replace (loopAt gs) w x (Ch.replacement s))

    word-coordinates : (v : General.GraphWord (Fin (P.length gs)))
      → Words.eval v ≡ evalGraphWord (λ i → cong Fwd.graph (petal i)) Coord.deleted-generator v
    word-coordinates General.emptyWord = refl
    word-coordinates (General.surviving i) = refl
    word-coordinates General.eliminated = refl
    word-coordinates (General.concatWord u v) = cong₂ _∙_ (word-coordinates u) (word-coordinates v)
    word-coordinates (General.reverseWord v) = cong sym (word-coordinates v)

    graph-lookup : (g : ℕ)
      → lookupLoop gs (λ i → cong Fwd.graph (petal i)) g ≡ cong Fwd.graph (loopAt gs g)
    graph-lookup g = sym (lookup-cong Fwd.graph gs petal g)

    translated-env : (g : ℕ)
      → (if g ≡ᵇ x then Coord.deleted-generator else lookupLoop gs (λ i → cong Fwd.graph (petal i)) g)
        ≡ env g
    translated-env g with g ≡ᵇ x
    ... | true = refl
    ... | false = graph-lookup g

    translated-word : (w : P.Word)
      → Words.eval (listToGraphWord x gs w) ≡ evalWord env w
    translated-word w = word-coordinates (listToGraphWord x gs w)
      ∙ eval-listToGraphWord x gs (λ i → cong Fwd.graph (petal i)) Coord.deleted-generator w
      ∙ cong (λ hs → evalWord hs w) (funExt translated-env)

    fibre-word : (w : P.Word) → inScope (Ch.alive S) w ≡ true
      → cong (snd ∘ normalized) (roseWord (Ch.alive S) w)
        ≡ emloop (int (P.exponent x w) Z.· RC.κ)
    fibre-word w scope = cong (cong snd) (normal-word w scope ∙ sym (translated-word w))
      ∙ Words.word-fibre-winding (listToGraphWord x gs w)
      ∙ cong emloop (cong₂ Z._·_ (exponent-listToGraphWord x gs w) (sym RC.replacementH-formula))

    normal-on-circle : (w : P.Word) → inScope (Ch.alive S) w ≡ true → (u : S¹)
      → normalized (circleRec root (roseWord (Ch.alive S) w) u)
        ≡ (circleRec root (roseWord gs (P.replace w x (Ch.replacement s))) u ,
            mulC (int (P.exponent x w) Z.· RC.κ) (Circle.circleToC u))
    normal-on-circle w scope base = refl
    normal-on-circle w scope (loop i) j = graph-word w scope j i ,
      (fibre-word w scope ∙ cong emloop (sym (Z.·IdR (int (P.exponent x w) Z.· RC.κ)))) j i

    normal-circle : (w : P.Word) → inScope (Ch.alive S) w ≡ true → (u : C)
      → normalized (wordCircle (Ch.alive S) w u)
        ≡ (wordCircle gs (P.replace w x (Ch.replacement s)) u ,
            mulC (int (P.exponent x w) Z.· RC.κ) u)
    normal-circle w scope u = normal-on-circle w scope (Circle.CToCircle u)
      ∙ (λ i → wordCircle gs (P.replace w x (Ch.replacement s)) u ,
          mulC (int (P.exponent x w) Z.· RC.κ) (Circle.circle-retraction u i))

    graph-affinity : (a : D.oldGraph) (t : C)
      → D.r (inl (a , t))
        ≡ (Normal.normalized a .fst , t +C Normal.normalized a .snd)
    graph-affinity a t = r-affine a t
      ∙ cong (λ z → z .fst , t +C z .snd) (λ i → Normal.comparison i a)

    -- The whole torus map, not just its two loop degrees. Its inverse is
    -- the χ used in the seam correction.
    retained-torus : (f : Ch.Face) → inScope (Ch.alive S) (Ch.faceWord f) ≡ true
      → (u t : C)
      → D.r (inl (Split.to (wordCircle (Ch.alive S) (Ch.faceWord f) u) ,
            t +C mulC (int (Ch.faceH f)) u))
        ≡ (wordCircle gs (Ch.faceWord (Ch.rewriteFace s f)) u ,
            t +C mulC (int (Ch.faceH (Ch.rewriteFace s f))) u)
    retained-torus f scope u t =
      graph-affinity (Split.to (wordCircle (Ch.alive S) (Ch.faceWord f) u))
        (t +C mulC (int (Ch.faceH f)) u)
      ∙ cong (λ z → z .fst , (t +C mulC (int (Ch.faceH f)) u) +C z .snd)
        (normal-circle (Ch.faceWord f) scope u)
      ∙ (λ i → wordCircle gs (Ch.faceWord (Ch.rewriteFace s f)) u , arithmetic i)
      where
      arithmetic : (t +C mulC (int (Ch.faceH f)) u)
          +C mulC (int (P.exponent x (Ch.faceWord f)) Z.· RC.κ) u
        ≡ t +C mulC (int (Ch.faceH (Ch.rewriteFace s f))) u
      arithmetic = sym (assocₖ {G = ℤAbGroup} 1 t (mulC (int (Ch.faceH f)) u)
          (mulC (int (P.exponent x (Ch.faceWord f)) Z.· RC.κ) u))
        ∙ cong (t +C_) (sym (General.CircleCoordinates.mulC-add (int (Ch.faceH f))
          (int (P.exponent x (Ch.faceWord f)) Z.· RC.κ) u))
        ∙ cong (λ k → t +C mulC k u) (sym (retained-face-winding f))

-- Finite positional bookkeeping is shared with the terminal interpreter;
-- it contains no cancellation or geometric premise.
import DeloopS3.Cert.Interpret.Terminal as Terminal
open import Cubical.Data.Sum using (_⊎_) renaming (inl to sumL; inr to sumR)

abstract
  getFace-found : (key : ℕ) (fs : List Ch.Face) (f : Ch.Face)
    → Ch.getFace key fs ≡ P.just f → (f ∈ fs) × (Ch.faceId f ≡ key)
  getFace-found key [] f h = Empty.rec (false≢true (cong isJust h))
    where
    isJust : P.Maybe Ch.Face → Bool
    isJust P.nothing = false
    isJust (P.just _) = true
  getFace-found key (g ∷ fs) f h with bool-dec (Ch.faceId g ≡ᵇ key)
  ... | yes e = subst (λ f → (f ∈ (g ∷ fs)) × (Ch.faceId f ≡ key)) same
      (here , natEq-sound (Ch.faceId g) key e)
    where
    extract : P.Maybe Ch.Face → Ch.Face
    extract P.nothing = f
    extract (P.just a) = a
    same : g ≡ f
    same = cong extract
      (sym (cong (λ b → if b then P.just g else Ch.getFace key fs) e) ∙ h)
  ... | no ne = there (rest .fst) , rest .snd
    where
    rest : (f ∈ fs) × (Ch.faceId f ≡ key)
    rest = getFace-found key fs f
      (sym (cong (λ b → if b then P.just g else Ch.getFace key fs)
        (test-false (Ch.faceId g ≡ᵇ key) ne)) ∙ h)

module FaceOrder (ct : Ch.Certificate) (S S′ : Ch.State) (s : Ch.Step)
  (wf : WellFormed (suc (Ch.index ct)) S)
  (ok : Ch.checkStep ct S s S′ ≡ true) where
  open Reflected ct S S′ s wf ok
  fs : List Ch.Face
  fs = Ch.faces S
  key : ℕ
  key = Ch.removedBoundary s
  keep : Ch.Face → Bool
  keep f = not (Ch.faceId f ≡ᵇ key)
  kept : List Ch.Face
  kept = P.filter keep fs
  front : List Ch.Face
  front = removed ∷ kept

  abstract
    removed-member : removed ∈ fs
    removed-member = getFace-found key fs removed (found-ok facts) .fst
    removed-id : Ch.faceId removed ≡ key
    removed-id = getFace-found key fs removed (found-ok facts) .snd
    kept-unique : P.unique _≡ᵇ_ (P.map Ch.faceId kept) ≡ true
    kept-unique = unique-filter-map Ch.faceId keep fs (ids-distinct wf)
    front-unique : P.unique _≡ᵇ_ (P.map Ch.faceId front) ≡ true
    front-unique = and-intro (not-true absent) kept-unique
      where
      absent : P.member _≡ᵇ_ (Ch.faceId removed) (P.map Ch.faceId kept) ≡ true → Empty.⊥
      absent p = false≢true (sym (cong not (natEq-refl key)) ∙
        sym (cong (λ k → not (k ≡ᵇ key)) (w .snd .snd ∙ removed-id)) ∙
        filter-satisfies keep fs (w .snd .fst))
        where
        w : Σ[ f ∈ Ch.Face ] ((f ∈ kept) × (Ch.faceId f ≡ Ch.faceId removed))
        w = map-member⁻ Ch.faceId kept
          (member-sound _≡ᵇ_ natEq-sound (Ch.faceId removed) (P.map Ch.faceId kept) p)

    front-in-old : (f : Ch.Face) → f ∈ front → f ∈ fs
    front-in-old f here = removed-member
    front-in-old f (there m) = filter-member keep fs m

    old-in-front : (f : Ch.Face) → f ∈ fs → f ∈ front
    old-in-front f m with bool-dec (Ch.faceId f ≡ᵇ key)
    ... | yes e = subst (λ g → g ∈ front)
      (sym (Terminal.face-id-injective fs (ids-distinct wf) f removed m removed-member
        (natEq-sound _ _ e ∙ sym removed-id))) here
    ... | no ne = there (filter-member-intro keep fs m
      (cong not (test-false (Ch.faceId f ≡ᵇ key) ne)))

  index-to : Fin (P.length front) → FaceIx S
  index-to i = member-index (front-in-old (at front i) (at-member front i)) .fst
  index-from : FaceIx S → Fin (P.length front)
  index-from i = member-index (old-in-front (at fs i) (at-member fs i)) .fst

  abstract
    index-face : (i : Fin (P.length front)) → faceAt S (index-to i) ≡ at front i
    index-face i = member-index (front-in-old (at front i) (at-member front i)) .snd
    index-face-back : (i : FaceIx S) → at front (index-from i) ≡ faceAt S i
    index-face-back i = member-index (old-in-front (at fs i) (at-member fs i)) .snd
    indices : Fin (P.length front) ≃ FaceIx S
    indices = isoToEquiv (iso index-to index-from
      (λ i → Terminal.face-index-injective fs (ids-distinct wf) (index-to (index-from i)) i
        (cong Ch.faceId (index-face (index-from i) ∙ index-face-back i)))
      (λ i → Terminal.face-index-injective front front-unique (index-from (index-to i)) i
        (cong Ch.faceId (index-face-back (index-to i) ∙ index-face i))))
    indices-map : equivFun indices ≡ index-to
    indices-map = refl

    removed-scope : inScope (Ch.alive S) (Ch.faceWord removed) ≡ true
    removed-scope = and-right {a = P.wordValid (suc (Ch.index ct)) (Ch.faceWord removed)}
      (all-sound (λ f → scopedWord (suc (Ch.index ct)) (Ch.alive S) (Ch.faceWord f))
        (words-in-scope wf) removed-member)
    kept-scope : (i : Fin (P.length kept)) → inScope (Ch.alive S) (Ch.faceWord (at kept i)) ≡ true
    kept-scope i = and-right {a = P.wordValid (suc (Ch.index ct)) (Ch.faceWord (at kept i))}
      (all-sound (λ f → scopedWord (suc (Ch.index ct)) (Ch.alive S) (Ch.faceWord f))
        (words-in-scope wf) (filter-member keep fs (at-member kept i)))

module Pack {X : Type} (n : ℕ) where
  pack : X ⊎ (Fin n × X) → Fin (suc n) × X
  pack (sumL x) = fzero , x
  pack (sumR (i , x)) = fsuc i , x
  unpack : Fin (suc n) × X → X ⊎ (Fin n × X)
  unpack (fzero , x) = sumL x
  unpack (fsuc i , x) = sumR (i , x)
  abstract
    pack-equiv : (X ⊎ (Fin n × X)) ≃ (Fin (suc n) × X)
    pack-equiv = isoToEquiv (iso pack unpack
      (λ { (fzero , x) → refl ; (fsuc i , x) → refl })
      (λ { (sumL x) → refl ; (sumR (i , x)) → refl }))
    pack-map : equivFun pack-equiv ≡ pack
    pack-map = refl

abstract
  eval-switch-absent : {X : Type ℓ} {a : X} (env : ℕ → a ≡ a)
    (x : ℕ) (p : a ≡ a) (w : P.Word)
    → P.all (λ t → not (P.number t ≡ᵇ x)) w ≡ true
    → evalWord (λ g → if g ≡ᵇ x then p else env g) w ≡ evalWord env w
  eval-switch-absent env x p [] h = refl
  eval-switch-absent env x p (t ∷ ts) h = cong₂ _∙_
    (letter t (and-left h)) (eval-switch-absent env x p ts (and-right {a = not (P.number t ≡ᵇ x)} h))
    where
    letter : (t : P.Letter) → not (P.number t ≡ᵇ x) ≡ true
      → evalLetter (λ g → if g ≡ᵇ x then p else env g) t ≡ evalLetter env t
    letter (P.fwd g) h = cong (λ b → if b then p else env g) (not-to-false (g ≡ᵇ x) h)
    letter (P.bwd g) h = cong sym (cong (λ b → if b then p else env g) (not-to-false (g ≡ᵇ x) h))

open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emsquash)
open import Cubical.HITs.EilenbergMacLane1.Properties using (elimSet)

abstract
  mul-one : (t : C) → mulC (Z.pos 1) t ≡ t
  mul-one = elimSet ℤGroup (λ _ → emsquash _ _) refl (λ g i j → emloop g i)

abstract
  based-cong : {X : Type ℓV} {Y : Type ℓQ} {a b : X}
    (f : X → Y) (p : a ≡ b) (l : a ≡ a)
    → transport (λ i → f (p i) ≡ f (p i)) (cong f l)
      ≡ cong f (transport (λ i → p i ≡ p i) l)
  based-cong f p l = fromPathP
    {A = λ i → f (p i) ≡ f (p i)}
    {x = cong f l} {y = cong f (transport (λ i → p i ≡ p i) l)}
    (λ i j → f (transport-filler (λ i → p i ≡ p i) l i j))

module Cancellation (ct : Ch.Certificate) (S S′ : Ch.State) (s : Ch.Step)
  (wf : WellFormed (suc (Ch.index ct)) S)
  (ok : Ch.checkStep ct S s S′ ≡ true) where
  module Ref = Reflected ct S S′ s wf ok
  open Ref
  module Tor = ReflectedTorus ct S S′ s wf ok
  module Face = FaceOrder ct S S′ s wf ok
  module D = Tor.D
  module Split = Tor.Split
  module Base = Tor.Base

  Ix : Type
  Ix = Fin (P.length Face.kept)

  retained-left : Ix × T² → D.oldGraph × C
  retained-left (i , u , t) = Split.to (wordCircle (Ch.alive S) (Ch.faceWord (at Face.kept i)) u) ,
    t +C mulC (int (Ch.faceH (at Face.kept i))) u

  retained-right : Ix × T² → Ix × C
  retained-right (i , u , t) = i ,
    mulC (int (Ch.faceWeight (at Face.kept i))) u +C mulC (Z.pos (Ch.faceOrder (at Face.kept i))) t

  canonical-left : Ix × T² → Rose gs × C
  canonical-left (i , u , t) = wordCircle gs (Ch.faceWord (Ch.rewriteFace s (at Face.kept i))) u ,
    t +C mulC (int (Ch.faceH (Ch.rewriteFace s (at Face.kept i)))) u

  module Stage = Primitive.Staging₂ D.left retained-left D.right retained-right

  abstract
    χ : (a : Ix × T²) → canonical-left a ≡ D.r (inl (retained-left a))
    χ (i , u , t) = sym (Tor.retained-torus (at Face.kept i) (Face.kept-scope i) u t)

  module Back = CorrectedReplaceLeft (D.j , D.j-isEquiv) D.r D.counit
    (inl ∘ retained-left) retained-right canonical-left χ

  abstract
    split-absent : (w : P.Word) → P.all (λ t → not (P.number t ≡ᵇ x)) w ≡ true
      → evalWord Split.generator w ≡ cong Cell.incQ (roseWord gs w)
    split-absent w h = eval-switch-absent (λ g → cong Cell.incQ (loopAt gs g)) x Cell.x w h
      ∙ sym (eval-cong Cell.incQ (loopAt gs) w)

    removed-word : cong Split.to (roseWord (Ch.alive S) (Ch.faceWord removed)) ≡ Base.w
    removed-word = eval-cong Split.to (loopAt (Ch.alive S)) (Ch.faceWord removed)
      ∙ scoped-eval-agree (Ch.alive S) (λ g → cong Split.to (loopAt (Ch.alive S) g))
        Split.generator Split.to-loop (Ch.faceWord removed) Face.removed-scope
      ∙ eval-single Split.generator x (Ch.faceWord removed) single
      ∙ cong₂ _∙_
        (cong₂ _∙_ (split-absent prefix (SingleOccurrence.prefix-absent single))
          (cong (Cell.power ε) (cong
            (λ b → if b then Cell.x else cong Cell.incQ (loopAt gs x)) (natEq-refl x))))
        (split-absent suffix (SingleOccurrence.suffix-absent single))

    removed-circle : (u : C) → Split.to (wordCircle (Ch.alive S) (Ch.faceWord removed) u) ≡ D.wordCircle u
    removed-circle u = on-S¹ (Circle.CToCircle u)
      where
      on-S¹ : (v : S¹) → Split.to (circleRec root (roseWord (Ch.alive S) (Ch.faceWord removed)) v)
        ≡ Cell.circleMap Base.w v
      on-S¹ base = refl
      on-S¹ (loop i) j = removed-word j i

    split-back-map : invEq Split.split-equiv ≡ Split.from
    split-back-map = Split.split-inverse

  graph-back : D.oldGraph × C → L S
  graph-back (a , t) = Split.from a , t

  overlap-back : T² ⊎ (Ix × T²) → O S
  overlap-back a = Face.index-to (Pack.pack (P.length Face.kept) a .fst) ,
    Pack.pack (P.length Face.kept) a .snd

  core-back : C ⊎ (Ix × C) → R S
  core-back a = Face.index-to (Pack.pack (P.length Face.kept) a .fst) ,
    Pack.pack (P.length Face.kept) a .snd

  abstract
    graph-back-equiv : isEquiv graph-back
    graph-back-equiv = subst isEquiv
      (funExt λ { (a , t) i → split-back-map i a , t })
      (Σ-cong-equiv-fst (invEquiv Split.split-equiv) .snd)

    overlap-back-equiv : isEquiv overlap-back
    overlap-back-equiv = subst isEquiv (funExt formula)
      (compEquiv (Pack.pack-equiv {X = T²} (P.length Face.kept)) (Σ-cong-equiv-fst Face.indices) .snd)
      where
      formula : (a : T² ⊎ (Ix × T²)) → equivFun
        (compEquiv (Pack.pack-equiv {X = T²} (P.length Face.kept)) (Σ-cong-equiv-fst Face.indices)) a ≡ overlap-back a
      formula a = cong (λ z → equivFun Face.indices (z .fst) , z .snd)
          (funExt⁻ (Pack.pack-map (P.length Face.kept)) a)
        ∙ (λ i → Face.indices-map i (Pack.pack (P.length Face.kept) a .fst) ,
          Pack.pack (P.length Face.kept) a .snd)

    core-back-equiv : isEquiv core-back
    core-back-equiv = subst isEquiv (funExt formula)
      (compEquiv (Pack.pack-equiv {X = C} (P.length Face.kept)) (Σ-cong-equiv-fst Face.indices) .snd)
      where
      formula : (a : C ⊎ (Ix × C)) → equivFun
        (compEquiv (Pack.pack-equiv {X = C} (P.length Face.kept)) (Σ-cong-equiv-fst Face.indices)) a ≡ core-back a
      formula a = cong (λ z → equivFun Face.indices (z .fst) , z .snd)
          (funExt⁻ (Pack.pack-map (P.length Face.kept)) a)
        ∙ (λ i → Face.indices-map i (Pack.pack (P.length Face.kept) a .fst) ,
          Pack.pack (P.length Face.kept) a .snd)

    old-left-square : (a : T² ⊎ (Ix × T²))
      → graph-back (Stage.allLeft a) ≡ left S (overlap-back a)
    old-left-square (sumL (u , t)) =
      (λ i → (sym (cong Split.from (removed-circle u))
          ∙ Split.chart-retraction (wordCircle (Ch.alive S) (Ch.faceWord removed) u)) i ,
        t +C mulC (int (Ch.faceH removed)) u)
      ∙ cong (λ f → wordCircle (Ch.alive S) (Ch.faceWord f) u , t +C mulC (int (Ch.faceH f)) u)
        (sym (Face.index-face fzero))
    old-left-square (sumR (i , u , t)) =
      (λ j → Split.chart-retraction (wordCircle (Ch.alive S) (Ch.faceWord (at Face.kept i)) u) j ,
        t +C mulC (int (Ch.faceH (at Face.kept i))) u)
      ∙ cong (λ f → wordCircle (Ch.alive S) (Ch.faceWord f) u , t +C mulC (int (Ch.faceH f)) u)
        (sym (Face.index-face (fsuc i)))

    old-right-square : (a : T² ⊎ (Ix × T²))
      → core-back (Stage.allRight a) ≡ right S (overlap-back a)
    old-right-square (sumL (u , t)) =
      (λ i → Face.index-to fzero , mulC (int (Ch.faceWeight removed)) u +C
        (sym (mul-one t) ∙ cong (λ d → mulC (Z.pos d) t) (sym order-one)) i)
      ∙ cong (λ f → Face.index-to fzero , mulC (int (Ch.faceWeight f)) u +C mulC (Z.pos (Ch.faceOrder f)) t)
        (sym (Face.index-face fzero))
    old-right-square (sumR (i , u , t)) = cong
      (λ f → Face.index-to (fsuc i) , mulC (int (Ch.faceWeight f)) u +C mulC (Z.pos (Ch.faceOrder f)) t)
      (sym (Face.index-face (fsuc i)))

    old-chart : Stage.All ≃ T S
    old-chart = PO.pushoutEquiv Stage.allLeft Stage.allRight (left S) (right S)
      (overlap-back , overlap-back-equiv) (graph-back , graph-back-equiv) (core-back , core-back-equiv)
      (funExt old-left-square) (funExt old-right-square)

  computed : Ch.State
  computed = Ch.advance S s

  target-index : FaceIx computed → Ix
  target-index = Terminal.back-index (Ch.rewriteFace s) Face.kept

  target-overlap : O computed → Ix × T²
  target-overlap (i , z) = target-index i , z

  target-core : R computed → Ix × C
  target-core (i , t) = target-index i , t

  abstract
    target-face : (i : FaceIx computed)
      → faceAt computed i ≡ Ch.rewriteFace s (at Face.kept (target-index i))
    target-face = Terminal.at-back-index (Ch.rewriteFace s) Face.kept

    target-index-isEquiv : isEquiv target-index
    target-index-isEquiv = subst isEquiv
      (funExt (Terminal.map-index-equiv-map (Ch.rewriteFace s) Face.kept))
      (Terminal.map-index-equiv (Ch.rewriteFace s) Face.kept .snd)

    target-left-square : (a : O computed) → left computed a ≡ canonical-left (target-overlap a)
    target-left-square (i , u , t) = cong
      (λ f → wordCircle gs (Ch.faceWord f) u , t +C mulC (int (Ch.faceH f)) u) (target-face i)

    target-right-square : (a : O computed)
      → target-core (right computed a) ≡ retained-right (target-overlap a)
    target-right-square (i , u , t) = cong
      (λ f → target-index i , mulC (int (Ch.faceWeight f)) u +C mulC (Z.pos (Ch.faceOrder f)) t)
      (target-face i)

  canonical-inl : Rose gs × C → Back.Canonical
  canonical-inl = inl
  canonical-inr : Ix × C → Back.Canonical
  canonical-inr = inr
  canonical-push : (a : Ix × T²)
    → canonical-inl (canonical-left a) ≡ canonical-inr (retained-right a)
  canonical-push = push

  target-seam : (a : O computed)
    → canonical-inl (left computed a) ≡ canonical-inr (target-core (right computed a))
  target-seam a = cong canonical-inl (target-left-square a)
    ∙∙ canonical-push (target-overlap a) ∙∙ sym (cong canonical-inr (target-right-square a))

  target-map : T computed → Back.Canonical
  target-map (inl l) = canonical-inl l
  target-map (inr r) = canonical-inr (target-core r)
  target-map (push a i) = target-seam a i

  abstract
    target-map-isEquiv : isEquiv target-map
    target-map-isEquiv = subst isEquiv (funExt agrees) (e .snd)
      where
      e : T computed ≃ Back.Canonical
      e = PO.pushoutEquiv (left computed) (right computed) canonical-left retained-right
        (Σ-cong-equiv-fst (target-index , target-index-isEquiv)) (idEquiv (Rose gs × C))
        (Σ-cong-equiv-fst (target-index , target-index-isEquiv))
        (funExt target-left-square) (funExt target-right-square)
      agrees : (z : T computed) → equivFun e z ≡ target-map z
      agrees (inl l) = refl
      agrees (inr r) = refl
      agrees (push a i) = refl

    unstage-isEquiv : isEquiv Stage.backward
    unstage-isEquiv = isoToIsEquiv (iso Stage.backward Stage.forward Stage.ret Stage.sec)

  forget-stage : Stage.Staged → T S
  forget-stage = equivFun old-chart ∘ Stage.backward

  abstract
    forget-stage-isEquiv : isEquiv forget-stage
    forget-stage-isEquiv = compEquiv (Stage.backward , unstage-isEquiv) old-chart .snd

  backward : T computed → T S
  backward = forget-stage ∘ Back.backward ∘ target-map

  back-left : L computed → T S
  back-left l = forget-stage (inl (D.j l))

  back-right : R computed → T S
  back-right r = forget-stage (inr (target-core r))

  -- The finite positional chart contributes its endpoint paths. Between
  -- them, the actual retained torus seam is exactly the χ/counit formula,
  -- followed by unstaging and the old graph/face chart.
  back-seam : (a : O computed) → back-left (left computed a) ≡ back-right (right computed a)
  back-seam a = cong back-left (target-left-square a)
    ∙∙ cong forget-stage (Back.backward-seam (target-overlap a))
    ∙∙ sym (cong (λ d → forget-stage (inr d)) (target-right-square a))

  abstract
    backward-seam-formula : (a : O computed) → cong backward (push a) ≡ back-seam a
    backward-seam-formula a = cong-∙∙ (forget-stage ∘ Back.backward)
      (cong canonical-inl (target-left-square a)) (canonical-push (target-overlap a))
      (sym (cong canonical-inr (target-right-square a)))

    backward-rec : backward ≡ Cell.PushoutUP.extend (left computed) (right computed) (T S)
      (back-left , back-right , back-seam)
    backward-rec j (inl l) = back-left l
    backward-rec j (inr r) = back-right r
    backward-rec j (push a i) = backward-seam-formula a j i

    backward-isEquiv : isEquiv backward
    backward-isEquiv = compEquiv (target-map , target-map-isEquiv)
      (compEquiv (Back.backward , Back.backward-isEquiv) (forget-stage , forget-stage-isEquiv)) .snd

    computed-step : RealizedStep (suc (Ch.index ct)) S computed
    computed-step = record
      { next-wf = subst (WellFormed (suc (Ch.index ct))) (sym snapshot) next-wf
      ; total = invEquiv (backward , backward-isEquiv)
      ; backLeft = back-left
      ; backRight = back-right
      ; backSeam = back-seam
      ; back-rec = backward-rec }

    computed-cocone : Path
      (Cell.PushoutUP.Cocone (left computed) (right computed) (T S))
      (RealizedStep.backLeft computed-step , RealizedStep.backRight computed-step , RealizedStep.backSeam computed-step)
      (back-left , back-right , back-seam)
    computed-cocone = refl

    computed-forward-map : equivFun (RealizedStep.total computed-step)
      ≡ invEq (backward , backward-isEquiv)
    computed-forward-map = refl

    old-chart-left : (z : D.oldGraph × C) → equivFun old-chart (inl z) ≡ inl (graph-back z)
    old-chart-left z = refl

-- Cert.Check alone supplies the reflected
-- primitive decomposition, replacement, winding and literal next snapshot.
abstract
  cancel-step-sound : (ct : Ch.Certificate) (S S′ : Ch.State) (s : Ch.Step)
    → WellFormed (suc (Ch.index ct)) S
    → Ch.checkStep ct S s S′ ≡ true
    → RealizedStep (suc (Ch.index ct)) S S′
  cancel-step-sound ct S S′ s wf ok = subst (RealizedStep (suc (Ch.index ct)) S)
    (Reflected.snapshot ct S S′ s wf ok) (Cancellation.computed-step ct S S′ s wf ok)

  cancel-step-sound-computation : (ct : Ch.Certificate) (S S′ : Ch.State) (s : Ch.Step)
    (wf : WellFormed (suc (Ch.index ct)) S) (ok : Ch.checkStep ct S s S′ ≡ true)
    → cancel-step-sound ct S S′ s wf ok ≡ subst (RealizedStep (suc (Ch.index ct)) S)
        (Reflected.snapshot ct S S′ s wf ok) (Cancellation.computed-step ct S S′ s wf ok)
  cancel-step-sound-computation ct S S′ s wf ok = refl

-- This module is intentionally OUTSIDE Cancellation: its isEquiv proof is
-- opaque here, so invEq does not execute the large composite equivalence.
module ForwardCoordinates (ct : Ch.Certificate) (S S′ : Ch.State) (s : Ch.Step)
  (wf : WellFormed (suc (Ch.index ct)) S)
  (ok : Ch.checkStep ct S s S′ ≡ true) where
  module Cancel = Cancellation ct S S′ s wf ok
  open Cancel
  open Cancel.Ref
  -- Forward formulas for the SAME total equivalence, rather than merely
  -- an unrelated primitive equivalence with the same winding numbers.
  partial-inclusion : D.V → T S
  partial-inclusion v = forget-stage (inl v)

  final-inclusion : Rose gs × C → T computed
  final-inclusion = inl

  forward : T S → T computed
  forward = invEq (backward , backward-isEquiv)

  abstract
    forward-is-total : equivFun (RealizedStep.total computed-step) ≡ forward
    forward-is-total = computed-forward-map

    forward-partial : (v : D.V) → forward (partial-inclusion v) ≡ final-inclusion (D.r v)
    forward-partial v = cong (forward ∘ partial-inclusion) (sym (D.counit v))
      ∙ retEq (backward , backward-isEquiv) (final-inclusion (D.r v))

    forward-old-graph : (a : D.oldGraph) (t : C)
      → forward (partial-inclusion (inl (a , t)))
        ≡ final-inclusion (Tor.Normal.normalized a .fst , t +C Tor.Normal.normalized a .snd)
    forward-old-graph a t = forward-partial (inl (a , t))
      ∙ cong final-inclusion (Tor.graph-affinity a t)

    forward-retained-face : (i : Ix) (u t : C)
      → forward (partial-inclusion (inl (retained-left (i , u , t))))
        ≡ final-inclusion (canonical-left (i , u , t))
    forward-retained-face i u t = forward-partial (inl (retained-left (i , u , t)))
      ∙ cong final-inclusion (sym (χ (i , u , t)))

  original-graph : D.oldGraph → T S
  original-graph a = partial-inclusion (inl (a , 0C))

  forward-base : forward (original-graph (Cell.incQ root)) ≡ final-inclusion (root , 0C)
  forward-base = forward-partial (inl (Cell.incQ root , 0C))
    ∙ cong final-inclusion (D.unit (root , 0C))

  actual-deleted-generator : Path (T computed) (final-inclusion (root , 0C)) (final-inclusion (root , 0C))
  actual-deleted-generator = transport (λ i → forward-base i ≡ forward-base i)
    (cong (forward ∘ original-graph) Cell.x)

  abstract
    original-graph-formula : (a : D.oldGraph)
      → original-graph a ≡ inl (Split.from a , 0C)
    original-graph-formula a = old-chart-left (a , 0C)

    -- The actual deleted generator under computed-step.total, with its
    -- explicit basepoint correction and BOTH signs of the primitive word.
    deleted-generator-formula : actual-deleted-generator
      ≡ cong final-inclusion Tor.RC.expected-generator
    deleted-generator-formula = Primitive.based-circle-homotopy
      (final-inclusion (root , 0C))
      (forward ∘ original-graph ∘ Cell.circleMap Cell.x)
      (final-inclusion ∘ Tor.Coord.old-graph ∘ Cell.circleMap Cell.x)
      forward-base (cong final-inclusion (D.unit (root , 0C)))
      (λ u → forward-partial (inl (Cell.circleMap Cell.x u , 0C)))
      (λ i → compPath-filler'
        (forward-partial (inl (Cell.incQ root , 0C)))
        (cong final-inclusion (D.unit (root , 0C))) (~ i))
      ∙ based-cong final-inclusion (D.unit (root , 0C)) (cong Tor.Coord.old-graph Cell.x)
      ∙ cong (cong final-inclusion) Tor.RC.deleted-generator-formula

