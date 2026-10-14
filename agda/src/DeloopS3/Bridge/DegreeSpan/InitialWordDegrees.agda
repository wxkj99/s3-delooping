{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.InitialWordDegrees where

-- H1 of the ACTUAL initial face words. Names in the certificate are not
-- petal positions: every use of a name passes through the unique gs list.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Nat using (ℕ; _≡ᵇ_)
open import Cubical.Data.Nat.Order.Inductive using
  (_≟ᵗ_; lt; eq; gt; <ᵗ-irrefl; isProp<ᵗ)
open import Cubical.Data.Bool using (true; false; if_then_else_)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Fin as F
import Cubical.Data.SumFin as SF
open import Cubical.Data.SumFin.Properties using (SumFin≃Fin)
import Cubical.Data.Empty as Empty
open import Cubical.Data.Int using (ℤ; pos; negsuc; _+_)
open import Cubical.Relation.Nullary using (yes; no; ¬_)
open import Cubical.HITs.S1.Base using (S¹; base; loop; winding; winding-hom)
open import Cubical.HITs.Pushout using (inl; inr; push)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal)
open import Cubical.HITs.Sn.Degree using (degree)
open import DeloopS3.Cover.Orientation.CircleModel using
  (circleToC; circle-section)
open import DeloopS3.Cert.Input.Model.Vocabulary using (ShortCase; octa; icosa; gs; S₀)
open import DeloopS3.Cert.Input.Graph.Maps using (Petal)
open import DeloopS3.Cert.Input.Initial.Faces using (initial-fibre)
open import DeloopS3.Bridge.CoverChains.Incidence using (Bdy)
open import DeloopS3.Bridge.CoverChains.Words using
  (faceIndex; wordExponent; initialExponent)
open import DeloopS3.Bridge.DegreeSpan.Pieces using (rose-bouquet)
open import DeloopS3.Cert.Interpret.Syntax using
  (bool-dec; natEq-refl; natEq-sound; _∈_; here; there;
   at; at-member; at-nth; member-index; member-sound; member-complete)
open import DeloopS3.Groups.TablePermutation using (unique-injective)
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P

-- Transparent public interface for the later product/H2 adapter.
petalProjection : (ns : List ℕ) → SF.Fin (P.length ns) → R.Rose ns → S¹
petalProjection ns j = pickPetal (equivFun (SumFin≃Fin (P.length ns)) j)
  ∘ equivFun (rose-bouquet ns)

actualProjection : (c : ShortCase) → Petal c → R.Rose (gs c) → S¹
actualProjection c = petalProjection (gs c)

actualCircleMap : (c : ShortCase) → Bdy c → Petal c → S¹ → S¹
actualCircleMap c b j x = actualProjection c j
  (fst (R.left (S₀ c) (faceIndex c b , circleToC x , R.0C)))

actualProjectedCircleMap : (c : ShortCase) → Bdy c → Petal c → S¹ → S¹
actualProjectedCircleMap = actualCircleMap

abstract
  source-fibre-is-id : (c : ShortCase) (b : Bdy c) (u t : R.C)
    → snd (R.left (S₀ c) (faceIndex c b , u , t)) ≡ t
  source-fibre-is-id c b = initial-fibre c (faceIndex c b)

-- The joining edges in SphereBouquet must be retained until pickPetal
-- contracts them. This is precisely the loop used by rose-bouquet.
standardLoop : {n : ℕ} (k : F.Fin n)
  → Path (SphereBouquet 1 (F.Fin n)) (inl tt) (inl tt)
standardLoop k = push k ∙∙ (λ i → inr (k , loop i)) ∙∙ sym (push k)

abstract
  pick-loop-self : {n : ℕ} (k : F.Fin n)
    → cong (pickPetal k) (standardLoop k) ≡ loop
  pick-loop-self k = cong-∙∙ (pickPetal k) (push k)
    (λ i → inr (k , loop i)) (sym (push k)) ∙ contract k
    where
    contract : {n : ℕ} (k : F.Fin n)
      → (cong (pickPetal k) (push k)
        ∙∙ (λ i → pickPetal k (inr (k , loop i)))
        ∙∙ sym (cong (pickPetal k) (push k))) ≡ loop
    contract k with fst k ≟ᵗ fst k
    ... | lt p = Empty.rec (<ᵗ-irrefl p)
    ... | gt p = Empty.rec (<ᵗ-irrefl p)
    ... | eq p = sym (rUnit loop)

  pick-loop-other : {n : ℕ} (j k : F.Fin n) → ¬ (j ≡ k)
    → cong (pickPetal j) (standardLoop k) ≡ refl
  pick-loop-other j k ne = cong-∙∙ (pickPetal j) (push k)
    (λ i → inr (k , loop i)) (sym (push k)) ∙ contract j k ne
    where
    contract : {n : ℕ} (j k : F.Fin n) → ¬ (j ≡ k)
      → (cong (pickPetal j) (push k)
        ∙∙ (λ i → pickPetal j (inr (k , loop i)))
        ∙∙ sym (cong (pickPetal j) (push k))) ≡ refl
    contract {n} j k ne with fst j ≟ᵗ fst k
    ... | lt p = sym (rUnit refl)
    ... | gt p = sym (rUnit refl)
    ... | eq p = Empty.rec (ne (Σ≡Prop (λ m → isProp<ᵗ {m} {n}) p))

nameLoop : ℕ → ℕ → base ≡ base
nameLoop a g = if a ≡ᵇ g then loop else refl

abstract
  projected-petal : (ns : List ℕ) → P.unique _≡ᵇ_ ns ≡ true
    → (j k : SF.Fin (P.length ns))
    → cong (petalProjection ns j) (R.petal k) ≡ nameLoop (at ns j) (at ns k)
  projected-petal ns unique j k with bool-dec (at ns j ≡ᵇ at ns k)
  ... | yes e =
    cong (λ k → cong (petalProjection ns j) (R.petal k)) (sym same)
    ∙ pick-loop-self (equivFun (SumFin≃Fin (P.length ns)) j)
    ∙ sym (cong (λ b → if b then loop else refl) e)
    where
    same : j ≡ k
    same = unique-injective _≡ᵇ_ natEq-refl ns unique j k
      (natEq-sound (at ns j) (at ns k) e)
  ... | no ne = pick-loop-other
      (equivFun (SumFin≃Fin (P.length ns)) j)
      (equivFun (SumFin≃Fin (P.length ns)) k) different
    ∙ sym (cong (λ b → if b then loop else refl)
      (R.test-false (at ns j ≡ᵇ at ns k) ne))
    where
    different : ¬ (equivFun (SumFin≃Fin (P.length ns)) j
                  ≡ equivFun (SumFin≃Fin (P.length ns)) k)
    different p = ne
      (cong (at ns j ≡ᵇ_) (sym (cong (at ns)
        (sym (retEq (SumFin≃Fin (P.length ns)) j)
          ∙ cong (invEq (SumFin≃Fin (P.length ns))) p
          ∙ retEq (SumFin≃Fin (P.length ns)) k)))
        ∙ natEq-refl (at ns j))

  lookup-absent : (ns : List ℕ) (g : ℕ) → ¬ (g ∈ ns)
    → R.loopAt ns g ≡ refl
  lookup-absent [] g absent = refl
  lookup-absent (h ∷ hs) g absent with bool-dec (g ≡ᵇ h)
  ... | yes e = Empty.rec (absent
    (subst (λ x → x ∈ (h ∷ hs)) (sym (natEq-sound g h e)) here))
  ... | no ne =
    cong (λ b → if b then R.petal SF.fzero
      else R.lookupLoop hs (R.petal ∘ SF.fsuc) g) (R.test-false (g ≡ᵇ h) ne)
    ∙ tail-absent hs (R.petal ∘ SF.fsuc) g (λ m → absent (there m))
    where
    tail-absent : {X : Type} {a : X} (xs : List ℕ)
      (ps : SF.Fin (P.length xs) → a ≡ a) (g : ℕ) → ¬ (g ∈ xs)
      → R.lookupLoop xs ps g ≡ refl
    tail-absent [] ps g absent = refl
    tail-absent (h ∷ hs) ps g absent with bool-dec (g ≡ᵇ h)
    ... | yes e = Empty.rec (absent
      (subst (λ x → x ∈ (h ∷ hs)) (sym (natEq-sound g h e)) here))
    ... | no ne = cong (λ b → if b then ps SF.fzero
        else R.lookupLoop hs (ps ∘ SF.fsuc) g) (R.test-false (g ≡ᵇ h) ne)
      ∙ tail-absent hs (ps ∘ SF.fsuc) g (λ m → absent (there m))

  projected-lookup : (ns : List ℕ) → P.unique _≡ᵇ_ ns ≡ true
    → (j : SF.Fin (P.length ns)) (g : ℕ)
    → cong (petalProjection ns j) (R.loopAt ns g) ≡ nameLoop (at ns j) g
  projected-lookup ns unique j g with bool-dec (P.member _≡ᵇ_ g ns)
  ... | yes e = cong (cong (petalProjection ns j)) (R.lookupLoop-member ns R.petal unique g m)
    ∙ projected-petal ns unique j (member-index m .fst)
    ∙ cong (nameLoop (at ns j)) (member-index m .snd)
    where
    m : g ∈ ns
    m = member-sound _≡ᵇ_ natEq-sound g ns e
  ... | no ne = cong (cong (petalProjection ns j)) (lookup-absent ns g absent)
    ∙ sym (cong (λ b → if b then loop else refl)
      (R.test-false (at ns j ≡ᵇ g) different))
    where
    absent : ¬ (g ∈ ns)
    absent m = ne (member-complete _≡ᵇ_ natEq-refl m)
    different : ¬ ((at ns j ≡ᵇ g) ≡ true)
    different e = absent (subst (λ x → x ∈ ns)
      (natEq-sound (at ns j) g e) (at-member ns j))

-- The integer calculation is an induction on the literal Word, including
-- inverse letters. No cellular incidence/Dhat hypothesis enters the proof.
letterExponent : ℕ → P.Letter → ℤ
letterExponent a (P.fwd g) = if a ≡ᵇ g then pos 1 else pos 0
letterExponent a (P.bwd g) = if a ≡ᵇ g then negsuc 0 else pos 0

abstract
  name-winding-positive : (a g : ℕ)
    → winding (nameLoop a g) ≡ letterExponent a (P.fwd g)
  name-winding-positive a g with a ≡ᵇ g
  ... | true = refl
  ... | false = refl

  name-winding-negative : (a g : ℕ)
    → winding (sym (nameLoop a g)) ≡ letterExponent a (P.bwd g)
  name-winding-negative a g with a ≡ᵇ g
  ... | true = refl
  ... | false = refl

  projected-letter-winding : (ns : List ℕ) → P.unique _≡ᵇ_ ns ≡ true
    → (j : SF.Fin (P.length ns)) (t : P.Letter)
    → winding (cong (petalProjection ns j) (R.evalLetter (R.loopAt ns) t))
      ≡ letterExponent (at ns j) t
  projected-letter-winding ns unique j (P.fwd g) =
    cong winding (projected-lookup ns unique j g)
    ∙ name-winding-positive (at ns j) g
  projected-letter-winding ns unique j (P.bwd g) =
    cong winding (cong sym (projected-lookup ns unique j g))
    ∙ name-winding-negative (at ns j) g

  projected-word-winding : (ns : List ℕ) → P.unique _≡ᵇ_ ns ≡ true
    → (j : SF.Fin (P.length ns)) (w : P.Word)
    → winding (cong (petalProjection ns j) (R.roseWord ns w))
      ≡ wordExponent (at ns j) w
  projected-word-winding ns unique j [] = refl
  projected-word-winding ns unique j (P.fwd g ∷ w) =
    cong winding (cong-∙ (petalProjection ns j) (R.loopAt ns g) (R.roseWord ns w))
    ∙ winding-hom (cong (petalProjection ns j) (R.loopAt ns g))
        (cong (petalProjection ns j) (R.roseWord ns w))
    ∙ cong₂ _+_ (projected-letter-winding ns unique j (P.fwd g))
        (projected-word-winding ns unique j w)
  projected-word-winding ns unique j (P.bwd g ∷ w) =
    cong winding (cong-∙ (petalProjection ns j) (sym (R.loopAt ns g)) (R.roseWord ns w))
    ∙ winding-hom (cong (petalProjection ns j) (sym (R.loopAt ns g)))
        (cong (petalProjection ns j) (R.roseWord ns w))
    ∙ cong₂ _+_ (projected-letter-winding ns unique j (P.bwd g))
        (projected-word-winding ns unique j w)

projectedWordCircle : (ns : List ℕ) → SF.Fin (P.length ns) → P.Word → S¹ → S¹
projectedWordCircle ns j w x = petalProjection ns j (R.wordCircle ns w (circleToC x))

abstract
  -- The degree-one definition computes to winding for this based recursor.
  projected-recursor-degree : (ns : List ℕ) (j : SF.Fin (P.length ns)) (w : P.Word)
    → degree 1 (petalProjection ns j ∘ R.circleRec R.root (R.roseWord ns w))
      ≡ winding (cong (petalProjection ns j) (R.roseWord ns w))
  projected-recursor-degree ns j w = refl

  projected-word-degree : (ns : List ℕ) → P.unique _≡ᵇ_ ns ≡ true
    → (j : SF.Fin (P.length ns)) (w : P.Word)
    → degree 1 (projectedWordCircle ns j w)
      ≡ wordExponent (P.nth 0 ns (SF.toℕ j)) w
  projected-word-degree ns unique j w =
    cong (degree 1) (funExt λ x →
      cong (petalProjection ns j ∘ R.circleRec R.root (R.roseWord ns w))
        (circle-section x))
    ∙ projected-recursor-degree ns j w
    ∙ projected-word-winding ns unique j w
    ∙ cong (λ a → wordExponent a w) (sym (at-nth 0 ns j))

  -- Bounded certificate data: these prove uniqueness of the actual lists,
  -- not a topological conclusion by enumerating face words.
  initial-generators-unique : (c : ShortCase) → P.unique _≡ᵇ_ (gs c) ≡ true
  initial-generators-unique octa = refl
  initial-generators-unique icosa = refl

  actualCircleMap-degree : (c : ShortCase) (b : Bdy c) (j : Petal c)
    → degree 1 (actualCircleMap c b j) ≡ initialExponent c b j
  actualCircleMap-degree c b j = projected-word-degree (gs c)
    (initial-generators-unique c) j (Ch.faceWord (R.faceAt (S₀ c) (faceIndex c b)))

  actualProjectedCircleMap-degree : (c : ShortCase) (b : Bdy c) (j : Petal c)
    → degree 1 (actualProjectedCircleMap c b j) ≡ initialExponent c b j
  actualProjectedCircleMap-degree = actualCircleMap-degree
