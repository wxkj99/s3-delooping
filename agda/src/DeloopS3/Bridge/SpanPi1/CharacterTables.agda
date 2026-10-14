{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.CharacterTables where

-- A small expression adapter, with explicit validation of EVERY subterm.
-- Certificate composition is converted by certificatePermutation-compose,
-- never treated as literal symmetric-group composition in the wrong order.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (Bool; true; _and_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.Enumerated using (certificate-cong)
import DeloopS3.Cert.Perm as P

data Term : Type₀ where
  X Y : Term
  _⊗_ : Term → Term → Term
  inverse : Term → Term

infixl 30 _⊗_

eval : (G : Group₀) → fst G → fst G → Term → fst G
eval G x y X = x
eval G x y Y = y
eval G x y (u ⊗ v) = GroupStr._·_ (snd G) (eval G x y u) (eval G x y v)
eval G x y (inverse u) = GroupStr.inv (snd G) (eval G x y u)

tableEval : P.Table → P.Table → Term → P.Table
tableEval a b X = a
tableEval a b Y = b
tableEval a b (u ⊗ v) = P.compose (tableEval a b u) (tableEval a b v)
tableEval a b (inverse u) = P.inverse (tableEval a b u)

validTerm : ℕ → P.Table → P.Table → Term → Bool
validTerm n a b X = P.isPerm n a
validTerm n a b Y = P.isPerm n b
validTerm n a b (u ⊗ v) = P.isPerm n (tableEval a b (u ⊗ v))
  and (validTerm n a b u and validTerm n a b v)
validTerm n a b (inverse u) = P.isPerm n (tableEval a b (inverse u)) and validTerm n a b u

valid-result : (n : ℕ) (a b : P.Table) (w : Term) → validTerm n a b w ≡ true
  → P.isPerm n (tableEval a b w) ≡ true
valid-result n a b X p = p
valid-result n a b Y p = p
valid-result n a b (u ⊗ v) p = and-left p
valid-result n a b (inverse u) p = and-left p

abstract
  hom-eval : {G H : Group₀} (f : GroupHom G H) (x y : fst G) (w : Term)
    → fst f (eval G x y w) ≡ eval H (fst f x) (fst f y) w
  hom-eval f x y X = refl
  hom-eval f x y Y = refl
  hom-eval {H = H} f x y (u ⊗ v) = IsGroupHom.pres· (snd f) _ _
    ∙ cong₂ (GroupStr._·_ (snd H)) (hom-eval f x y u) (hom-eval f x y v)
  hom-eval {H = H} f x y (inverse u) = IsGroupHom.presinv (snd f) _
    ∙ cong (GroupStr.inv (snd H)) (hom-eval f x y u)

  table-eval-sound : (n : ℕ) (a b : P.Table)
    (va : P.isPerm n a ≡ true) (vb : P.isPerm n b ≡ true)
    (w : Term) (ok : validTerm n a b w ≡ true)
    → eval (FinSymGroup n) (certificatePermutation {t = a} va) (certificatePermutation {t = b} vb) w
      ≡ certificatePermutation {t = tableEval a b w} (valid-result n a b w ok)
  table-eval-sound n a b va vb X ok = certificate-cong a a va ok refl
  table-eval-sound n a b va vb Y ok = certificate-cong b b vb ok refl
  table-eval-sound n a b va vb (u ⊗ v) ok =
    cong₂ compEquiv
      (table-eval-sound n a b va vb u okU)
      (table-eval-sound n a b va vb v okV)
    ∙ sym (certificatePermutation-compose (tableEval a b u) (tableEval a b v)
      (valid-result n a b u okU) (valid-result n a b v okV) (and-left ok))
    where
    children : validTerm n a b u and validTerm n a b v ≡ true
    children = and-right {a = P.isPerm n (tableEval a b (u ⊗ v))} ok
    okU : validTerm n a b u ≡ true
    okU = and-left children
    okV : validTerm n a b v ≡ true
    okV = and-right {a = validTerm n a b u} children
  table-eval-sound n a b va vb (inverse u) ok =
    cong invEquiv (table-eval-sound n a b va vb u (and-right ok))
    ∙ sym (certificatePermutation-inverse (tableEval a b u)
      (valid-result n a b u (and-right ok)) (and-left ok))

  interpreted-table : {G : Group₀} (n : ℕ) (f : GroupHom G (FinSymGroup n))
    (x y : fst G) (a b : P.Table)
    (va : P.isPerm n a ≡ true) (vb : P.isPerm n b ≡ true)
    → fst f x ≡ certificatePermutation {t = a} va
    → fst f y ≡ certificatePermutation {t = b} vb
    → (w : Term) (ok : validTerm n a b w ≡ true)
    → (t : P.Table) (vt : P.isPerm n t ≡ true)
    → P.tableEq (tableEval a b w) t ≡ true
    → fst f (eval G x y w) ≡ certificatePermutation {t = t} vt
  interpreted-table n f x y a b va vb px py w ok t vt hit = hom-eval f x y w
    ∙ cong₂ (λ x y → eval (FinSymGroup n) x y w) px py
    ∙ table-eval-sound n a b va vb w ok
    ∙ certificate-cong (tableEval a b w) t (valid-result n a b w ok) vt
      (tableEq-sound _ _ hit)
