{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Sheets.ActionFinite where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; _≡ᵇ_)
open import Cubical.Data.Bool using (Bool; true; _and_)
open import Cubical.Data.SumFin using (Fin; fzero; toℕ)
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.FiniteReflection
open import DeloopS3.Cert.Input.Model.Vocabulary
open import DeloopS3.Cert.Input.Model.Finite using (repTable)
open import DeloopS3.Cert.Input.Sheets.Finite
open import DeloopS3.Cert.Input.Sheets.NormalForm using (module O; module I)
import DeloopS3.Groups.Concrete as C
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P

letterTable : ShortCase → BaseLetter → P.Table
letterTable c t = P.letterImage (Ch.baseGenerators (certOf c)) (wireLetter t)

actionTable : ShortCase → BaseLetter → P.Table
actionTable c t = Ch.actTable (Ch.action (certOf c)) (wireLetter t)

module SignedLookup (nh ns : ℕ)
  (hTable : Fin nh → P.Table) (rTable : Fin ns → P.Table)
  (hFind : P.Table → Fin nh) (s₀ : Fin ns)
  (letters actions : BaseLetter → P.Table) where

  target : (t : BaseLetter) → Fin ns → Fin ns
  target t i = search (λ k → toℕ k ≡ᵇ P.apply (actions t) (toℕ i))
    (sample ns (λ k → k)) s₀

  witness : Fin ns → BaseLetter → Fin nh
  witness i t = hFind (P.compose (rTable i) (letters t))

  left right : Fin ns → BaseLetter → P.Table
  left i t = P.compose (hTable (witness i t)) (rTable (target t i))
  right i t = P.compose (rTable i) (letters t)

  targetB productB checkAt : Fin ns → BaseLetter → Bool
  targetB i t = toℕ (target t i) ≡ᵇ P.apply (actions t) (toℕ i)
  productB i t = P.tableEq (left i t) (right i t)
  checkAt i t = targetB i t and productB i t

  check : BaseLetter → Bool
  check t = allFin (λ i → checkAt i t)

  module Checked (ok : (t : BaseLetter) → check t ≡ true) where
    abstract
      at-ok : (i : Fin ns) (t : BaseLetter) → checkAt i t ≡ true
      at-ok i t = allFin-sound (λ i → checkAt i t) (ok t) i

      target-value : (i : Fin ns) (t : BaseLetter)
        → toℕ (target t i) ≡ P.apply (actions t) (toℕ i)
      target-value i t = natEq-sound _ _
        (and-left {a = targetB i t} {b = productB i t} (at-ok i t))

      product : (i : Fin ns) (t : BaseLetter) → left i t ≡ right i t
      product i t = tableEq-sound _ _
        (and-right {a = targetB i t} {b = productB i t} (at-ok i t))

module OA = SignedLookup 8 3 C.D₈-tables.table (repTable octa)
  (λ t → O.backward (O.findGroup t) .fst) fzero (letterTable octa) (actionTable octa)
module IA = SignedLookup 6 10 C.D₆-tables.table (repTable icosa)
  (λ t → I.backward (I.findGroup t) .fst) fzero (letterTable icosa) (actionTable icosa)

-- Only 12/40 signed transitions: all assertions stay at the table level.
abstract
  octa-actions : (t : BaseLetter) → OA.check t ≡ true
  octa-actions a+ = refl
  octa-actions a- = refl
  octa-actions b+ = refl
  octa-actions b- = refl
  icosa-actions : (t : BaseLetter) → IA.check t ≡ true
  icosa-actions a+ = refl
  icosa-actions a- = refl
  icosa-actions b+ = refl
  icosa-actions b- = refl

module OAC = OA.Checked octa-actions
module IAC = IA.Checked icosa-actions
