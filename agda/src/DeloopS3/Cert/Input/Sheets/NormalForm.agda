{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Sheets.NormalForm where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (true)
open import Cubical.Data.SumFin using (Fin; fzero)
open import Cubical.Algebra.Group.Base using (GroupStr)
open import Cubical.Algebra.Group.Morphisms using (IsGroupHom)
open import DeloopS3.Cover.Cosets using (hom)
open import DeloopS3.Cert.Input.Model.Vocabulary
open import DeloopS3.Cert.Input.Model.Finite using (repTable; repTable-valid; repElement-table)
open import DeloopS3.Cert.Input.Model.Groups using (ambient; ambientHom; ambient-injective)
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.TableAlgebra using (compose-valid)
open import DeloopS3.Groups.Enumerated using (certificate-cong)
import DeloopS3.Groups.Concrete as C
import DeloopS3.Groups.Identification as ID
import DeloopS3.Cert.Perm as P
open import DeloopS3.Cert.Input.Sheets.Finite

module O = Lookup 8 3 24 C.D₈-tables.table (repTable octa) C.S₄-tables.table fzero fzero fzero
module I = Lookup 6 10 60 C.D₆-tables.table (repTable icosa) C.A₅-tables.table fzero fzero fzero

abstract
  octa-ret : O.retCheck ≡ true
  octa-ret = refl
  octa-sec : O.secCheck ≡ true
  octa-sec = refl
  icosa-ret : I.retCheck ≡ true
  icosa-ret = refl
  icosa-sec : I.secCheck ≡ true
  icosa-sec = refl

module OC = O.Checked octa-ret octa-sec
module IC = I.Checked icosa-ret icosa-sec

-- Generic semantic reflection of a table product, not group reduction.
abstract
  decode-product : {n : ℕ} (p q r : P.Table)
    (vp : P.isPerm n p ≡ true) (vq : P.isPerm n q ≡ true)
    (vr : P.isPerm n r ≡ true) → r ≡ P.compose p q
    → certificatePermutation {t = r} vr
      ≡ compEquiv (certificatePermutation {t = p} vp) (certificatePermutation {t = q} vq)
  decode-product p q r vp vq vr eq = certificate-cong r (P.compose p q) vr
    (compose-valid p q vp vq) eq
    ∙ certificatePermutation-compose p q vp vq (compose-valid p q vp vq)

pack : (c : ShortCase) → H c .fst × Sh c → Δ c .fst
pack c (h , i) = GroupStr._·_ (Δ c .snd) (hom (j c) .fst h) (repElement c i)

rawNormalForm : (c : ShortCase) → (H c .fst × Sh c) ≃ Δ c .fst
rawNormalForm octa = compEquiv OC.equivalence (isoToEquiv (ID.S₄-tables≅S₄ .fst))
rawNormalForm icosa = IC.equivalence

abstract
  rawNormalForm-pack : (c : ShortCase) (x : H c .fst × Sh c)
    → equivFun (rawNormalForm c) x ≡ pack c x
  rawNormalForm-pack octa (h , i) =
    decode-product (C.D₈-tables.table h) (repTable octa i) (C.S₄-tables.table (O.forward (h , i)))
      (C.D₈-tables.valid h) (repTable-valid octa i) (C.S₄-tables.valid (O.forward (h , i)))
      (OC.forward-table (h , i))
    ∙ cong (compEquiv (C.D₈-tables.embed h)) (sym (repElement-table octa i))
  rawNormalForm-pack icosa (h , i) = ambient-injective icosa
    (decode-product (C.D₆-tables.table h) (repTable icosa i) (C.A₅-tables.table (I.forward (h , i)))
      (C.D₆-tables.valid h) (repTable-valid icosa i) (C.A₅-tables.valid (I.forward (h , i)))
      (IC.forward-table (h , i))
    ∙ sym (IsGroupHom.pres· (ambientHom icosa .snd) (hom (j icosa) .fst h) (repElement icosa i)
      ∙ cong₂ compEquiv (ID.D₆-inclusion.commutes h) (repElement-table icosa i)))

  normalForm : (c : ShortCase) → (H c .fst × Sh c) ≃ Δ c .fst
  normalForm c = pack c , subst isEquiv (funExt (rawNormalForm-pack c)) (rawNormalForm c .snd)

  normalForm-pack : (c : ShortCase) (x : H c .fst × Sh c)
    → equivFun (normalForm c) x ≡ pack c x
  normalForm-pack c x = refl
