{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Sheets.Action where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (true)
open import Cubical.Data.SumFin using (toℕ; toℕ-injective)
open import Cubical.Algebra.Group.Base using (GroupStr)
open import Cubical.Algebra.Group.Morphisms using (IsGroupHom)
open import DeloopS3.Cover.Cosets using (hom)
open import DeloopS3.Cert.Input.Model.Vocabulary
open import DeloopS3.Cert.Input.Model.Finite using (repTable; repTable-valid; repElement-table)
open import DeloopS3.Cert.Input.Model.Groups using
  (ambient; ambientHom; ambient-injective; genTable-valid; genElement-table)
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.TableAlgebra using (compose-valid; inverse-valid)
open import DeloopS3.Groups.Enumerated using (certificate-cong)
open import DeloopS3.Cert.Input.Sheets.ActionFinite
import DeloopS3.Groups.Concrete as C
import DeloopS3.Groups.Identification as ID
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Short as Short

abstract
  letter-valid : (c : ShortCase) (t : BaseLetter)
    → P.isPerm (Ch.degree (certOf c)) (letterTable c t) ≡ true
  letter-valid c a+ = genTable-valid c Ch.A
  letter-valid c b+ = genTable-valid c Ch.B
  letter-valid c a- = inverse-valid (letterTable c a+) (genTable-valid c Ch.A)
  letter-valid c b- = inverse-valid (letterTable c b+) (genTable-valid c Ch.B)

letterCertificate : (c : ShortCase) → BaseLetter → ambient c .fst
letterCertificate octa t = certificatePermutation {t = letterTable octa t} (letter-valid octa t)
letterCertificate icosa t = certificatePermutation {t = letterTable icosa t} (letter-valid icosa t)

abstract
  letter-decode : (c : ShortCase) (t : BaseLetter)
    → ambientHom c .fst (letterElement c t) ≡ letterCertificate c t
  letter-decode octa a+ = genElement-table octa Ch.A
    ∙ certificate-cong _ _ (genTable-valid octa Ch.A) (letter-valid octa a+) refl
  letter-decode octa b+ = genElement-table octa Ch.B
    ∙ certificate-cong _ _ (genTable-valid octa Ch.B) (letter-valid octa b+) refl
  letter-decode icosa a+ = genElement-table icosa Ch.A
    ∙ certificate-cong _ _ (genTable-valid icosa Ch.A) (letter-valid icosa a+) refl
  letter-decode icosa b+ = genElement-table icosa Ch.B
    ∙ certificate-cong _ _ (genTable-valid icosa Ch.B) (letter-valid icosa b+) refl
  letter-decode octa a- = IsGroupHom.presinv (ambientHom octa .snd) (letterElement octa a+)
    ∙ cong invEquiv (letter-decode octa a+)
    ∙ sym (certificatePermutation-inverse (letterTable octa a+) (letter-valid octa a+) (letter-valid octa a-))
  letter-decode octa b- = IsGroupHom.presinv (ambientHom octa .snd) (letterElement octa b+)
    ∙ cong invEquiv (letter-decode octa b+)
    ∙ sym (certificatePermutation-inverse (letterTable octa b+) (letter-valid octa b+) (letter-valid octa b-))
  letter-decode icosa a- = IsGroupHom.presinv (ambientHom icosa .snd) (letterElement icosa a+)
    ∙ cong invEquiv (letter-decode icosa a+)
    ∙ sym (certificatePermutation-inverse (letterTable icosa a+) (letter-valid icosa a+) (letter-valid icosa a-))
  letter-decode icosa b- = IsGroupHom.presinv (ambientHom icosa .snd) (letterElement icosa b+)
    ∙ cong invEquiv (letter-decode icosa b+)
    ∙ sym (certificatePermutation-inverse (letterTable icosa b+) (letter-valid icosa b+) (letter-valid icosa b-))

  decoded-products : {n : ℕ} (p q r s : P.Table)
    (vp : P.isPerm n p ≡ true) (vq : P.isPerm n q ≡ true)
    (vr : P.isPerm n r ≡ true) (vs : P.isPerm n s ≡ true)
    → P.compose p q ≡ P.compose r s
    → compEquiv (certificatePermutation {t = p} vp) (certificatePermutation {t = q} vq)
      ≡ compEquiv (certificatePermutation {t = r} vr) (certificatePermutation {t = s} vs)
  decoded-products p q r s vp vq vr vs eq =
    sym (certificatePermutation-compose p q vp vq (compose-valid p q vp vq))
    ∙ certificate-cong (P.compose p q) (P.compose r s)
      (compose-valid p q vp vq) (compose-valid r s vr vs) eq
    ∙ certificatePermutation-compose r s vr vs (compose-valid r s vr vs)

  act-value : (c : ShortCase) (i : Sh c) (t : BaseLetter)
    → toℕ (actFin (certOf c) (rawChecks c) t i) ≡ P.apply (actionTable c t) (toℕ i)
  act-value c i t = tablePermutation-value {t = actionTable c t}
    (and-left (Short.action-checked (certOf c) (rawChecks c) t)) i

  target-octa : (i : Sh octa) (t : BaseLetter)
    → OA.target t i ≡ actFin (certOf octa) (rawChecks octa) t i
  target-octa i t = toℕ-injective (OAC.target-value i t ∙ sym (act-value octa i t))

  target-icosa : (i : Sh icosa) (t : BaseLetter)
    → IA.target t i ≡ actFin (certOf icosa) (rawChecks icosa) t i
  target-icosa i t = toℕ-injective (IAC.target-value i t ∙ sym (act-value icosa i t))

  action-witness : (c : ShortCase) (i : Sh c) (t : BaseLetter)
    → Σ[ h ∈ H c .fst ]
        GroupStr._·_ (Δ c .snd) (hom (j c) .fst h)
          (repElement c (actFin (certOf c) (rawChecks c) t i))
        ≡ GroupStr._·_ (Δ c .snd) (repElement c i) (letterElement c t)
  action-witness octa i t = h ,
    (cong (λ k → GroupStr._·_ (Δ octa .snd) (hom (j octa) .fst h) (repElement octa k))
        (sym (target-octa i t))
    ∙ cong (compEquiv (C.D₈-tables.embed h)) (repElement-table octa (OA.target t i))
    ∙ decoded-products (C.D₈-tables.table h) (repTable octa (OA.target t i))
        (repTable octa i) (letterTable octa t)
        (C.D₈-tables.valid h) (repTable-valid octa (OA.target t i))
        (repTable-valid octa i) (letter-valid octa t) (OAC.product i t)
    ∙ sym (cong₂ compEquiv (repElement-table octa i) (letter-decode octa t)))
    where
    h : H octa .fst
    h = OA.witness i t
  action-witness icosa i t = h ,
    (cong (λ k → GroupStr._·_ (Δ icosa .snd) (hom (j icosa) .fst h) (repElement icosa k))
        (sym (target-icosa i t))
    ∙ ambient-injective icosa
      (IsGroupHom.pres· (ambientHom icosa .snd) (hom (j icosa) .fst h) (repElement icosa (IA.target t i))
      ∙ cong₂ compEquiv (ID.D₆-inclusion.commutes h) (repElement-table icosa (IA.target t i))
      ∙ decoded-products (C.D₆-tables.table h) (repTable icosa (IA.target t i))
          (repTable icosa i) (letterTable icosa t)
          (C.D₆-tables.valid h) (repTable-valid icosa (IA.target t i))
          (repTable-valid icosa i) (letter-valid icosa t) (IAC.product i t)
      ∙ sym (IsGroupHom.pres· (ambientHom icosa .snd) (repElement icosa i) (letterElement icosa t)
          ∙ cong₂ compEquiv (repElement-table icosa i) (letter-decode icosa t))))
    where
    h : H icosa .fst
    h = IA.witness i t
