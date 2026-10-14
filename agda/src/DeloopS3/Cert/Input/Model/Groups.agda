{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Model.Groups where

-- Small semantic equations: proofs compute on four/five points, NEVER
-- by normalizing the opaque 24/60-element closure certificates.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (true)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc; toℕ; toℕ-injective)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·)
open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Octa3 as O
import DeloopS3.Cert.Icosa10 as I
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Groups.Concrete as Concrete
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.Enumerated using (certificate-cong)
open import DeloopS3.Cert.Input.Model.Vocabulary

abstract
  decode-permutation : {n : ℕ} (p : P.Table) (v : P.isPerm n p ≡ true)
    (e : Fin n ≃ Fin n)
    → ((i : Fin n) → toℕ (invEq e i) ≡ P.apply p (toℕ i))
    → certificatePermutation {t = p} v ≡ e
  decode-permutation {n} p v e values = cong invEquiv
    (equivEq (funExt λ i → toℕ-injective
      (tablePermutation-value {t = p} v i ∙ sym (values i))))
    ∙ GroupTheory.invInv (FinSymGroup n) e

aO : Fin 4 ≃ Fin 4
aO = isoToEquiv (iso forward backward sec ret)
  where
  forward backward : Fin 4 → Fin 4
  forward fzero = (fsuc fzero)
  forward (fsuc fzero) = fzero
  forward (fsuc (fsuc fzero)) = (fsuc (fsuc fzero))
  forward (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc (fsuc fzero)))
  forward (fsuc (fsuc (fsuc (fsuc ()))))
  backward fzero = (fsuc fzero)
  backward (fsuc fzero) = fzero
  backward (fsuc (fsuc fzero)) = (fsuc (fsuc fzero))
  backward (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc (fsuc fzero)))
  backward (fsuc (fsuc (fsuc (fsuc ()))))
  sec : (i : Fin 4) → forward (backward i) ≡ i
  sec fzero = refl
  sec (fsuc fzero) = refl
  sec (fsuc (fsuc fzero)) = refl
  sec (fsuc (fsuc (fsuc fzero))) = refl
  sec (fsuc (fsuc (fsuc (fsuc ()))))
  ret : (i : Fin 4) → backward (forward i) ≡ i
  ret fzero = refl
  ret (fsuc fzero) = refl
  ret (fsuc (fsuc fzero)) = refl
  ret (fsuc (fsuc (fsuc fzero))) = refl
  ret (fsuc (fsuc (fsuc (fsuc ()))))

abstract
  aO-decode : certificatePermutation {t = Ch.a O.cert} refl ≡ aO
  aO-decode = decode-permutation _ refl aO values
    where
    values : (i : Fin 4) → toℕ (invEq aO i) ≡ P.apply (Ch.a O.cert) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))

bO : Fin 4 ≃ Fin 4
bO = isoToEquiv (iso forward backward sec ret)
  where
  forward backward : Fin 4 → Fin 4
  forward fzero = fzero
  forward (fsuc fzero) = (fsuc (fsuc (fsuc fzero)))
  forward (fsuc (fsuc fzero)) = (fsuc fzero)
  forward (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc fzero))
  forward (fsuc (fsuc (fsuc (fsuc ()))))
  backward fzero = fzero
  backward (fsuc fzero) = (fsuc (fsuc fzero))
  backward (fsuc (fsuc fzero)) = (fsuc (fsuc (fsuc fzero)))
  backward (fsuc (fsuc (fsuc fzero))) = (fsuc fzero)
  backward (fsuc (fsuc (fsuc (fsuc ()))))
  sec : (i : Fin 4) → forward (backward i) ≡ i
  sec fzero = refl
  sec (fsuc fzero) = refl
  sec (fsuc (fsuc fzero)) = refl
  sec (fsuc (fsuc (fsuc fzero))) = refl
  sec (fsuc (fsuc (fsuc (fsuc ()))))
  ret : (i : Fin 4) → backward (forward i) ≡ i
  ret fzero = refl
  ret (fsuc fzero) = refl
  ret (fsuc (fsuc fzero)) = refl
  ret (fsuc (fsuc (fsuc fzero))) = refl
  ret (fsuc (fsuc (fsuc (fsuc ()))))

abstract
  bO-decode : certificatePermutation {t = Ch.b O.cert} refl ≡ bO
  bO-decode = decode-permutation _ refl bO values
    where
    values : (i : Fin 4) → toℕ (invEq bO i) ≡ P.apply (Ch.b O.cert) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))

aI : Fin 5 ≃ Fin 5
aI = isoToEquiv (iso forward backward sec ret)
  where
  forward backward : Fin 5 → Fin 5
  forward fzero = (fsuc fzero)
  forward (fsuc fzero) = fzero
  forward (fsuc (fsuc fzero)) = (fsuc (fsuc (fsuc fzero)))
  forward (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc fzero))
  forward (fsuc (fsuc (fsuc (fsuc fzero)))) = (fsuc (fsuc (fsuc (fsuc fzero))))
  forward (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  backward fzero = (fsuc fzero)
  backward (fsuc fzero) = fzero
  backward (fsuc (fsuc fzero)) = (fsuc (fsuc (fsuc fzero)))
  backward (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc fzero))
  backward (fsuc (fsuc (fsuc (fsuc fzero)))) = (fsuc (fsuc (fsuc (fsuc fzero))))
  backward (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  sec : (i : Fin 5) → forward (backward i) ≡ i
  sec fzero = refl
  sec (fsuc fzero) = refl
  sec (fsuc (fsuc fzero)) = refl
  sec (fsuc (fsuc (fsuc fzero))) = refl
  sec (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  ret : (i : Fin 5) → backward (forward i) ≡ i
  ret fzero = refl
  ret (fsuc fzero) = refl
  ret (fsuc (fsuc fzero)) = refl
  ret (fsuc (fsuc (fsuc fzero))) = refl
  ret (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  ret (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

abstract
  aI-decode : certificatePermutation {t = Ch.a I.cert} refl ≡ aI
  aI-decode = decode-permutation _ refl aI values
    where
    values : (i : Fin 5) → toℕ (invEq aI i) ≡ P.apply (Ch.a I.cert) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

bI : Fin 5 ≃ Fin 5
bI = isoToEquiv (iso forward backward sec ret)
  where
  forward backward : Fin 5 → Fin 5
  forward fzero = fzero
  forward (fsuc fzero) = (fsuc (fsuc (fsuc (fsuc fzero))))
  forward (fsuc (fsuc fzero)) = (fsuc fzero)
  forward (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc (fsuc fzero)))
  forward (fsuc (fsuc (fsuc (fsuc fzero)))) = (fsuc (fsuc fzero))
  forward (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  backward fzero = fzero
  backward (fsuc fzero) = (fsuc (fsuc fzero))
  backward (fsuc (fsuc fzero)) = (fsuc (fsuc (fsuc (fsuc fzero))))
  backward (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc (fsuc fzero)))
  backward (fsuc (fsuc (fsuc (fsuc fzero)))) = (fsuc fzero)
  backward (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  sec : (i : Fin 5) → forward (backward i) ≡ i
  sec fzero = refl
  sec (fsuc fzero) = refl
  sec (fsuc (fsuc fzero)) = refl
  sec (fsuc (fsuc (fsuc fzero))) = refl
  sec (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  sec (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  ret : (i : Fin 5) → backward (forward i) ≡ i
  ret fzero = refl
  ret (fsuc fzero) = refl
  ret (fsuc (fsuc fzero)) = refl
  ret (fsuc (fsuc (fsuc fzero))) = refl
  ret (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  ret (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

abstract
  bI-decode : certificatePermutation {t = Ch.b I.cert} refl ≡ bI
  bI-decode = decode-permutation _ refl bI values
    where
    values : (i : Fin 5) → toℕ (invEq bI i) ≡ P.apply (Ch.b I.cert) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

ambient : ShortCase → Group₀
ambient octa = FinSymGroup 4
ambient icosa = FinSymGroup 5
ambientHom : (c : ShortCase) → GroupHom (Δ c) (ambient c)
ambientHom octa = idGroupHom
ambientHom icosa = Concrete.A₅→S₅
abstract
  ambient-injective : (c : ShortCase) {x y : Δ c .fst}
    → ambientHom c .fst x ≡ ambientHom c .fst y → x ≡ y
  ambient-injective octa p = p
  ambient-injective icosa p = Concrete.A₅-tables.embed-injective p

ambientA ambientB : (c : ShortCase) → ambient c .fst
ambientA octa = aO
ambientA icosa = aI
ambientB octa = bO
ambientB icosa = bI
ambientGen : (c : ShortCase) → Ch.Kind → ambient c .fst
ambientGen c Ch.A = ambientA c
ambientGen c Ch.B = ambientB c
ambientGen c Ch.C = GroupStr.inv (ambient c .snd)
  (GroupStr._·_ (ambient c .snd) (ambientA c) (ambientB c))

abstract
  ambient-a : (c : ShortCase) → ambientHom c .fst (letterElement c a+) ≡ ambientA c
  ambient-a octa = Short.generator-a-octa ∙ aO-decode
  ambient-a icosa = certificate-cong
    (Concrete.A₅-tables.table (Short.generator-a icosa)) (Ch.a I.cert)
    (Concrete.A₅-tables.valid (Short.generator-a icosa)) refl
    Short.generator-a-icosa ∙ aI-decode
  ambient-b : (c : ShortCase) → ambientHom c .fst (letterElement c b+) ≡ ambientB c
  ambient-b octa = Short.generator-b-octa ∙ bO-decode
  ambient-b icosa = certificate-cong
    (Concrete.A₅-tables.table (Short.generator-b icosa)) (Ch.b I.cert)
    (Concrete.A₅-tables.valid (Short.generator-b icosa)) refl
    Short.generator-b-icosa ∙ bI-decode
  ambient-gen : (c : ShortCase) (k : Ch.Kind)
    → ambientHom c .fst (genElement c k) ≡ ambientGen c k
  ambient-gen c Ch.A = ambient-a c
  ambient-gen c Ch.B = ambient-b c
  ambient-gen c Ch.C = IsGroupHom.presinv (ambientHom c .snd) _
    ∙ cong (GroupStr.inv (ambient c .snd))
      (IsGroupHom.pres· (ambientHom c .snd) _ _
       ∙ cong₂ (GroupStr._·_ (ambient c .snd)) (ambient-a c) (ambient-b c))

  ambient-order : (c : ShortCase) (k : Ch.Kind)
    → (Z.pos (localOrder c k) ℤ[ ambient c ]· ambientGen c k)
      ≡ GroupStr.1g (ambient c .snd)
  ambient-order octa Ch.A = equivEq (funExt values)
    where
    values : (i : Fin 4) → (Z.pos (localOrder octa Ch.A) ℤ[ ambient octa ]· ambientGen octa Ch.A) .fst i ≡ i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))
  ambient-order octa Ch.B = equivEq (funExt values)
    where
    values : (i : Fin 4) → (Z.pos (localOrder octa Ch.B) ℤ[ ambient octa ]· ambientGen octa Ch.B) .fst i ≡ i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))
  ambient-order octa Ch.C = equivEq (funExt values)
    where
    values : (i : Fin 4) → (Z.pos (localOrder octa Ch.C) ℤ[ ambient octa ]· ambientGen octa Ch.C) .fst i ≡ i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))
  ambient-order icosa Ch.A = equivEq (funExt values)
    where
    values : (i : Fin 5) → (Z.pos (localOrder icosa Ch.A) ℤ[ ambient icosa ]· ambientGen icosa Ch.A) .fst i ≡ i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  ambient-order icosa Ch.B = equivEq (funExt values)
    where
    values : (i : Fin 5) → (Z.pos (localOrder icosa Ch.B) ℤ[ ambient icosa ]· ambientGen icosa Ch.B) .fst i ≡ i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  ambient-order icosa Ch.C = equivEq (funExt values)
    where
    values : (i : Fin 5) → (Z.pos (localOrder icosa Ch.C) ℤ[ ambient icosa ]· ambientGen icosa Ch.C) .fst i ≡ i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

  ambient-weight : (c : ShortCase) (k : Ch.Kind)
    → (localWeight c k ℤ[ ambient c ]· ambientGen c k) ≡ ambientGen c k
  ambient-weight octa Ch.A = equivEq (funExt values)
    where
    values : (i : Fin 4) → (localWeight octa Ch.A ℤ[ ambient octa ]· ambientGen octa Ch.A) .fst i ≡ ambientGen octa Ch.A .fst i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))
  ambient-weight octa Ch.B = equivEq (funExt values)
    where
    values : (i : Fin 4) → (localWeight octa Ch.B ℤ[ ambient octa ]· ambientGen octa Ch.B) .fst i ≡ ambientGen octa Ch.B .fst i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))
  ambient-weight octa Ch.C = equivEq (funExt values)
    where
    values : (i : Fin 4) → (localWeight octa Ch.C ℤ[ ambient octa ]· ambientGen octa Ch.C) .fst i ≡ ambientGen octa Ch.C .fst i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))
  ambient-weight icosa Ch.A = equivEq (funExt values)
    where
    values : (i : Fin 5) → (localWeight icosa Ch.A ℤ[ ambient icosa ]· ambientGen icosa Ch.A) .fst i ≡ ambientGen icosa Ch.A .fst i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  ambient-weight icosa Ch.B = equivEq (funExt values)
    where
    values : (i : Fin 5) → (localWeight icosa Ch.B ℤ[ ambient icosa ]· ambientGen icosa Ch.B) .fst i ≡ ambientGen icosa Ch.B .fst i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  ambient-weight icosa Ch.C = equivEq (funExt values)
    where
    values : (i : Fin 5) → (localWeight icosa Ch.C ℤ[ ambient icosa ]· ambientGen icosa Ch.C) .fst i ≡ ambientGen icosa Ch.C .fst i
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

  gen-order : (c : ShortCase) (k : Ch.Kind)
    → (Z.pos (localOrder c k) ℤ[ Δ c ]· genElement c k) ≡ GroupStr.1g (Δ c .snd)
  gen-order c k = ambient-injective c
    (homPresℤ· (ambientHom c) (genElement c k) (Z.pos (localOrder c k))
     ∙ cong (Z.pos (localOrder c k) ℤ[ ambient c ]·_) (ambient-gen c k)
     ∙ ambient-order c k ∙ sym (IsGroupHom.pres1 (ambientHom c .snd)))
  gen-weight : (c : ShortCase) (k : Ch.Kind)
    → (localWeight c k ℤ[ Δ c ]· genElement c k) ≡ genElement c k
  gen-weight c k = ambient-injective c
    (homPresℤ· (ambientHom c) (genElement c k) (localWeight c k)
     ∙ cong (localWeight c k ℤ[ ambient c ]·_) (ambient-gen c k)
     ∙ ambient-weight c k ∙ sym (ambient-gen c k))
  gen-product : (c : ShortCase) → genElement c Ch.C ≡ GroupStr.inv (Δ c .snd)
    (GroupStr._·_ (Δ c .snd) (genElement c Ch.A) (genElement c Ch.B))
  gen-product c = refl
  gen-c-inverses : (c : ShortCase) → genElement c Ch.C ≡
    GroupStr._·_ (Δ c .snd) (letterElement c b-) (letterElement c a-)
  gen-c-inverses c = GroupTheory.invDistr (Δ c) (genElement c Ch.A) (genElement c Ch.B)

abstract
  genTable-valid : (c : ShortCase) (k : Ch.Kind)
    → P.isPerm (Ch.degree (certOf c)) (Ch.kindGenerator (certOf c) k) ≡ true
  genTable-valid octa Ch.A = refl
  genTable-valid octa Ch.B = refl
  genTable-valid octa Ch.C = refl
  genTable-valid icosa Ch.A = refl
  genTable-valid icosa Ch.B = refl
  genTable-valid icosa Ch.C = refl

  ambientGen-table-octa : (k : Ch.Kind) → ambientGen octa k
    ≡ certificatePermutation {t = Ch.kindGenerator (certOf octa) k} (genTable-valid octa k)
  ambientGen-table-octa Ch.A = sym (decode-permutation _ (genTable-valid octa Ch.A) (ambientGen octa Ch.A) values)
    where
    values : (i : Fin 4) → toℕ (invEq (ambientGen octa Ch.A) i) ≡ P.apply (Ch.kindGenerator (certOf octa) Ch.A) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))
  ambientGen-table-octa Ch.B = sym (decode-permutation _ (genTable-valid octa Ch.B) (ambientGen octa Ch.B) values)
    where
    values : (i : Fin 4) → toℕ (invEq (ambientGen octa Ch.B) i) ≡ P.apply (Ch.kindGenerator (certOf octa) Ch.B) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))
  ambientGen-table-octa Ch.C = sym (decode-permutation _ (genTable-valid octa Ch.C) (ambientGen octa Ch.C) values)
    where
    values : (i : Fin 4) → toℕ (invEq (ambientGen octa Ch.C) i) ≡ P.apply (Ch.kindGenerator (certOf octa) Ch.C) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc ()))))
  ambientGen-table-icosa : (k : Ch.Kind) → ambientGen icosa k
    ≡ certificatePermutation {t = Ch.kindGenerator (certOf icosa) k} (genTable-valid icosa k)
  ambientGen-table-icosa Ch.A = sym (decode-permutation _ (genTable-valid icosa Ch.A) (ambientGen icosa Ch.A) values)
    where
    values : (i : Fin 5) → toℕ (invEq (ambientGen icosa Ch.A) i) ≡ P.apply (Ch.kindGenerator (certOf icosa) Ch.A) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  ambientGen-table-icosa Ch.B = sym (decode-permutation _ (genTable-valid icosa Ch.B) (ambientGen icosa Ch.B) values)
    where
    values : (i : Fin 5) → toℕ (invEq (ambientGen icosa Ch.B) i) ≡ P.apply (Ch.kindGenerator (certOf icosa) Ch.B) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  ambientGen-table-icosa Ch.C = sym (decode-permutation _ (genTable-valid icosa Ch.C) (ambientGen icosa Ch.C) values)
    where
    values : (i : Fin 5) → toℕ (invEq (ambientGen icosa Ch.C) i) ≡ P.apply (Ch.kindGenerator (certOf icosa) Ch.C) (toℕ i)
    values fzero = refl
    values (fsuc fzero) = refl
    values (fsuc (fsuc fzero)) = refl
    values (fsuc (fsuc (fsuc fzero))) = refl
    values (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
    values (fsuc (fsuc (fsuc (fsuc (fsuc ())))))

certificateGen : (c : ShortCase) → Ch.Kind → ambient c .fst
certificateGen octa k = certificatePermutation {t = Ch.kindGenerator (certOf octa) k} (genTable-valid octa k)
certificateGen icosa k = certificatePermutation {t = Ch.kindGenerator (certOf icosa) k} (genTable-valid icosa k)
abstract
  genElement-table : (c : ShortCase) (k : Ch.Kind)
    → ambientHom c .fst (genElement c k) ≡ certificateGen c k
  genElement-table octa k = ambient-gen octa k ∙ ambientGen-table-octa k
  genElement-table icosa k = ambient-gen icosa k ∙ ambientGen-table-icosa k
