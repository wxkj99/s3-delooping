{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Model.Finite where

-- Finite action and endpoint interfaces for the shared ShortInput record.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Bool using (true)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc; toℕ)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Groups.Concrete as Concrete
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.Enumerated using (table-cong; certificate-cong)
open import DeloopS3.Cert.Input.Model.Vocabulary
open import DeloopS3.Cert.Input.Model.Groups

abstract
  act-a-inverse : (c : ShortCase) (checked : RawChecks (certOf c))
    → actEquiv (certOf c) checked a- ≡ invEquiv (actEquiv (certOf c) checked a+)
  act-a-inverse octa checked = tablePermutation-inverse
    (Ch.actTable (Ch.action (certOf octa)) (wireLetter a+))
    (and-left (Short.action-checked (certOf octa) checked a+))
    (and-left (Short.action-checked (certOf octa) checked a-))
  act-a-inverse icosa checked = tablePermutation-inverse
    (Ch.actTable (Ch.action (certOf icosa)) (wireLetter a+))
    (and-left (Short.action-checked (certOf icosa) checked a+))
    (and-left (Short.action-checked (certOf icosa) checked a-))
  act-b-inverse : (c : ShortCase) (checked : RawChecks (certOf c))
    → actEquiv (certOf c) checked b- ≡ invEquiv (actEquiv (certOf c) checked b+)
  act-b-inverse octa checked = tablePermutation-inverse
    (Ch.actTable (Ch.action (certOf octa)) (wireLetter b+))
    (and-left (Short.action-checked (certOf octa) checked b+))
    (and-left (Short.action-checked (certOf octa) checked b-))
  act-b-inverse icosa checked = tablePermutation-inverse
    (Ch.actTable (Ch.action (certOf icosa)) (wireLetter b+))
    (and-left (Short.action-checked (certOf icosa) checked b+))
    (and-left (Short.action-checked (certOf icosa) checked b-))

  firstSheet-value : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    (ok : Ch.checkBoundary (certOf c) (bdAt c k b) ≡ true)
    → Short.firstSheet (certOf c) (bdAt c k b) ok ≡ startOf c k b
  firstSheet-value octa Ch.A fzero ok = refl
  firstSheet-value octa Ch.A (fsuc fzero) ok = refl
  firstSheet-value octa Ch.A (fsuc (fsuc ())) ok
  firstSheet-value octa Ch.B fzero ok = refl
  firstSheet-value octa Ch.B (fsuc ()) ok
  firstSheet-value octa Ch.C fzero ok = refl
  firstSheet-value octa Ch.C (fsuc fzero) ok = refl
  firstSheet-value octa Ch.C (fsuc (fsuc ())) ok
  firstSheet-value icosa Ch.A fzero ok = refl
  firstSheet-value icosa Ch.A (fsuc fzero) ok = refl
  firstSheet-value icosa Ch.A (fsuc (fsuc fzero)) ok = refl
  firstSheet-value icosa Ch.A (fsuc (fsuc (fsuc fzero))) ok = refl
  firstSheet-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) ok = refl
  firstSheet-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) ok = refl
  firstSheet-value icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))) ok
  firstSheet-value icosa Ch.B fzero ok = refl
  firstSheet-value icosa Ch.B (fsuc fzero) ok = refl
  firstSheet-value icosa Ch.B (fsuc (fsuc fzero)) ok = refl
  firstSheet-value icosa Ch.B (fsuc (fsuc (fsuc fzero))) ok = refl
  firstSheet-value icosa Ch.B (fsuc (fsuc (fsuc (fsuc ())))) ok
  firstSheet-value icosa Ch.C fzero ok = refl
  firstSheet-value icosa Ch.C (fsuc fzero) ok = refl
  firstSheet-value icosa Ch.C (fsuc (fsuc ())) ok

repTable : (c : ShortCase) → Sh c → P.Table
repTable octa = at (Ch.representatives (certOf octa))
repTable icosa = at (Ch.representatives (certOf icosa))
abstract
  repTable-valid : (c : ShortCase) (i : Sh c) → P.isPerm (Ch.degree (certOf c)) (repTable c i) ≡ true
  repTable-valid octa fzero = refl
  repTable-valid octa (fsuc fzero) = refl
  repTable-valid octa (fsuc (fsuc fzero)) = refl
  repTable-valid octa (fsuc (fsuc (fsuc ())))
  repTable-valid icosa fzero = refl
  repTable-valid icosa (fsuc fzero) = refl
  repTable-valid icosa (fsuc (fsuc fzero)) = refl
  repTable-valid icosa (fsuc (fsuc (fsuc fzero))) = refl
  repTable-valid icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  repTable-valid icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  repTable-valid icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  repTable-valid icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  repTable-valid icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  repTable-valid icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  repTable-valid icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))

ambientBase : (c : ShortCase) → ℕ → ambient c .fst
ambientBase c 1 = ambientA c
ambientBase c 2 = ambientB c
ambientBase c _ = GroupStr.1g (ambient c .snd)
ambientWord : (c : ShortCase) → P.Word → ambient c .fst
ambientWord c [] = GroupStr.1g (ambient c .snd)
ambientWord c (P.fwd n ∷ w) = GroupStr._·_ (ambient c .snd) (ambientBase c n) (ambientWord c w)
ambientWord c (P.bwd n ∷ w) = GroupStr._·_ (ambient c .snd)
  (GroupStr.inv (ambient c .snd) (ambientBase c n)) (ambientWord c w)

abstract
  ambient-base : (c : ShortCase) (n : ℕ) → ambientHom c .fst (Short.baseElement c n) ≡ ambientBase c n
  ambient-base c 0 = IsGroupHom.pres1 (ambientHom c .snd)
  ambient-base c 1 = ambient-a c
  ambient-base c 2 = ambient-b c
  ambient-base c (Cubical.Data.Nat.suc (Cubical.Data.Nat.suc (Cubical.Data.Nat.suc n))) = IsGroupHom.pres1 (ambientHom c .snd)
  ambient-word : (c : ShortCase) (w : P.Word) → ambientHom c .fst (Short.wordElement c w) ≡ ambientWord c w
  ambient-word c [] = IsGroupHom.pres1 (ambientHom c .snd)
  ambient-word c (P.fwd n ∷ w) = IsGroupHom.pres· (ambientHom c .snd) _ _
    ∙ cong₂ (GroupStr._·_ (ambient c .snd)) (ambient-base c n) (ambient-word c w)
  ambient-word c (P.bwd n ∷ w) = IsGroupHom.pres· (ambientHom c .snd) _ _
    ∙ cong₂ (GroupStr._·_ (ambient c .snd))
      (IsGroupHom.presinv (ambientHom c .snd) _ ∙ cong (GroupStr.inv (ambient c .snd)) (ambient-base c n))
      (ambient-word c w)

  rep-values-octa : (i : Sh octa) (q : Fin 4)
    → toℕ (invEq (ambientWord octa (P.nth [] (Ch.reps (certOf octa)) (toℕ i))) q)
      ≡ P.apply (repTable octa i) (toℕ q)
  rep-values-icosa : (i : Sh icosa) (q : Fin 5)
    → toℕ (invEq (ambientWord icosa (P.nth [] (Ch.reps (certOf icosa)) (toℕ i))) q)
      ≡ P.apply (repTable icosa i) (toℕ q)
  rep-values-octa fzero fzero = refl
  rep-values-octa fzero (fsuc fzero) = refl
  rep-values-octa fzero (fsuc (fsuc fzero)) = refl
  rep-values-octa fzero (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-octa fzero (fsuc (fsuc (fsuc (fsuc ()))))
  rep-values-octa (fsuc fzero) fzero = refl
  rep-values-octa (fsuc fzero) (fsuc fzero) = refl
  rep-values-octa (fsuc fzero) (fsuc (fsuc fzero)) = refl
  rep-values-octa (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-octa (fsuc fzero) (fsuc (fsuc (fsuc (fsuc ()))))
  rep-values-octa (fsuc (fsuc fzero)) fzero = refl
  rep-values-octa (fsuc (fsuc fzero)) (fsuc fzero) = refl
  rep-values-octa (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) = refl
  rep-values-octa (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-octa (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc ()))))
  rep-values-octa (fsuc (fsuc (fsuc ()))) q
  rep-values-icosa fzero fzero = refl
  rep-values-icosa fzero (fsuc fzero) = refl
  rep-values-icosa fzero (fsuc (fsuc fzero)) = refl
  rep-values-icosa fzero (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa fzero (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa fzero (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc fzero) fzero = refl
  rep-values-icosa (fsuc fzero) (fsuc fzero) = refl
  rep-values-icosa (fsuc fzero) (fsuc (fsuc fzero)) = refl
  rep-values-icosa (fsuc fzero) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa (fsuc fzero) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa (fsuc fzero) (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc (fsuc fzero)) fzero = refl
  rep-values-icosa (fsuc (fsuc fzero)) (fsuc fzero) = refl
  rep-values-icosa (fsuc (fsuc fzero)) (fsuc (fsuc fzero)) = refl
  rep-values-icosa (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa (fsuc (fsuc fzero)) (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc (fsuc (fsuc fzero))) fzero = refl
  rep-values-icosa (fsuc (fsuc (fsuc fzero))) (fsuc fzero) = refl
  rep-values-icosa (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc fzero)) = refl
  rep-values-icosa (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc fzero))) (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc fzero)))) fzero = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc fzero) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc fzero)) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc fzero)))) (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) fzero = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc fzero) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc fzero)) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) fzero = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc fzero) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc fzero)) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) fzero = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc fzero) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc fzero)) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) fzero = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc fzero) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc fzero)) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) fzero = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc fzero) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc fzero)) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc fzero))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (fsuc (fsuc (fsuc (fsuc (fsuc ())))))
  rep-values-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))) q


certificateRep : (c : ShortCase) → Sh c → ambient c .fst
certificateRep octa i = certificatePermutation {t = repTable octa i} (repTable-valid octa i)
certificateRep icosa i = certificatePermutation {t = repTable icosa i} (repTable-valid icosa i)

abstract
  repElement-table : (c : ShortCase) (i : Sh c)
    → ambientHom c .fst (repElement c i) ≡ certificateRep c i
  repElement-table octa i = ambient-word octa (P.nth [] (Ch.reps (certOf octa)) (toℕ i))
    ∙ sym (decode-permutation (repTable octa i) (repTable-valid octa i) _ (rep-values-octa i))
  repElement-table icosa i = ambient-word icosa (P.nth [] (Ch.reps (certOf icosa)) (toℕ i))
    ∙ sym (decode-permutation (repTable icosa i) (repTable-valid icosa i) _ (rep-values-icosa i))

import DeloopS3.Cover.CircleOrbit as CO

abstract
  -- The specified start endpoint for the shared interpreter record.
  shortInput-orbit-start : (c : ShortCase) (input : ShortInput c) (k : Ch.Kind)
    (r : CO.CyclicOrbitData.Rep (ShortInput.orbits input k))
    → CO.CyclicOrbitData.repr (ShortInput.orbits input k) r
      ≡ startOf c k (equivFun (ShortInput.orbit-index input k) r)
  shortInput-orbit-start c input k r = ShortInput.orbit-start input k r
    ∙ firstSheet-value c k (equivFun (ShortInput.orbit-index input k) r) _

abstract
  repTable-member-icosa : (i : Sh icosa)
    → P.member P.tableEq (repTable icosa i) (Ch.group (certOf icosa)) ≡ true
  repTable-member-icosa fzero = refl
  repTable-member-icosa (fsuc fzero) = refl
  repTable-member-icosa (fsuc (fsuc fzero)) = refl
  repTable-member-icosa (fsuc (fsuc (fsuc fzero))) = refl
  repTable-member-icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  repTable-member-icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  repTable-member-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  repTable-member-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  repTable-member-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  repTable-member-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  repTable-member-icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))

  repElement-decode-octa : (i : Sh octa)
    → repElement octa i ≡ certificatePermutation {t = repTable octa i} (repTable-valid octa i)
  repElement-decode-octa = repElement-table octa

  repElement-decode-icosa : (i : Sh icosa)
    → repElement icosa i ≡ Concrete.A₅-tables.locate (repTable icosa i) (repTable-member-icosa i)
  repElement-decode-icosa i = Concrete.A₅-tables.embed-injective
    (repElement-table icosa i ∙ sym
      (Concrete.A₅-tables.realize (repTable icosa i) (repTable-member-icosa i)
       ∙ certificate-cong (repTable icosa i) (repTable icosa i)
         (Concrete.A₅-tables.listed-valid (repTable icosa i) (repTable-member-icosa i))
         (repTable-valid icosa i) refl))
