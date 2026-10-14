{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Initial.Walk where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.Nat using (ℕ)
import Cubical.Data.SumFin as SF
open import DeloopS3.Cert.Input.Graph.Base
open import DeloopS3.Cert.Input.Graph.Maps using (collapse)
open import DeloopS3.Groups.TablePermutation using (tablePermutation-value; and-left)
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P

walk : (c : ShortCase) → Sh c → List BaseLetter → Sh c
walk c i [] = i
walk c i (t ∷ ts) = walk c (actFin (certOf c) (rawChecks c) t i) ts

walkPath : (c : ShortCase) (i : Sh c) (w : List BaseLetter)
  → Path (LiftedGraph c) (vertex i) (vertex (walk c i w))
walkPath c i [] = refl
walkPath c i (t ∷ ts) = signedEdge c i t ∙ walkPath c (actFin (certOf c) (rawChecks c) t i) ts

abstract
  act-value : (c : ShortCase) (i : Sh c) (t : BaseLetter)
    → SF.toℕ (actFin (certOf c) (rawChecks c) t i)
      ≡ Ch.act (Ch.action (certOf c)) (SF.toℕ i) (wireLetter t)
  act-value c i t = tablePermutation-value
    (and-left (Short.action-checked (certOf c) (rawChecks c) t)) i

  liftLetter-sound : (c : ShortCase) (i : Sh c) (t : BaseLetter)
    → cong (collapse c) (signedEdge c i t)
      ≡ R.roseWord (gs c) (Ch.liftLetter (certOf c) (SF.toℕ i) (wireLetter t))
  liftLetter-sound c i a+ = cong-∙ (collapse c) (edge i ga) (cong vertex (nextSheet-action c i ga))
    ∙ sym (rUnit (R.roseWord (gs c) (Ch.labelAt (Ch.labels (certOf c)) (edgeCode c i ga))))
  liftLetter-sound c i b+ = cong-∙ (collapse c) (edge i gb) (cong vertex (nextSheet-action c i gb))
    ∙ sym (rUnit (R.roseWord (gs c) (Ch.labelAt (Ch.labels (certOf c)) (edgeCode c i gb))))
  liftLetter-sound c i a- = cong-∙ (collapse c) (sym (cong vertex (next-negative c i ga)))
      (sym (edge (actFin (certOf c) (rawChecks c) a- i) ga))
    ∙ sym (lUnit (sym (R.roseWord (gs c) label)))
    ∙ sym (R.eval-inverse (R.loopAt (gs c)) label)
    ∙ cong (λ n → R.roseWord (gs c) (P.inverseWord (Ch.labelAt (Ch.labels (certOf c)) (Ch.edge n 1))))
        (act-value c i a-)
    where
    label : P.Word
    label = Ch.labelAt (Ch.labels (certOf c)) (edgeCode c (actFin (certOf c) (rawChecks c) a- i) ga)
  liftLetter-sound c i b- = cong-∙ (collapse c) (sym (cong vertex (next-negative c i gb)))
      (sym (edge (actFin (certOf c) (rawChecks c) b- i) gb))
    ∙ sym (lUnit (sym (R.roseWord (gs c) label)))
    ∙ sym (R.eval-inverse (R.loopAt (gs c)) label)
    ∙ cong (λ n → R.roseWord (gs c) (P.inverseWord (Ch.labelAt (Ch.labels (certOf c)) (Ch.edge n 2))))
        (act-value c i b-)
    where
    label : P.Word
    label = Ch.labelAt (Ch.labels (certOf c)) (edgeCode c (actFin (certOf c) (rawChecks c) b- i) gb)

  liftAcc-sound : (c : ShortCase) (i : Sh c) (w : List BaseLetter) (out : P.Word)
    → R.roseWord (gs c) (P.snd (Ch.liftAcc (certOf c) (SF.toℕ i) (wireWord w) out))
      ≡ R.roseWord (gs c) out ∙ cong (collapse c) (walkPath c i w)
  liftAcc-sound c i [] out = R.eval-reduce (R.loopAt (gs c)) out
    ∙ rUnit (R.roseWord (gs c) out)
  liftAcc-sound c i (t ∷ ts) out =
    cong (λ n → R.roseWord (gs c) (P.snd (Ch.liftAcc (certOf c) n (wireWord ts) (out P.++ letter))))
      (sym (act-value c i t))
    ∙ liftAcc-sound c next ts (out P.++ letter)
    ∙ cong (_∙ tail) (R.eval-append (R.loopAt (gs c)) out letter)
    ∙ sym (assoc (R.roseWord (gs c) out) (R.roseWord (gs c) letter) tail)
    ∙ cong (R.roseWord (gs c) out ∙_) (cong (_∙ tail) (sym (liftLetter-sound c i t))
      ∙ sym (cong-∙ (collapse c) (signedEdge c i t) (walkPath c next ts)))
    where
    next : Sh c
    next = actFin (certOf c) (rawChecks c) t i
    letter : P.Word
    letter = Ch.liftLetter (certOf c) (SF.toℕ i) (wireLetter t)
    tail : Path (R.Rose (gs c)) R.root R.root
    tail = cong (collapse c) (walkPath c next ts)

  liftAcc-endpoint : (c : ShortCase) (i : Sh c) (w : List BaseLetter) (out : P.Word)
    → SF.toℕ (walk c i w)
      ≡ P.fst (Ch.liftAcc (certOf c) (SF.toℕ i) (wireWord w) out)
  liftAcc-endpoint c i [] out = refl
  liftAcc-endpoint c i (t ∷ ts) out = liftAcc-endpoint c next ts more
    ∙ cong (λ n → P.fst (Ch.liftAcc (certOf c) n (wireWord ts) more)) (act-value c i t)
    where
    next : Sh c
    next = actFin (certOf c) (rawChecks c) t i
    more : P.Word
    more = out P.++ Ch.liftLetter (certOf c) (SF.toℕ i) (wireLetter t)

  walk-endpoint : (c : ShortCase) (i : Sh c) (w : List BaseLetter)
    → SF.toℕ (walk c i w)
      ≡ P.fst (Ch.liftWord (certOf c) (SF.toℕ i) (wireWord w))
  walk-endpoint c i w = liftAcc-endpoint c i w []
