{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Graph.Base where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.SumFin using (Fin; fzero; fsuc; toℕ; toℕ-injective)
open import DeloopS3.Cert.Input.Model.Vocabulary public
open import DeloopS3.Cert.Input.Model.Finite using (act-a-inverse; act-b-inverse)
open import DeloopS3.Groups.TablePermutation using (tablePermutation-value; and-left)
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Interpret.Realization as R

open import DeloopS3.Cert.Input.Graph.Core public using (Generator; ga; gb; ActionGraph; vertex; edge)
import DeloopS3.Cert.Input.Graph.Core as Core

positive : Generator → BaseLetter
positive ga = a+
positive gb = b+

edgeCode : (c : ShortCase) → Sh c → Generator → Ch.Edge
edgeCode c i ga = Ch.edge (toℕ i) 1
edgeCode c i gb = Ch.edge (toℕ i) 2

rootSheet : (c : ShortCase) → Sh c
rootSheet octa = fzero
rootSheet icosa = fzero

-- Literal finite endpoints: never reduce the opaque permutation proof.
nextSheet : (c : ShortCase) → Sh c → Generator → Sh c
nextSheet octa fzero ga = (fsuc fzero)
nextSheet octa (fsuc fzero) ga = fzero
nextSheet octa (fsuc (fsuc fzero)) ga = (fsuc (fsuc fzero))
nextSheet octa fzero gb = (fsuc (fsuc fzero))
nextSheet octa (fsuc fzero) gb = fzero
nextSheet octa (fsuc (fsuc fzero)) gb = (fsuc fzero)
nextSheet octa (fsuc (fsuc (fsuc ()))) g
nextSheet icosa fzero ga = (fsuc fzero)
nextSheet icosa (fsuc fzero) ga = fzero
nextSheet icosa (fsuc (fsuc fzero)) ga = (fsuc (fsuc (fsuc (fsuc fzero))))
nextSheet icosa (fsuc (fsuc (fsuc fzero))) ga = (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc fzero)))) ga = (fsuc (fsuc fzero))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) ga = (fsuc (fsuc (fsuc fzero)))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ga = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ga = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) ga = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) ga = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
nextSheet icosa fzero gb = fzero
nextSheet icosa (fsuc fzero) gb = (fsuc (fsuc fzero))
nextSheet icosa (fsuc (fsuc fzero)) gb = (fsuc (fsuc (fsuc fzero)))
nextSheet icosa (fsuc (fsuc (fsuc fzero))) gb = (fsuc fzero)
nextSheet icosa (fsuc (fsuc (fsuc (fsuc fzero)))) gb = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) gb = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb = (fsuc (fsuc (fsuc (fsuc fzero))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) gb = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb = (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
nextSheet icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))) g

abstract
  nextSheet-value : (c : ShortCase) (i : Sh c) (g : Generator)
    → toℕ (nextSheet c i g)
      ≡ P.apply (Ch.actTable (Ch.action (certOf c)) (wireLetter (positive g))) (toℕ i)
  nextSheet-value octa fzero ga = refl
  nextSheet-value octa fzero gb = refl
  nextSheet-value octa (fsuc fzero) ga = refl
  nextSheet-value octa (fsuc fzero) gb = refl
  nextSheet-value octa (fsuc (fsuc fzero)) ga = refl
  nextSheet-value octa (fsuc (fsuc fzero)) gb = refl
  nextSheet-value octa (fsuc (fsuc (fsuc ()))) g
  nextSheet-value icosa fzero ga = refl
  nextSheet-value icosa fzero gb = refl
  nextSheet-value icosa (fsuc fzero) ga = refl
  nextSheet-value icosa (fsuc fzero) gb = refl
  nextSheet-value icosa (fsuc (fsuc fzero)) ga = refl
  nextSheet-value icosa (fsuc (fsuc fzero)) gb = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc fzero))) ga = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc fzero))) gb = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc fzero)))) ga = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc fzero)))) gb = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) ga = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ga = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) gb = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ga = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) ga = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) gb = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) ga = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb = refl
  nextSheet-value icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))) g

  nextSheet-action : (c : ShortCase) (i : Sh c) (g : Generator)
    → nextSheet c i g ≡ actFin (certOf c) (rawChecks c) (positive g) i
  nextSheet-action c i g = toℕ-injective
    (nextSheet-value c i g ∙ sym (tablePermutation-value
      (and-left (Short.action-checked (certOf c) (rawChecks c) (positive g))) i))

LiftedGraph : ShortCase → Type₀
LiftedGraph c = ActionGraph (Sh c) (nextSheet c)

projectGraph : (c : ShortCase) → LiftedGraph c → Γ
projectGraph c = Core.project

private
  neg : Generator → BaseLetter
  neg ga = a-
  neg gb = b-

abstract
  next-negative : (c : ShortCase) (i : Sh c) (g : Generator)
    → nextSheet c (actFin (certOf c) (rawChecks c) (neg g) i) g ≡ i
  next-negative c i ga = nextSheet-action c _ ga
    ∙ cong (equivFun (actEquiv (certOf c) (rawChecks c) a+))
      (cong (λ e → equivFun e i) (act-a-inverse c (rawChecks c)))
    ∙ secEq (actEquiv (certOf c) (rawChecks c) a+) i
  next-negative c i gb = nextSheet-action c _ gb
    ∙ cong (equivFun (actEquiv (certOf c) (rawChecks c) b+))
      (cong (λ e → equivFun e i) (act-b-inverse c (rawChecks c)))
    ∙ secEq (actEquiv (certOf c) (rawChecks c) b+) i

signedEdge : (c : ShortCase) (i : Sh c) (t : BaseLetter)
  → Path (LiftedGraph c) (vertex i)
      (vertex (actFin (certOf c) (rawChecks c) t i))
signedEdge c i a+ = edge i ga ∙ cong vertex (nextSheet-action c i ga)
signedEdge c i b+ = edge i gb ∙ cong vertex (nextSheet-action c i gb)
signedEdge c i a- = sym (cong vertex (next-negative c i ga))
  ∙ sym (edge (actFin (certOf c) (rawChecks c) a- i) ga)
signedEdge c i b- = sym (cong vertex (next-negative c i gb))
  ∙ sym (edge (actFin (certOf c) (rawChecks c) b- i) gb)
