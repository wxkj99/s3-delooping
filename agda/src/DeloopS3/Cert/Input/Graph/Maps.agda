{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Graph.Maps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.List.Base using ([]; _∷_)
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin using (Fin; fzero; fsuc; toℕ)
open import DeloopS3.Cert.Input.Graph.Base
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Interpret.Realization as R

treeRoute : (c : ShortCase) (i : Sh c)
  → Path (LiftedGraph c) (vertex (rootSheet c)) (vertex i)
treeRoute octa fzero = refl
treeRoute octa (fsuc fzero) = edge fzero ga
treeRoute octa (fsuc (fsuc fzero)) = edge fzero gb
treeRoute octa (fsuc (fsuc (fsuc ())))
treeRoute icosa fzero = refl
treeRoute icosa (fsuc fzero) = edge fzero ga
treeRoute icosa (fsuc (fsuc fzero)) = (edge fzero ga) ∙ edge (fsuc fzero) gb
treeRoute icosa (fsuc (fsuc (fsuc fzero))) = (edge fzero ga) ∙ sym (edge (fsuc (fsuc (fsuc fzero))) gb)
treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = ((edge fzero ga) ∙ edge (fsuc fzero) gb) ∙ edge (fsuc (fsuc fzero)) ga
treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = ((edge fzero ga) ∙ sym (edge (fsuc (fsuc (fsuc fzero))) gb)) ∙ edge (fsuc (fsuc (fsuc fzero))) ga
treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = (((edge fzero ga) ∙ edge (fsuc fzero) gb) ∙ edge (fsuc (fsuc fzero)) ga) ∙ edge (fsuc (fsuc (fsuc (fsuc fzero)))) gb
treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = (((edge fzero ga) ∙ edge (fsuc fzero) gb) ∙ edge (fsuc (fsuc fzero)) ga) ∙ sym (edge (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb)
treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = (((edge fzero ga) ∙ sym (edge (fsuc (fsuc (fsuc fzero))) gb)) ∙ edge (fsuc (fsuc (fsuc fzero))) ga) ∙ edge (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb
treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = (((edge fzero ga) ∙ sym (edge (fsuc (fsuc (fsuc fzero))) gb)) ∙ edge (fsuc (fsuc (fsuc fzero))) ga) ∙ sym (edge (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb)
treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))

collapse : (c : ShortCase) → LiftedGraph c → R.Rose (gs c)
collapse c (vertex i) = R.root
collapse c (edge i g t) = R.roseWord (gs c)
  (Ch.labelAt (Ch.labels (certOf c)) (edgeCode c i g)) t

Petal : ShortCase → Type₀
Petal c = Fin (P.length (gs c))

nonTree : (c : ShortCase) → Petal c → Sh c × Generator
nonTree octa fzero = (fsuc fzero) , ga
nonTree octa (fsuc fzero) = (fsuc fzero) , gb
nonTree octa (fsuc (fsuc fzero)) = (fsuc (fsuc fzero)) , ga
nonTree octa (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc fzero)) , gb
nonTree octa (fsuc (fsuc (fsuc (fsuc ()))))
nonTree icosa fzero = fzero , gb
nonTree icosa (fsuc fzero) = (fsuc fzero) , ga
nonTree icosa (fsuc (fsuc fzero)) = (fsuc (fsuc fzero)) , gb
nonTree icosa (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc (fsuc (fsuc fzero)))) , ga
nonTree icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) , ga
nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) , ga
nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) , gb
nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) , ga
nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) , ga
nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) , gb
nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) , ga
nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))

rootedEdge : (c : ShortCase) (i : Sh c) (g : Generator)
  → Path (LiftedGraph c) (vertex (rootSheet c)) (vertex (rootSheet c))
rootedEdge c i g = (treeRoute c i ∙ edge i g) ∙ sym (treeRoute c (nextSheet c i g))

expand : (c : ShortCase) → R.Rose (gs c) → LiftedGraph c
expand c R.root = vertex (rootSheet c)
expand c (R.petal k t) = rootedEdge c (nonTree c k .fst) (nonTree c k .snd) t

-- This is the certificate's literal word, not its value in Δ.
representativeWord : (c : ShortCase) → Sh c → P.Word
representativeWord c i = P.nth [] (Ch.reps (certOf c)) (toℕ i)

abstract
  project-append : (c : ShortCase) {i j : Sh c}
    (p : Path (LiftedGraph c) (vertex (rootSheet c)) (vertex i))
    (q : Path (LiftedGraph c) (vertex i) (vertex j))
    (w : P.Word) (t : P.Letter)
    → cong (projectGraph c) p ≡ R.roseWord twoGenerators w
    → cong (projectGraph c) q ≡ R.evalLetter (R.loopAt twoGenerators) t
    → cong (projectGraph c) (p ∙ q) ≡ R.roseWord twoGenerators (w P.++ (t ∷ []))
  project-append c p q w t hp hq = cong-∙ (projectGraph c) p q
    ∙ cong₂ _∙_ hp (hq ∙ rUnit (R.evalLetter (R.loopAt twoGenerators) t))
    ∙ sym (R.eval-append (R.loopAt twoGenerators) w (t ∷ []))

  project-treeRoute : (c : ShortCase) (i : Sh c)
    → Path (Path Γ R.root R.root)
        (cong (projectGraph c) (treeRoute c i))
        (R.roseWord twoGenerators (representativeWord c i))
  project-treeRoute octa fzero = refl
  project-treeRoute octa (fsuc fzero) = rUnit (cong (projectGraph octa) (edge fzero ga))
  project-treeRoute octa (fsuc (fsuc fzero)) = rUnit (cong (projectGraph octa) (edge fzero gb))
  project-treeRoute octa (fsuc (fsuc (fsuc ())))
  project-treeRoute icosa fzero = refl
  project-treeRoute icosa (fsuc fzero) = rUnit (cong (projectGraph icosa) (edge fzero ga))
  project-treeRoute icosa (fsuc (fsuc fzero)) = project-append icosa (treeRoute icosa (fsuc fzero)) (edge (fsuc fzero) gb)
    (representativeWord icosa (fsuc fzero)) (P.fwd 2) ((rUnit (cong (projectGraph icosa) (edge fzero ga)))) refl
  project-treeRoute icosa (fsuc (fsuc (fsuc fzero))) = project-append icosa (treeRoute icosa (fsuc fzero)) (sym (edge (fsuc (fsuc (fsuc fzero))) gb))
    (representativeWord icosa (fsuc fzero)) (P.bwd 2) ((rUnit (cong (projectGraph icosa) (edge fzero ga)))) refl
  project-treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = project-append icosa (treeRoute icosa (fsuc (fsuc fzero))) (edge (fsuc (fsuc fzero)) ga)
    (representativeWord icosa (fsuc (fsuc fzero))) (P.fwd 1) ((project-append icosa (treeRoute icosa (fsuc fzero)) (edge (fsuc fzero) gb)
    (representativeWord icosa (fsuc fzero)) (P.fwd 2) ((rUnit (cong (projectGraph icosa) (edge fzero ga)))) refl)) refl
  project-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = project-append icosa (treeRoute icosa (fsuc (fsuc (fsuc fzero)))) (edge (fsuc (fsuc (fsuc fzero))) ga)
    (representativeWord icosa (fsuc (fsuc (fsuc fzero)))) (P.fwd 1) ((project-append icosa (treeRoute icosa (fsuc fzero)) (sym (edge (fsuc (fsuc (fsuc fzero))) gb))
    (representativeWord icosa (fsuc fzero)) (P.bwd 2) ((rUnit (cong (projectGraph icosa) (edge fzero ga)))) refl)) refl
  project-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = project-append icosa (treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero))))) (edge (fsuc (fsuc (fsuc (fsuc fzero)))) gb)
    (representativeWord icosa (fsuc (fsuc (fsuc (fsuc fzero))))) (P.fwd 2) ((project-append icosa (treeRoute icosa (fsuc (fsuc fzero))) (edge (fsuc (fsuc fzero)) ga)
    (representativeWord icosa (fsuc (fsuc fzero))) (P.fwd 1) ((project-append icosa (treeRoute icosa (fsuc fzero)) (edge (fsuc fzero) gb)
    (representativeWord icosa (fsuc fzero)) (P.fwd 2) ((rUnit (cong (projectGraph icosa) (edge fzero ga)))) refl)) refl)) refl
  project-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = project-append icosa (treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero))))) (sym (edge (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb))
    (representativeWord icosa (fsuc (fsuc (fsuc (fsuc fzero))))) (P.bwd 2) ((project-append icosa (treeRoute icosa (fsuc (fsuc fzero))) (edge (fsuc (fsuc fzero)) ga)
    (representativeWord icosa (fsuc (fsuc fzero))) (P.fwd 1) ((project-append icosa (treeRoute icosa (fsuc fzero)) (edge (fsuc fzero) gb)
    (representativeWord icosa (fsuc fzero)) (P.fwd 2) ((rUnit (cong (projectGraph icosa) (edge fzero ga)))) refl)) refl)) refl
  project-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = project-append icosa (treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (edge (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb)
    (representativeWord icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (P.fwd 2) ((project-append icosa (treeRoute icosa (fsuc (fsuc (fsuc fzero)))) (edge (fsuc (fsuc (fsuc fzero))) ga)
    (representativeWord icosa (fsuc (fsuc (fsuc fzero)))) (P.fwd 1) ((project-append icosa (treeRoute icosa (fsuc fzero)) (sym (edge (fsuc (fsuc (fsuc fzero))) gb))
    (representativeWord icosa (fsuc fzero)) (P.bwd 2) ((rUnit (cong (projectGraph icosa) (edge fzero ga)))) refl)) refl)) refl
  project-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = project-append icosa (treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (sym (edge (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb))
    (representativeWord icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (P.bwd 2) ((project-append icosa (treeRoute icosa (fsuc (fsuc (fsuc fzero)))) (edge (fsuc (fsuc (fsuc fzero))) ga)
    (representativeWord icosa (fsuc (fsuc (fsuc fzero)))) (P.fwd 1) ((project-append icosa (treeRoute icosa (fsuc fzero)) (sym (edge (fsuc (fsuc (fsuc fzero))) gb))
    (representativeWord icosa (fsuc fzero)) (P.bwd 2) ((rUnit (cong (projectGraph icosa) (edge fzero ga)))) refl)) refl)) refl
  project-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))

  collapse-treeRoute : (c : ShortCase) (i : Sh c)
    → cong (collapse c) (treeRoute c i) ≡ refl
  collapse-treeRoute octa fzero = refl
  collapse-treeRoute octa (fsuc fzero) = refl
  collapse-treeRoute octa (fsuc (fsuc fzero)) = refl
  collapse-treeRoute octa (fsuc (fsuc (fsuc ())))
  collapse-treeRoute icosa fzero = refl
  collapse-treeRoute icosa (fsuc fzero) = refl
  collapse-treeRoute icosa (fsuc (fsuc fzero)) = cong-∙ (collapse icosa) (treeRoute icosa (fsuc fzero)) (edge (fsuc fzero) gb)
    ∙ cong (_∙ refl) ((refl)) ∙ sym (lUnit refl)
  collapse-treeRoute icosa (fsuc (fsuc (fsuc fzero))) = cong-∙ (collapse icosa) (treeRoute icosa (fsuc fzero)) (sym (edge (fsuc (fsuc (fsuc fzero))) gb))
    ∙ cong (_∙ refl) ((refl)) ∙ sym (lUnit refl)
  collapse-treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc fzero))) (edge (fsuc (fsuc fzero)) ga)
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc fzero)) (edge (fsuc fzero) gb)
    ∙ cong (_∙ refl) ((refl)) ∙ sym (lUnit refl))) ∙ sym (lUnit refl)
  collapse-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc (fsuc fzero)))) (edge (fsuc (fsuc (fsuc fzero))) ga)
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc fzero)) (sym (edge (fsuc (fsuc (fsuc fzero))) gb))
    ∙ cong (_∙ refl) ((refl)) ∙ sym (lUnit refl))) ∙ sym (lUnit refl)
  collapse-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero))))) (edge (fsuc (fsuc (fsuc (fsuc fzero)))) gb)
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc fzero))) (edge (fsuc (fsuc fzero)) ga)
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc fzero)) (edge (fsuc fzero) gb)
    ∙ cong (_∙ refl) ((refl)) ∙ sym (lUnit refl))) ∙ sym (lUnit refl))) ∙ sym (lUnit refl)
  collapse-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero))))) (sym (edge (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb))
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc fzero))) (edge (fsuc (fsuc fzero)) ga)
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc fzero)) (edge (fsuc fzero) gb)
    ∙ cong (_∙ refl) ((refl)) ∙ sym (lUnit refl))) ∙ sym (lUnit refl))) ∙ sym (lUnit refl)
  collapse-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (edge (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb)
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc (fsuc fzero)))) (edge (fsuc (fsuc (fsuc fzero))) ga)
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc fzero)) (sym (edge (fsuc (fsuc (fsuc fzero))) gb))
    ∙ cong (_∙ refl) ((refl)) ∙ sym (lUnit refl))) ∙ sym (lUnit refl))) ∙ sym (lUnit refl)
  collapse-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (sym (edge (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb))
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc (fsuc (fsuc fzero)))) (edge (fsuc (fsuc (fsuc fzero))) ga)
    ∙ cong (_∙ refl) ((cong-∙ (collapse icosa) (treeRoute icosa (fsuc fzero)) (sym (edge (fsuc (fsuc (fsuc fzero))) gb))
    ∙ cong (_∙ refl) ((refl)) ∙ sym (lUnit refl))) ∙ sym (lUnit refl))) ∙ sym (lUnit refl)
  collapse-treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))

  collapse-nonTree : (c : ShortCase) (k : Petal c)
    → cong (collapse c) (edge (nonTree c k .fst) (nonTree c k .snd)) ≡ R.petal k
  collapse-nonTree octa fzero = sym (rUnit (R.petal fzero))
  collapse-nonTree octa (fsuc fzero) = sym (rUnit (R.petal (fsuc fzero)))
  collapse-nonTree octa (fsuc (fsuc fzero)) = sym (rUnit (R.petal (fsuc (fsuc fzero))))
  collapse-nonTree octa (fsuc (fsuc (fsuc fzero))) = sym (rUnit (R.petal (fsuc (fsuc (fsuc fzero)))))
  collapse-nonTree octa (fsuc (fsuc (fsuc (fsuc ()))))
  collapse-nonTree icosa fzero = sym (rUnit (R.petal fzero))
  collapse-nonTree icosa (fsuc fzero) = sym (rUnit (R.petal (fsuc fzero)))
  collapse-nonTree icosa (fsuc (fsuc fzero)) = sym (rUnit (R.petal (fsuc (fsuc fzero))))
  collapse-nonTree icosa (fsuc (fsuc (fsuc fzero))) = sym (rUnit (R.petal (fsuc (fsuc (fsuc fzero)))))
  collapse-nonTree icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = sym (rUnit (R.petal (fsuc (fsuc (fsuc (fsuc fzero))))))
  collapse-nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = sym (rUnit (R.petal (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
  collapse-nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = sym (rUnit (R.petal (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
  collapse-nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = sym (rUnit (R.petal (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
  collapse-nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = sym (rUnit (R.petal (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))
  collapse-nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = sym (rUnit (R.petal (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))))
  collapse-nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) = sym (rUnit (R.petal (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))))
  collapse-nonTree icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))))
