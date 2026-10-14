{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Graph.Chart where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin using (fzero; fsuc)
open import DeloopS3.Cert.Input.Graph.Base
open import DeloopS3.Cert.Input.Graph.Maps
import DeloopS3.Cert.Interpret.Realization as R

private
  abstract
    cancel-tail : {X : Type₀} {x y z : X} (p : x ≡ y) (q : z ≡ y)
      → (p ∙ sym q) ∙ q ≡ p
    cancel-tail p q = sym (assoc p (sym q) q)
      ∙ cong (p ∙_) (lCancel q) ∙ sym (rUnit p)

abstract
  unit-petal : (c : ShortCase) (k : Petal c)
    → cong (collapse c) (rootedEdge c (nonTree c k .fst) (nonTree c k .snd)) ≡ R.petal k
  unit-petal c k =
    cong-∙ (collapse c) (treeRoute c s ∙ edge s g) (sym (treeRoute c (nextSheet c s g)))
    ∙ cong₂ _∙_
      (cong-∙ (collapse c) (treeRoute c s) (edge s g)
       ∙ cong₂ _∙_ (collapse-treeRoute c s) (collapse-nonTree c k))
      (cong sym (collapse-treeRoute c (nextSheet c s g)))
    ∙ cong (_∙ refl) (sym (lUnit (R.petal k))) ∙ sym (rUnit (R.petal k))
    where
    s : Sh c
    s = nonTree c k .fst
    g : Generator
    g = nonTree c k .snd

  nonTree-square : (c : ShortCase) (k : Petal c)
    → cong (λ x → expand c (collapse c x)) (edge (nonTree c k .fst) (nonTree c k .snd))
        ∙ treeRoute c (nextSheet c (nonTree c k .fst) (nonTree c k .snd))
      ≡ treeRoute c (nonTree c k .fst) ∙ edge (nonTree c k .fst) (nonTree c k .snd)
  nonTree-square c k = cong (_∙ treeRoute c (nextSheet c s g))
      (cong (cong (expand c)) (collapse-nonTree c k))
    ∙ cancel-tail (treeRoute c s ∙ edge s g) (treeRoute c (nextSheet c s g))
    where
    s : Sh c
    s = nonTree c k .fst
    g : Generator
    g = nonTree c k .snd

  counit-edge : (c : ShortCase) (i : Sh c) (g : Generator)
    → cong (λ x → expand c (collapse c x)) (edge i g) ∙ treeRoute c (nextSheet c i g)
      ≡ treeRoute c i ∙ edge i g
  counit-edge octa fzero ga = refl
  counit-edge octa fzero gb = refl
  counit-edge octa (fsuc fzero) ga = nonTree-square octa fzero
  counit-edge octa (fsuc fzero) gb = nonTree-square octa (fsuc fzero)
  counit-edge octa (fsuc (fsuc fzero)) ga = nonTree-square octa (fsuc (fsuc fzero))
  counit-edge octa (fsuc (fsuc fzero)) gb = nonTree-square octa (fsuc (fsuc (fsuc fzero)))
  counit-edge octa (fsuc (fsuc (fsuc ()))) g
  counit-edge icosa fzero ga = refl
  counit-edge icosa fzero gb = nonTree-square icosa fzero
  counit-edge icosa (fsuc fzero) ga = nonTree-square icosa (fsuc fzero)
  counit-edge icosa (fsuc fzero) gb = sym (lUnit (treeRoute icosa (fsuc (fsuc fzero))))
  counit-edge icosa (fsuc (fsuc fzero)) ga = sym (lUnit (treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero))))))
  counit-edge icosa (fsuc (fsuc fzero)) gb = nonTree-square icosa (fsuc (fsuc fzero))
  counit-edge icosa (fsuc (fsuc (fsuc fzero))) ga = sym (lUnit (treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
  counit-edge icosa (fsuc (fsuc (fsuc fzero))) gb = sym (lUnit (treeRoute icosa (fsuc fzero)))
    ∙ sym (cancel-tail (treeRoute icosa (fsuc fzero)) (edge (fsuc (fsuc (fsuc fzero))) gb))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc fzero)))) ga = nonTree-square icosa (fsuc (fsuc (fsuc fzero)))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc fzero)))) gb = sym (lUnit (treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) ga = nonTree-square icosa (fsuc (fsuc (fsuc (fsuc fzero))))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb = sym (lUnit (treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ga = nonTree-square icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) gb = nonTree-square icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ga = nonTree-square icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb = sym (lUnit (treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero))))))
    ∙ sym (cancel-tail (treeRoute icosa (fsuc (fsuc (fsuc (fsuc fzero))))) (edge (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) ga = nonTree-square icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) gb = nonTree-square icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) ga = nonTree-square icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb = sym (lUnit (treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
    ∙ sym (cancel-tail (treeRoute icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (edge (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb))
  counit-edge icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))) g

tree-unit : (c : ShortCase) (x : R.Rose (gs c)) → collapse c (expand c x) ≡ x
tree-unit c R.root = refl
tree-unit c (R.petal k i) j = unit-petal c k j i

tree-counit : (c : ShortCase) (x : LiftedGraph c) → expand c (collapse c x) ≡ x
tree-counit c (vertex i) = treeRoute c i
tree-counit c (edge i g t) j = compPath→Square (counit-edge c i g) t j

record TreeChart (c : ShortCase) : Type₀ where
  field
    unit : (x : R.Rose (gs c)) → collapse c (expand c x) ≡ x
    counit : (x : LiftedGraph c) → expand c (collapse c x) ≡ x
    counit-vertex : (i : Sh c) → counit (vertex i) ≡ treeRoute c i

tree-chart : (c : ShortCase) → TreeChart c
TreeChart.unit (tree-chart c) = tree-unit c
TreeChart.counit (tree-chart c) = tree-counit c
TreeChart.counit-vertex (tree-chart c) i = refl

octa-tree-chart : TreeChart octa
octa-tree-chart = tree-chart octa
icosa-tree-chart : TreeChart icosa
icosa-tree-chart = tree-chart icosa

graph-chart : (c : ShortCase) → R.Rose (gs c) ≃ LiftedGraph c
graph-chart c = isoToEquiv (iso (expand c) (collapse c) (tree-counit c) (tree-unit c))
