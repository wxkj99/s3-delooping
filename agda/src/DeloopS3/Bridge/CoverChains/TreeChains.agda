{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.CoverChains.TreeChains where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin using (fzero; fsuc)
open import Cubical.Algebra.AbGroup
open import DeloopS3.Cert.Input.Graph.Base public
open import DeloopS3.Cert.Input.Graph.Maps using (Petal; nonTree; treeRoute)

previous : (c : ShortCase) → Sh c → Generator → Sh c
previous c s ga = nextSheet c s ga
previous c s gb = nextSheet c (nextSheet c s gb) gb

abstract
  next-previous : (c : ShortCase) (s : Sh c) (g : Generator)
    → nextSheet c (previous c s g) g ≡ s
  next-previous octa fzero ga = refl
  next-previous octa fzero gb = refl
  next-previous octa (fsuc fzero) ga = refl
  next-previous octa (fsuc fzero) gb = refl
  next-previous octa (fsuc (fsuc fzero)) ga = refl
  next-previous octa (fsuc (fsuc fzero)) gb = refl
  next-previous octa (fsuc (fsuc (fsuc ()))) g
  next-previous icosa fzero ga = refl
  next-previous icosa fzero gb = refl
  next-previous icosa (fsuc fzero) ga = refl
  next-previous icosa (fsuc fzero) gb = refl
  next-previous icosa (fsuc (fsuc fzero)) ga = refl
  next-previous icosa (fsuc (fsuc fzero)) gb = refl
  next-previous icosa (fsuc (fsuc (fsuc fzero))) ga = refl
  next-previous icosa (fsuc (fsuc (fsuc fzero))) gb = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc fzero)))) ga = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc fzero)))) gb = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) ga = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ga = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) gb = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ga = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) ga = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) gb = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) ga = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb = refl
  next-previous icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))) g

  previous-next : (c : ShortCase) (s : Sh c) (g : Generator)
    → previous c (nextSheet c s g) g ≡ s
  previous-next octa fzero ga = refl
  previous-next octa fzero gb = refl
  previous-next octa (fsuc fzero) ga = refl
  previous-next octa (fsuc fzero) gb = refl
  previous-next octa (fsuc (fsuc fzero)) ga = refl
  previous-next octa (fsuc (fsuc fzero)) gb = refl
  previous-next octa (fsuc (fsuc (fsuc ()))) g
  previous-next icosa fzero ga = refl
  previous-next icosa fzero gb = refl
  previous-next icosa (fsuc fzero) ga = refl
  previous-next icosa (fsuc fzero) gb = refl
  previous-next icosa (fsuc (fsuc fzero)) ga = refl
  previous-next icosa (fsuc (fsuc fzero)) gb = refl
  previous-next icosa (fsuc (fsuc (fsuc fzero))) ga = refl
  previous-next icosa (fsuc (fsuc (fsuc fzero))) gb = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc fzero)))) ga = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc fzero)))) gb = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) ga = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ga = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) gb = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ga = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) ga = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) gb = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) ga = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb = refl
  previous-next icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))) g

-- This is the certificate's rooted tree, used as a path, not a chosen connectivity
-- witness extracted from propositional truncation.
tree-constant : {X : Type₀} (c : ShortCase) (v : Sh c → X)
  → ((s : Sh c) (g : Generator) → v s ≡ v (nextSheet c s g))
  → (s : Sh c) → v (rootSheet c) ≡ v s
tree-constant c v along s = cong descend (treeRoute c s)
  where
  descend : LiftedGraph c → _
  descend (vertex s) = v s
  descend (edge s g i) = along s g i

module GraphChains (G : AbGroup ℓ-zero) where
  open AbGroupStr (snd G)

  EdgeVector : ShortCase → Type₀
  EdgeVector c = Sh c → Generator → fst G

  GraphCycle : (c : ShortCase) → EdgeVector c → Type₀
  GraphCycle c y = (s : Sh c)
    → y (previous c s ga) ga + y (previous c s gb) gb
      ≡ y s ga + y s gb

  collapse₁ : (c : ShortCase) → EdgeVector c → (Petal c → fst G)
  collapse₁ c y j = y (fst (nonTree c j)) (snd (nonTree c j))

  private
    abstract
      isolate₁ : (a b c d : fst G) → b ≡ 0g → c ≡ 0g → d ≡ 0g
        → a + b ≡ c + d → a ≡ 0g
      isolate₁ a b c d pb pc pd eq = sym (+IdR a)
        ∙ cong (a +_) (sym pb) ∙ eq ∙ cong₂ _+_ pc pd ∙ +IdR 0g

      isolate₂ : (a b c d : fst G) → a ≡ 0g → c ≡ 0g → d ≡ 0g
        → a + b ≡ c + d → b ≡ 0g
      isolate₂ a b c d pa pc pd eq = sym (+IdL b)
        ∙ cong (_+ b) (sym pa) ∙ eq ∙ cong₂ _+_ pc pd ∙ +IdR 0g

      isolate₃ : (a b c d : fst G) → a ≡ 0g → b ≡ 0g → d ≡ 0g
        → a + b ≡ c + d → c ≡ 0g
      isolate₃ a b c d pa pb pd eq = isolate₁ c d a b pd pa pb (sym eq)

      isolate₄ : (a b c d : fst G) → a ≡ 0g → b ≡ 0g → c ≡ 0g
        → a + b ≡ c + d → d ≡ 0g
      isolate₄ a b c d pa pb pc eq = isolate₂ c d a b pc pa pb (sym eq)

  -- Leaf elimination in the certificate's literal spanning tree. Every
  -- non-tree coordinate is taken from Graph.Maps.nonTree; the remaining
  -- equations are the graph boundary equations at successive leaves.
  abstract
    collapse-injective-on-cycles : (c : ShortCase) (y : EdgeVector c)
      → GraphCycle c y → ((j : Petal c) → collapse₁ c y j ≡ 0g)
      → (s : Sh c) (g : Generator) → y s g ≡ 0g
    collapse-injective-on-cycles octa y cyc nt = result
      where
      t0a : y fzero ga ≡ 0g
      t0a = isolate₁ (y fzero ga) (y (fsuc (fsuc fzero)) gb) (y (fsuc fzero) ga) (y (fsuc fzero) gb) (nt (fsuc (fsuc (fsuc fzero)))) (nt fzero) (nt (fsuc fzero)) (cyc (fsuc fzero))
      t0b : y fzero gb ≡ 0g
      t0b = isolate₂ (y (fsuc (fsuc fzero)) ga) (y fzero gb) (y (fsuc (fsuc fzero)) ga) (y (fsuc (fsuc fzero)) gb) (nt (fsuc (fsuc fzero))) (nt (fsuc (fsuc fzero))) (nt (fsuc (fsuc (fsuc fzero)))) (cyc (fsuc (fsuc fzero)))
      result : (s : Sh octa) (g : Generator) → y s g ≡ 0g
      result fzero ga = t0a
      result fzero gb = t0b
      result (fsuc fzero) ga = nt fzero
      result (fsuc fzero) gb = nt (fsuc fzero)
      result (fsuc (fsuc fzero)) ga = nt (fsuc (fsuc fzero))
      result (fsuc (fsuc fzero)) gb = nt (fsuc (fsuc (fsuc fzero)))
      result (fsuc (fsuc (fsuc ()))) g
    collapse-injective-on-cycles icosa y cyc nt = result
      where
      t0a : y fzero ga ≡ 0g
      t0a = isolate₃ (y (fsuc fzero) ga) (y fzero gb) (y fzero ga) (y fzero gb) (nt (fsuc fzero)) (nt fzero) (nt fzero) (cyc fzero)
      t4b : y (fsuc (fsuc (fsuc (fsuc fzero)))) gb ≡ 0g
      t4b = isolate₂ (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) ga) (y (fsuc (fsuc (fsuc (fsuc fzero)))) gb) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) gb) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (nt (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (cyc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
      t7b : y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb ≡ 0g
      t7b = isolate₄ (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) gb) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) (cyc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
      t5b : y (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb ≡ 0g
      t5b = isolate₂ (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) gb) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (cyc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
      t9b : y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb ≡ 0g
      t9b = isolate₄ (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) gb) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb) (nt (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))) (nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))) (cyc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))
      t2a : y (fsuc (fsuc fzero)) ga ≡ 0g
      t2a = isolate₁ (y (fsuc (fsuc fzero)) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb) (y (fsuc (fsuc (fsuc (fsuc fzero)))) ga) (y (fsuc (fsuc (fsuc (fsuc fzero)))) gb) (t7b) (nt (fsuc (fsuc (fsuc fzero)))) (t4b) (cyc (fsuc (fsuc (fsuc (fsuc fzero)))))
      t3a : y (fsuc (fsuc (fsuc fzero))) ga ≡ 0g
      t3a = isolate₁ (y (fsuc (fsuc (fsuc fzero))) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb) (y (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) ga) (y (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb) (t9b) (nt (fsuc (fsuc (fsuc (fsuc fzero))))) (t5b) (cyc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
      t1b : y (fsuc fzero) gb ≡ 0g
      t1b = isolate₂ (y (fsuc (fsuc (fsuc (fsuc fzero)))) ga) (y (fsuc fzero) gb) (y (fsuc (fsuc fzero)) ga) (y (fsuc (fsuc fzero)) gb) (nt (fsuc (fsuc (fsuc fzero)))) (t2a) (nt (fsuc (fsuc fzero))) (cyc (fsuc (fsuc fzero)))
      t3b : y (fsuc (fsuc (fsuc fzero))) gb ≡ 0g
      t3b = isolate₄ (y (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) ga) (y (fsuc (fsuc fzero)) gb) (y (fsuc (fsuc (fsuc fzero))) ga) (y (fsuc (fsuc (fsuc fzero))) gb) (nt (fsuc (fsuc (fsuc (fsuc fzero))))) (nt (fsuc (fsuc fzero))) (t3a) (cyc (fsuc (fsuc (fsuc fzero))))
      result : (s : Sh icosa) (g : Generator) → y s g ≡ 0g
      result fzero ga = t0a
      result fzero gb = nt fzero
      result (fsuc fzero) ga = nt (fsuc fzero)
      result (fsuc fzero) gb = t1b
      result (fsuc (fsuc fzero)) ga = t2a
      result (fsuc (fsuc fzero)) gb = nt (fsuc (fsuc fzero))
      result (fsuc (fsuc (fsuc fzero))) ga = t3a
      result (fsuc (fsuc (fsuc fzero))) gb = t3b
      result (fsuc (fsuc (fsuc (fsuc fzero)))) ga = nt (fsuc (fsuc (fsuc fzero)))
      result (fsuc (fsuc (fsuc (fsuc fzero)))) gb = t4b
      result (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) ga = nt (fsuc (fsuc (fsuc (fsuc fzero))))
      result (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) gb = t5b
      result (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) ga = nt (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
      result (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) gb = nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
      result (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) ga = nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
      result (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) gb = t7b
      result (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) ga = nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
      result (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) gb = nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
      result (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) ga = nt (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))))
      result (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) gb = t9b
      result (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))))))) g
