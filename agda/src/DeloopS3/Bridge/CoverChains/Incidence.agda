{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.CoverChains.Incidence where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin using (fzero; fsuc)
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms hiding (Ker)
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup using (kerGroup; kerGroup≡)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.AbGroup.Instances.Pi
open import DeloopS3.Bridge.CoverChains.OrbitSums
open import DeloopS3.Bridge.CoverChains.TreeChains
open import DeloopS3.Cert.Input.Graph.Maps using (Petal; nonTree)
open import DeloopS3.Cert.Input.Orbits using (cycleLocate; cycle-ret; cycle-start)

private
  module Z = AbGroupStr (snd ℤAbGroup)
  module ZT = GroupTheory ℤGroup

Bdy : ShortCase → Type₀
Bdy c = Σ[ k ∈ Kind ] Bd c k

Tori : ShortCase → AbGroup ℓ-zero
Tori c = ΠℤAbGroup (Bdy c)

RoseEdges : ShortCase → AbGroup ℓ-zero
RoseEdges c = ΠℤAbGroup (Petal c)

RawEdges : ShortCase → AbGroup ℓ-zero
RawEdges c = ΠℤAbGroup (Sh c × Generator)

orbit : (c : ShortCase) (k : Kind) → Sh c → Bd c k
orbit c k s = fst (cycleLocate c k s)

abstract
  orbit-representative : (c : ShortCase) (k : Kind) (b : Bd c k)
    → orbit c k (startOf c k b) ≡ b
  orbit-representative c k b = cong (orbit c k) (sym (cycle-start c k b))
    ∙ cong fst (cycle-ret c k (b , _))

  orbit-A : (c : ShortCase) (s : Sh c)
    → orbit c A (nextSheet c s ga) ≡ orbit c A s
  orbit-A octa fzero = refl
  orbit-A octa (fsuc fzero) = refl
  orbit-A octa (fsuc (fsuc fzero)) = refl
  orbit-A octa (fsuc (fsuc (fsuc ())))
  orbit-A icosa fzero = refl
  orbit-A icosa (fsuc fzero) = refl
  orbit-A icosa (fsuc (fsuc fzero)) = refl
  orbit-A icosa (fsuc (fsuc (fsuc fzero))) = refl
  orbit-A icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  orbit-A icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  orbit-A icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  orbit-A icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  orbit-A icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  orbit-A icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  orbit-A icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))

  orbit-B : (c : ShortCase) (s : Sh c)
    → orbit c B (nextSheet c s gb) ≡ orbit c B s
  orbit-B octa fzero = refl
  orbit-B octa (fsuc fzero) = refl
  orbit-B octa (fsuc (fsuc fzero)) = refl
  orbit-B octa (fsuc (fsuc (fsuc ())))
  orbit-B icosa fzero = refl
  orbit-B icosa (fsuc fzero) = refl
  orbit-B icosa (fsuc (fsuc fzero)) = refl
  orbit-B icosa (fsuc (fsuc (fsuc fzero))) = refl
  orbit-B icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  orbit-B icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  orbit-B icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  orbit-B icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  orbit-B icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  orbit-B icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  orbit-B icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))

  orbit-C-inverse-order : (c : ShortCase) (s : Sh c)
    → orbit c C (previous c s ga) ≡ orbit c C (nextSheet c s gb)
  orbit-C-inverse-order octa fzero = refl
  orbit-C-inverse-order octa (fsuc fzero) = refl
  orbit-C-inverse-order octa (fsuc (fsuc fzero)) = refl
  orbit-C-inverse-order octa (fsuc (fsuc (fsuc ())))
  orbit-C-inverse-order icosa fzero = refl
  orbit-C-inverse-order icosa (fsuc fzero) = refl
  orbit-C-inverse-order icosa (fsuc (fsuc fzero)) = refl
  orbit-C-inverse-order icosa (fsuc (fsuc (fsuc fzero))) = refl
  orbit-C-inverse-order icosa (fsuc (fsuc (fsuc (fsuc fzero)))) = refl
  orbit-C-inverse-order icosa (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = refl
  orbit-C-inverse-order icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = refl
  orbit-C-inverse-order icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = refl
  orbit-C-inverse-order icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = refl
  orbit-C-inverse-order icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = refl
  orbit-C-inverse-order icosa (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))

  orbit-A-prev : (c : ShortCase) (s : Sh c)
    → orbit c A (previous c s ga) ≡ orbit c A s
  orbit-A-prev c s = orbit-A c s

  orbit-B-prev : (c : ShortCase) (s : Sh c)
    → orbit c B (previous c s gb) ≡ orbit c B s
  orbit-B-prev c s = orbit-B c (nextSheet c s gb) ∙ orbit-B c s

sheetValue : (c : ShortCase) → fst (Tori c) → Kind → Sh c → ℤ
sheetValue c x k s = x (k , orbit c k s)

-- Each positive a/b edge occurs once in its positive-colour orbit.
-- In a C step (b inverse, then a inverse), the negative a-edge at s
-- belongs to C(s), and the negative b-edge at s belongs to C(b s).
positiveCoefficients negativeCoefficients : (c : ShortCase)
  → AbGroupHom (Tori c) (RawEdges c)
fst (positiveCoefficients c) x (s , ga) = sheetValue c x A s
fst (positiveCoefficients c) x (s , gb) = sheetValue c x B s
snd (positiveCoefficients c) = makeIsGroupHom λ x y → funExt λ
  { (s , ga) → refl ; (s , gb) → refl }
fst (negativeCoefficients c) x (s , ga) = sheetValue c x C s
fst (negativeCoefficients c) x (s , gb) = sheetValue c x C (nextSheet c s gb)
snd (negativeCoefficients c) = makeIsGroupHom λ x y → funExt λ
  { (s , ga) → refl ; (s , gb) → refl }

rawIncidence : (c : ShortCase) → AbGroupHom (Tori c) (RawEdges c)
rawIncidence c = subtrGroupHom (Tori c) (RawEdges c)
  (positiveCoefficients c) (negativeCoefficients c)

collapseHom : (c : ShortCase) → AbGroupHom (RawEdges c) (RoseEdges c)
fst (collapseHom c) y j = y (nonTree c j)
snd (collapseHom c) = makeIsGroupHom λ x y → refl

Dhat : (c : ShortCase) → AbGroupHom (Tori c) (RoseEdges c)
Dhat c = compGroupHom (rawIncidence c) (collapseHom c)

constant : (c : ShortCase) → ℤ → fst (Tori c)
constant c t _ = t

ones : (c : ShortCase) → fst (Tori c)
ones c = constant c (pos 1)

module GC = GraphChains ℤAbGroup

abstract
  switch-negatives : (a b u v : ℤ)
    → (a Z.+ Z.- u) Z.+ (b Z.+ Z.- v)
      ≡ (a Z.+ Z.- v) Z.+ (b Z.+ Z.- u)
  switch-negatives a b u v = AbGroupTheory.comm-4 ℤAbGroup a (Z.- u) b (Z.- v)
    ∙ cong ((a Z.+ b) Z.+_) (Z.+Comm (Z.- u) (Z.- v))
    ∙ sym (AbGroupTheory.comm-4 ℤAbGroup a (Z.- v) b (Z.- u))

  raw-cycle : (c : ShortCase) (x : fst (Tori c))
    → GC.GraphCycle c (λ s g → fst (rawIncidence c) x (s , g))
  raw-cycle c x s = cong₂ Z._+_
    (cong₂ (λ a u → a Z.+ Z.- u)
      (cong (λ b → x (A , b)) (orbit-A-prev c s))
      (cong (λ b → x (C , b)) (orbit-C-inverse-order c s)))
    (cong₂ (λ b v → b Z.+ Z.- v)
      (cong (λ b → x (B , b)) (orbit-B-prev c s))
      (cong (sheetValue c x C) (next-previous c s gb)))
    ∙ switch-negatives (sheetValue c x A s) (sheetValue c x B s)
        (sheetValue c x C (nextSheet c s gb)) (sheetValue c x C s)

  raw-constant : (c : ShortCase) (t : ℤ)
    → fst (rawIncidence c) (constant c t) ≡ (λ _ → pos 0)
  raw-constant c t = funExt λ { (s , ga) → Z.+InvR t ; (s , gb) → Z.+InvR t }

  constant-cycle : (c : ShortCase) (t : ℤ)
    → fst (Dhat c) (constant c t) ≡ (λ _ → pos 0)
  constant-cycle c t = cong (fst (collapseHom c)) (raw-constant c t)

  ones-cycle : (c : ShortCase) → fst (Dhat c) (ones c) ≡ (λ _ → pos 0)
  ones-cycle c = constant-cycle c (pos 1)

  subtraction-zero : (a b : ℤ) → a Z.+ Z.- b ≡ pos 0 → a ≡ b
  subtraction-zero a b p = ZT.invUniqueL p ∙ ZT.invInv b

  raw-kernel-constant : (c : ShortCase) (x : fst (Tori c))
    → fst (rawIncidence c) x ≡ (λ _ → pos 0)
    → x ≡ constant c (sheetValue c x A (rootSheet c))
  raw-kernel-constant c x p = funExt coefficient
    where
    α β γ : Sh c → ℤ
    α = sheetValue c x A
    β = sheetValue c x B
    γ = sheetValue c x C

    αγ : (s : Sh c) → α s ≡ γ s
    αγ s = subtraction-zero (α s) (γ s) (funExt⁻ p (s , ga))

    βγ : (s : Sh c) → β s ≡ γ s
    βγ s = cong (λ b → x (B , b)) (sym (orbit-B-prev c s))
      ∙ subtraction-zero (β (previous c s gb))
          (γ (nextSheet c (previous c s gb) gb))
          (funExt⁻ p (previous c s gb , gb))
      ∙ cong γ (next-previous c s gb)

    along : (s : Sh c) (g : Generator) → γ s ≡ γ (nextSheet c s g)
    along s ga = sym (αγ s) ∙ cong (λ b → x (A , b)) (sym (orbit-A c s))
      ∙ αγ (nextSheet c s ga)
    along s gb = sym (βγ s) ∙ cong (λ b → x (B , b)) (sym (orbit-B c s))
      ∙ βγ (nextSheet c s gb)

    γ-root : (s : Sh c) → γ s ≡ α (rootSheet c)
    γ-root s = sym (tree-constant c γ along s) ∙ sym (αγ (rootSheet c))

    at-sheet : (k : Kind) (s : Sh c) → sheetValue c x k s ≡ α (rootSheet c)
    at-sheet A s = αγ s ∙ γ-root s
    at-sheet B s = βγ s ∙ γ-root s
    at-sheet C s = γ-root s

    coefficient : (b : Bdy c) → x b ≡ α (rootSheet c)
    coefficient (k , b) = cong (λ b → x (k , b)) (sym (orbit-representative c k b))
      ∙ at-sheet k (startOf c k b)

  kernel-constant : (c : ShortCase) (x : fst (Tori c))
    → fst (Dhat c) x ≡ (λ _ → pos 0)
    → x ≡ constant c (sheetValue c x A (rootSheet c))
  kernel-constant c x p = raw-kernel-constant c x
    (funExt λ { (s , g) → GC.collapse-injective-on-cycles c
      (λ s g → fst (rawIncidence c) x (s , g)) (raw-cycle c x)
      (funExt⁻ p) s g })

Ker : {G H : Group ℓ-zero} → GroupHom G H → Group ℓ-zero
Ker = kerGroup

-- Evaluation at the root A-orbit is a specified integral inverse. In
-- particular the all-ones vector is primitive, not merely nonzero.
cover-kernel : (c : ShortCase) → GroupEquiv (Ker (Dhat c)) ℤGroup
cover-kernel c = isoToEquiv coordinateIso , makeIsGroupHom (λ _ _ → refl)
  where
  coordinateIso : Iso (fst (Ker (Dhat c))) ℤ
  Iso.fun coordinateIso z = sheetValue c (fst z) A (rootSheet c)
  Iso.inv coordinateIso t = constant c t , constant-cycle c t
  Iso.sec coordinateIso t = refl
  Iso.ret coordinateIso (x , p) = kerGroup≡ (Dhat c) (sym (kernel-constant c x p))

cover-kernel-ones : (c : ShortCase)
  → invEq (fst (cover-kernel c)) (pos 1) ≡ (ones c , ones-cycle c)
cover-kernel-ones c = kerGroup≡ (Dhat c) refl
