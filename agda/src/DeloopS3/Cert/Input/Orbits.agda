{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Orbits where

-- Ordered, exhaustive cyclic coordinates with the original moduli.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
import Cubical.Data.Nat as N
open import Cubical.Data.Bool using (Bool; true; _and_)
open import Cubical.Data.Unit using (tt)
import Cubical.Data.Empty as Empty
import Cubical.Data.Fin as F
import Cubical.Data.SumFin as SF
open SF using (fzero; fsuc)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group.Base using (Group₀; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom; IsGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·)
open import Cubical.Algebra.SymmetricGroup using (SymGroup)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Groups.FiniteReflection using (allFin; allFin-sound)
open import DeloopS3.Groups.TablePermutation using (natEq-sound; and-left; and-right; tablePermutation-value)
open import DeloopS3.Cert.Input.Model.Vocabulary
open import DeloopS3.Cert.Input.Model.Finite using (firstSheet-value)
open import DeloopS3.Cert.Input.Sheets
open import DeloopS3.Cover.CyclicResidue public
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Interpret.Short as Short
import DeloopS3.Cover.CircleOrbit as CO

-- All finite quantification is reduced to proof-free SumFin enumeration.
allF : (n : ℕ) → (F.Fin n → Bool) → Bool
allF n p = allFin {n = n} (λ i → p (SF.SumFin→Fin {k = n} i))

abstract
  allF-sound : (n : ℕ) (p : F.Fin n → Bool)
    → allF n p ≡ true → (i : F.Fin n) → p i ≡ true
  allF-sound n p ok i = sym (cong p (SF.Fin→SumFin→Fin {k = n} i))
    ∙ allFin-sound {n = n} (λ j → p (SF.SumFin→Fin {k = n} j)) ok (SF.Fin→SumFin {k = n} i)

Cyclic : ℕ → Group₀
Cyclic m = ℤGroup/ suc m

Coord : (c : ShortCase) → Ch.Kind → Type₀
Coord c k = Σ[ b ∈ Bd c k ] F.Fin (suc (ellPred c k b))

-- The code equality checks both coordinates, not just an orbit length.
coordEq : (c : ShortCase) (k : Ch.Kind) → Coord c k → Coord c k → Bool
coordEq c k (b , q) (b′ , q′) = (SF.toℕ b ≡ᵇ SF.toℕ b′) and (q .fst ≡ᵇ q′ .fst)

abstract
  dependent-fin-ext : {n : ℕ} (l : SF.Fin n → ℕ)
    (x y : Σ[ b ∈ SF.Fin n ] F.Fin (l b))
    → x .fst ≡ y .fst → x .snd .fst ≡ y .snd .fst → x ≡ y
  dependent-fin-ext l (b , q) (b′ , q′) e = J
    (λ b′ e → (q′ : F.Fin (l b′)) → q .fst ≡ q′ .fst → (b , q) ≡ (b′ , q′))
    (λ q′ p → cong (b ,_) (F.toℕ-injective {k = l b} p)) e q′

  coordEq-sound : (c : ShortCase) (k : Ch.Kind) (x y : Coord c k)
    → coordEq c k x y ≡ true → x ≡ y
  coordEq-sound c k x y p = dependent-fin-ext (λ b → suc (ellPred c k b)) x y
    (SF.toℕ-injective (natEq-sound _ _ (and-left p)))
    (natEq-sound _ _ (and-right {a = SF.toℕ (x .fst) ≡ᵇ SF.toℕ (y .fst)} p))

-- Literal lists in Bd order, with no default sheet.
cycleEntry : (c : ShortCase) (k : Ch.Kind) → Coord c k → Sh c
cycleEntry octa Ch.A (fzero , (0 , p)) = fzero
cycleEntry octa Ch.A (fzero , (1 , p)) = (fsuc fzero)
cycleEntry octa Ch.A (fzero , (suc (suc (q)) , p)) = Empty.rec p
cycleEntry octa Ch.A ((fsuc fzero) , (0 , p)) = (fsuc (fsuc fzero))
cycleEntry octa Ch.A ((fsuc fzero) , (suc (q) , p)) = Empty.rec p
cycleEntry octa Ch.A ((fsuc (fsuc ())) , q)
cycleEntry octa Ch.B (fzero , (0 , p)) = fzero
cycleEntry octa Ch.B (fzero , (1 , p)) = (fsuc (fsuc fzero))
cycleEntry octa Ch.B (fzero , (2 , p)) = (fsuc fzero)
cycleEntry octa Ch.B (fzero , (suc (suc (suc (q))) , p)) = Empty.rec p
cycleEntry octa Ch.B ((fsuc ()) , q)
cycleEntry octa Ch.C (fzero , (0 , p)) = fzero
cycleEntry octa Ch.C (fzero , (suc (q) , p)) = Empty.rec p
cycleEntry octa Ch.C ((fsuc fzero) , (0 , p)) = (fsuc fzero)
cycleEntry octa Ch.C ((fsuc fzero) , (1 , p)) = (fsuc (fsuc fzero))
cycleEntry octa Ch.C ((fsuc fzero) , (suc (suc (q)) , p)) = Empty.rec p
cycleEntry octa Ch.C ((fsuc (fsuc ())) , q)
cycleEntry icosa Ch.A (fzero , (0 , p)) = fzero
cycleEntry icosa Ch.A (fzero , (1 , p)) = (fsuc fzero)
cycleEntry icosa Ch.A (fzero , (suc (suc (q)) , p)) = Empty.rec p
cycleEntry icosa Ch.A ((fsuc fzero) , (0 , p)) = (fsuc (fsuc fzero))
cycleEntry icosa Ch.A ((fsuc fzero) , (1 , p)) = (fsuc (fsuc (fsuc (fsuc fzero))))
cycleEntry icosa Ch.A ((fsuc fzero) , (suc (suc (q)) , p)) = Empty.rec p
cycleEntry icosa Ch.A ((fsuc (fsuc fzero)) , (0 , p)) = (fsuc (fsuc (fsuc fzero)))
cycleEntry icosa Ch.A ((fsuc (fsuc fzero)) , (1 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
cycleEntry icosa Ch.A ((fsuc (fsuc fzero)) , (suc (suc (q)) , p)) = Empty.rec p
cycleEntry icosa Ch.A ((fsuc (fsuc (fsuc fzero))) , (0 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
cycleEntry icosa Ch.A ((fsuc (fsuc (fsuc fzero))) , (1 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
cycleEntry icosa Ch.A ((fsuc (fsuc (fsuc fzero))) , (suc (suc (q)) , p)) = Empty.rec p
cycleEntry icosa Ch.A ((fsuc (fsuc (fsuc (fsuc fzero)))) , (0 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
cycleEntry icosa Ch.A ((fsuc (fsuc (fsuc (fsuc fzero)))) , (suc (q) , p)) = Empty.rec p
cycleEntry icosa Ch.A ((fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) , (0 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
cycleEntry icosa Ch.A ((fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) , (suc (q) , p)) = Empty.rec p
cycleEntry icosa Ch.A ((fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ())))))) , q)
cycleEntry icosa Ch.B (fzero , (0 , p)) = fzero
cycleEntry icosa Ch.B (fzero , (suc (q) , p)) = Empty.rec p
cycleEntry icosa Ch.B ((fsuc fzero) , (0 , p)) = (fsuc fzero)
cycleEntry icosa Ch.B ((fsuc fzero) , (1 , p)) = (fsuc (fsuc fzero))
cycleEntry icosa Ch.B ((fsuc fzero) , (2 , p)) = (fsuc (fsuc (fsuc fzero)))
cycleEntry icosa Ch.B ((fsuc fzero) , (suc (suc (suc (q))) , p)) = Empty.rec p
cycleEntry icosa Ch.B ((fsuc (fsuc fzero)) , (0 , p)) = (fsuc (fsuc (fsuc (fsuc fzero))))
cycleEntry icosa Ch.B ((fsuc (fsuc fzero)) , (1 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
cycleEntry icosa Ch.B ((fsuc (fsuc fzero)) , (2 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
cycleEntry icosa Ch.B ((fsuc (fsuc fzero)) , (suc (suc (suc (q))) , p)) = Empty.rec p
cycleEntry icosa Ch.B ((fsuc (fsuc (fsuc fzero))) , (0 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
cycleEntry icosa Ch.B ((fsuc (fsuc (fsuc fzero))) , (1 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
cycleEntry icosa Ch.B ((fsuc (fsuc (fsuc fzero))) , (2 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
cycleEntry icosa Ch.B ((fsuc (fsuc (fsuc fzero))) , (suc (suc (suc (q))) , p)) = Empty.rec p
cycleEntry icosa Ch.B ((fsuc (fsuc (fsuc (fsuc ())))) , q)
cycleEntry icosa Ch.C (fzero , (0 , p)) = fzero
cycleEntry icosa Ch.C (fzero , (1 , p)) = (fsuc fzero)
cycleEntry icosa Ch.C (fzero , (2 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))
cycleEntry icosa Ch.C (fzero , (3 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))
cycleEntry icosa Ch.C (fzero , (4 , p)) = (fsuc (fsuc fzero))
cycleEntry icosa Ch.C (fzero , (suc (suc (suc (suc (suc (q))))) , p)) = Empty.rec p
cycleEntry icosa Ch.C ((fsuc fzero) , (0 , p)) = (fsuc (fsuc (fsuc fzero)))
cycleEntry icosa Ch.C ((fsuc fzero) , (1 , p)) = (fsuc (fsuc (fsuc (fsuc fzero))))
cycleEntry icosa Ch.C ((fsuc fzero) , (2 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))
cycleEntry icosa Ch.C ((fsuc fzero) , (3 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))))
cycleEntry icosa Ch.C ((fsuc fzero) , (4 , p)) = (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))
cycleEntry icosa Ch.C ((fsuc fzero) , (suc (suc (suc (suc (suc (q))))) , p)) = Empty.rec p
cycleEntry icosa Ch.C ((fsuc (fsuc ())) , q)

cycleLocate : (c : ShortCase) (k : Ch.Kind) → Sh c → Coord c k
cycleLocate octa Ch.A fzero = fzero , (0 , tt)
cycleLocate octa Ch.A (fsuc fzero) = fzero , (1 , tt)
cycleLocate octa Ch.A (fsuc (fsuc fzero)) = (fsuc fzero) , (0 , tt)
cycleLocate octa Ch.A (fsuc (fsuc (fsuc ())))
cycleLocate octa Ch.B fzero = fzero , (0 , tt)
cycleLocate octa Ch.B (fsuc (fsuc fzero)) = fzero , (1 , tt)
cycleLocate octa Ch.B (fsuc fzero) = fzero , (2 , tt)
cycleLocate octa Ch.B (fsuc (fsuc (fsuc ())))
cycleLocate octa Ch.C fzero = fzero , (0 , tt)
cycleLocate octa Ch.C (fsuc fzero) = (fsuc fzero) , (0 , tt)
cycleLocate octa Ch.C (fsuc (fsuc fzero)) = (fsuc fzero) , (1 , tt)
cycleLocate octa Ch.C (fsuc (fsuc (fsuc ())))
cycleLocate icosa Ch.A fzero = fzero , (0 , tt)
cycleLocate icosa Ch.A (fsuc fzero) = fzero , (1 , tt)
cycleLocate icosa Ch.A (fsuc (fsuc fzero)) = (fsuc fzero) , (0 , tt)
cycleLocate icosa Ch.A (fsuc (fsuc (fsuc (fsuc fzero)))) = (fsuc fzero) , (1 , tt)
cycleLocate icosa Ch.A (fsuc (fsuc (fsuc fzero))) = (fsuc (fsuc fzero)) , (0 , tt)
cycleLocate icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = (fsuc (fsuc fzero)) , (1 , tt)
cycleLocate icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = (fsuc (fsuc (fsuc fzero))) , (0 , tt)
cycleLocate icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = (fsuc (fsuc (fsuc fzero))) , (1 , tt)
cycleLocate icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = (fsuc (fsuc (fsuc (fsuc fzero)))) , (0 , tt)
cycleLocate icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) , (0 , tt)
cycleLocate icosa Ch.A (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))
cycleLocate icosa Ch.B fzero = fzero , (0 , tt)
cycleLocate icosa Ch.B (fsuc fzero) = (fsuc fzero) , (0 , tt)
cycleLocate icosa Ch.B (fsuc (fsuc fzero)) = (fsuc fzero) , (1 , tt)
cycleLocate icosa Ch.B (fsuc (fsuc (fsuc fzero))) = (fsuc fzero) , (2 , tt)
cycleLocate icosa Ch.B (fsuc (fsuc (fsuc (fsuc fzero)))) = (fsuc (fsuc fzero)) , (0 , tt)
cycleLocate icosa Ch.B (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = (fsuc (fsuc fzero)) , (1 , tt)
cycleLocate icosa Ch.B (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = (fsuc (fsuc fzero)) , (2 , tt)
cycleLocate icosa Ch.B (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = (fsuc (fsuc (fsuc fzero))) , (0 , tt)
cycleLocate icosa Ch.B (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = (fsuc (fsuc (fsuc fzero))) , (1 , tt)
cycleLocate icosa Ch.B (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = (fsuc (fsuc (fsuc fzero))) , (2 , tt)
cycleLocate icosa Ch.B (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))
cycleLocate icosa Ch.C fzero = fzero , (0 , tt)
cycleLocate icosa Ch.C (fsuc fzero) = fzero , (1 , tt)
cycleLocate icosa Ch.C (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))) = fzero , (2 , tt)
cycleLocate icosa Ch.C (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))) = fzero , (3 , tt)
cycleLocate icosa Ch.C (fsuc (fsuc fzero)) = fzero , (4 , tt)
cycleLocate icosa Ch.C (fsuc (fsuc (fsuc fzero))) = (fsuc fzero) , (0 , tt)
cycleLocate icosa Ch.C (fsuc (fsuc (fsuc (fsuc fzero)))) = (fsuc fzero) , (1 , tt)
cycleLocate icosa Ch.C (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))) = (fsuc fzero) , (2 , tt)
cycleLocate icosa Ch.C (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero))))))))) = (fsuc fzero) , (3 , tt)
cycleLocate icosa Ch.C (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc fzero)))))))) = (fsuc fzero) , (4 , tt)
cycleLocate icosa Ch.C (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc (fsuc ()))))))))))

cycle-ret-check cycle-sec-check cycle-start-check : (c : ShortCase) (k : Ch.Kind) → Bool
cycle-ret-check c k = allFin (λ b → allF (suc (ellPred c k b)) (λ q →
  coordEq c k (cycleLocate c k (cycleEntry c k (b , q))) (b , q)))
cycle-sec-check c k = allFin (λ x →
  SF.toℕ (cycleEntry c k (cycleLocate c k x)) ≡ᵇ SF.toℕ x)
cycle-start-check c k = allFin (λ b →
  SF.toℕ (cycleEntry c k (b , F.fzero)) ≡ᵇ SF.toℕ (startOf c k b))

abstract
  cycle-ret-ok : (c : ShortCase) (k : Ch.Kind) → cycle-ret-check c k ≡ true
  cycle-sec-ok : (c : ShortCase) (k : Ch.Kind) → cycle-sec-check c k ≡ true
  cycle-start-ok : (c : ShortCase) (k : Ch.Kind) → cycle-start-check c k ≡ true
  cycle-ret-ok octa Ch.A = refl
  cycle-ret-ok octa Ch.B = refl
  cycle-ret-ok octa Ch.C = refl
  cycle-ret-ok icosa Ch.A = refl
  cycle-ret-ok icosa Ch.B = refl
  cycle-ret-ok icosa Ch.C = refl
  cycle-sec-ok octa Ch.A = refl
  cycle-sec-ok octa Ch.B = refl
  cycle-sec-ok octa Ch.C = refl
  cycle-sec-ok icosa Ch.A = refl
  cycle-sec-ok icosa Ch.B = refl
  cycle-sec-ok icosa Ch.C = refl
  cycle-start-ok octa Ch.A = refl
  cycle-start-ok octa Ch.B = refl
  cycle-start-ok octa Ch.C = refl
  cycle-start-ok icosa Ch.A = refl
  cycle-start-ok icosa Ch.B = refl
  cycle-start-ok icosa Ch.C = refl

  cycle-ret : (c : ShortCase) (k : Ch.Kind) (x : Coord c k)
    → cycleLocate c k (cycleEntry c k x) ≡ x
  cycle-ret c k (b , q) = coordEq-sound c k _ _
    (allF-sound (suc (ellPred c k b)) (λ q → coordEq c k (cycleLocate c k (cycleEntry c k (b , q))) (b , q))
      (allFin-sound (λ b → allF (suc (ellPred c k b)) (λ q →
        coordEq c k (cycleLocate c k (cycleEntry c k (b , q))) (b , q)))
        (cycle-ret-ok c k) b) q)

  cycle-sec : (c : ShortCase) (k : Ch.Kind) (x : Sh c)
    → cycleEntry c k (cycleLocate c k x) ≡ x
  cycle-sec c k x = SF.toℕ-injective (natEq-sound _ _
    (allFin-sound (λ x → SF.toℕ (cycleEntry c k (cycleLocate c k x)) ≡ᵇ SF.toℕ x)
      (cycle-sec-ok c k) x))

  cycle-start : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    → cycleEntry c k (b , F.fzero) ≡ startOf c k b
  cycle-start c k b = SF.toℕ-injective (natEq-sound _ _
    (allFin-sound (λ b → SF.toℕ (cycleEntry c k (b , F.fzero)) ≡ᵇ SF.toℕ (startOf c k b))
      (cycle-start-ok c k) b))

cycleCoordinates : (c : ShortCase) (k : Ch.Kind) → Coord c k ≃ Sh c
cycleCoordinates c k = isoToEquiv
  (iso (cycleEntry c k) (cycleLocate c k) (cycle-sec c k) (cycle-ret c k))

modulusPred : ShortCase → Ch.Kind → ℕ
modulusPred c Ch.A = 1
modulusPred c Ch.B = 2
modulusPred octa Ch.C = 3
modulusPred icosa Ch.C = 4

-- Reduction C_n → C_l; its finite homomorphism equations are checked below.
reduceResidue : (n l : ℕ) → F.Fin (suc n) → F.Fin (suc l)
reduceResidue n l x = CO.residue l .fst (Z.pos (x .fst))

reduction-product-check : (n l : ℕ) → Bool
reduction-product-check n l = allF (suc n) (λ x → allF (suc n) (λ y →
  reduceResidue n l (GroupStr._·_ (Cyclic n .snd) x y) .fst ≡ᵇ
  GroupStr._·_ (Cyclic l .snd) (reduceResidue n l x) (reduceResidue n l y) .fst))
reduction-generator-check : (n l : ℕ) → Bool
reduction-generator-check n l =
  reduceResidue n l (CO.residue n .fst (Z.pos 1)) .fst ≡ᵇ CO.residue l .fst (Z.pos 1) .fst

reduction-check factor-check : (c : ShortCase) (k : Ch.Kind) → Bool
reduction-check c k = allFin (λ b →
  reduction-product-check (modulusPred c k) (ellPred c k b) and
  reduction-generator-check (modulusPred c k) (ellPred c k b))
factor-check c k = allFin (λ b → suc (modulusPred c k) ≡ᵇ
  (suc (ellPred c k b) N.· suc (orderPred c k b)))

abstract
  reduction-ok : (c : ShortCase) (k : Ch.Kind) → reduction-check c k ≡ true
  factor-ok : (c : ShortCase) (k : Ch.Kind) → factor-check c k ≡ true
  reduction-ok octa Ch.A = refl
  reduction-ok octa Ch.B = refl
  reduction-ok octa Ch.C = refl
  reduction-ok icosa Ch.A = refl
  reduction-ok icosa Ch.B = refl
  reduction-ok icosa Ch.C = refl
  factor-ok octa Ch.A = refl
  factor-ok octa Ch.B = refl
  factor-ok octa Ch.C = refl
  factor-ok icosa Ch.A = refl
  factor-ok icosa Ch.B = refl
  factor-ok icosa Ch.C = refl

-- Reflection is used only for genuinely finite group tables. The next
-- module upgrades their generator comparison to a formula for EVERY z.
module Reduction (n l : ℕ)
  (product-ok : reduction-product-check n l ≡ true)
  (generator-ok : reduction-generator-check n l ≡ true) where
  abstract
    product : (x y : F.Fin (suc n))
      → reduceResidue n l (GroupStr._·_ (Cyclic n .snd) x y)
      ≡ GroupStr._·_ (Cyclic l .snd) (reduceResidue n l x) (reduceResidue n l y)
    product x y = F.toℕ-injective {k = suc l} (natEq-sound _ _
      (allF-sound (suc n) (λ y →
        reduceResidue n l (GroupStr._·_ (Cyclic n .snd) x y) .fst ≡ᵇ
        GroupStr._·_ (Cyclic l .snd) (reduceResidue n l x) (reduceResidue n l y) .fst)
        (allF-sound (suc n) (λ x → allF (suc n) (λ y →
          reduceResidue n l (GroupStr._·_ (Cyclic n .snd) x y) .fst ≡ᵇ
          GroupStr._·_ (Cyclic l .snd) (reduceResidue n l x) (reduceResidue n l y) .fst))
          product-ok x) y))
    generator : reduceResidue n l (CO.residue n .fst (Z.pos 1))
      ≡ CO.residue l .fst (Z.pos 1)
    generator = F.toℕ-injective {k = suc l} (natEq-sound _ _ generator-ok)

  hom : GroupHom (Cyclic n) (Cyclic l)
  hom = reduceResidue n l , makeIsGroupHom product

  abstract
    integer : (z : Z.ℤ) → hom .fst (CO.residue n .fst z) ≡ CO.residue l .fst z
    integer z = cong (hom .fst) (CO.residue-power n z)
      ∙ homPresℤ· hom (CO.residue n .fst (Z.pos 1)) z
      ∙ cong (λ g → z ℤ[ Cyclic l ]· g) generator
      ∙ sym (CO.residue-power l z)

module LocalReduction (c : ShortCase) (k : Ch.Kind) (b : Bd c k) where
  private
    n = modulusPred c k
    l = ellPred c k b
  abstract
    ok : reduction-product-check n l and reduction-generator-check n l ≡ true
    ok = allFin-sound (λ b →
      reduction-product-check n (ellPred c k b) and
      reduction-generator-check n (ellPred c k b)) (reduction-ok c k) b
  open Reduction n l
    (and-left {a = reduction-product-check n l} {b = reduction-generator-check n l} ok)
    (and-right {a = reduction-product-check n l} {b = reduction-generator-check n l} ok) public

-- Generic right translation and conjugation. Keeping this independent of
-- the six tables prevents conversion from expanding any semantic groups.
module CoordinateAction (B : Type₀) (l : B → ℕ)
  (X : Type₀) (setX : isSet X)
  (e : (Σ[ b ∈ B ] F.Fin (suc (l b))) ≃ X)
  (n : ℕ) (ρ : (b : B) → GroupHom (Cyclic n) (Cyclic (l b))) where

  Coordinates : Type₀
  Coordinates = Σ[ b ∈ B ] F.Fin (suc (l b))

  translate : (b : B) → F.Fin (suc (l b)) → F.Fin (suc (l b)) ≃ F.Fin (suc (l b))
  translate b a = isoToEquiv (iso (G._· a) (G._· G.inv a) sec ret)
    where
    module G = GroupStr (Cyclic (l b) .snd)
    sec : (q : F.Fin (suc (l b))) → (q G.· G.inv a) G.· a ≡ q
    sec q = sym (G.·Assoc q (G.inv a) a)
      ∙ cong (q G.·_) (G.·InvL a) ∙ G.·IdR q
    ret : (q : F.Fin (suc (l b))) → (q G.· a) G.· G.inv a ≡ q
    ret q = sym (G.·Assoc q a (G.inv a))
      ∙ cong (q G.·_) (G.·InvR a) ∙ G.·IdR q

  rotation : F.Fin (suc n) → Coordinates ≃ Coordinates
  rotation a = Σ-cong-equiv-snd (λ b → translate b (ρ b .fst a))

  permutation : F.Fin (suc n) → X ≃ X
  permutation a = compEquiv (invEquiv e) (compEquiv (rotation a) e)

  abstract
    on-coordinate : (a : F.Fin (suc n)) (u : Coordinates)
      → permutation a .fst (e .fst u) ≡ e .fst (rotation a .fst u)
    on-coordinate a u = cong (λ v → e .fst (rotation a .fst v)) (retEq e u)

    rotation-product : (a d : F.Fin (suc n)) (u : Coordinates)
      → rotation (GroupStr._·_ (Cyclic n .snd) a d) .fst u
      ≡ rotation d .fst (rotation a .fst u)
    rotation-product a d (b , q) = cong (b ,_)
      (cong (GroupStr._·_ (Cyclic (l b) .snd) q) (IsGroupHom.pres· (ρ b .snd) a d)
       ∙ GroupStr.·Assoc (Cyclic (l b) .snd) q (ρ b .fst a) (ρ b .fst d))

    preserves-product : (a d : F.Fin (suc n))
      → permutation (GroupStr._·_ (Cyclic n .snd) a d)
      ≡ compEquiv (permutation a) (permutation d)
    preserves-product a d = equivEq (funExt (λ x →
      cong (e .fst) (rotation-product a d (invEq e x))
      ∙ sym (on-coordinate d (rotation a .fst (invEq e x)))))

  action : GroupHom (Cyclic n) (SymGroup X setX)
  action = permutation , makeIsGroupHom preserves-product

  module Stabilizers (repr : B → X)
    (start : (b : B) → e .fst (b , F.fzero) ≡ repr b)
    (integer : (b : B) (z : Z.ℤ)
      → ρ b .fst (CO.residue n .fst z) ≡ CO.residue (l b) .fst z) where

    act : Z.ℤ → X → X
    act z = action .fst (CO.residue n .fst z) .fst

    abstract
      integer-coordinate : (b : B) (z : Z.ℤ) (q : F.Fin (suc (l b)))
        → act z (e .fst (b , q))
        ≡ e .fst (b , GroupStr._·_ (Cyclic (l b) .snd) q (CO.residue (l b) .fst z))
      integer-coordinate b z q = on-coordinate (CO.residue n .fst z) (b , q)
        ∙ cong (λ a → e .fst (b , GroupStr._·_ (Cyclic (l b) .snd) q a)) (integer b z)

      integer-start : (b : B) (z : Z.ℤ)
        → act z (repr b) ≡ e .fst (b , CO.residue (l b) .fst z)
      integer-start b z = cong (act z) (sym (start b))
        ∙ integer-coordinate b z F.fzero
        ∙ cong (λ q → e .fst (b , q))
            (GroupStr.·IdL (Cyclic (l b) .snd) (CO.residue (l b) .fst z))

      fixed-multiple : (b : B) (z : Z.ℤ)
        → act (Z.pos (suc (l b)) Z.· z) (repr b) ≡ repr b
      fixed-multiple b z = integer-start b (Z.pos (suc (l b)) Z.· z)
        ∙ cong (λ q → e .fst (b , q)) (residue-multiple-zero (l b) z)
        ∙ start b

      fixed-coordinates : (b d : B) (z : Z.ℤ)
        → act z (repr b) ≡ repr d
        → Path Coordinates (b , CO.residue (l b) .fst z) (d , F.fzero {k = l d})
      fixed-coordinates b d z p = sym (retEq e (b , CO.residue (l b) .fst z))
        ∙ cong (invEq e) (sym (integer-start b z) ∙ p ∙ sym (start d))
        ∙ retEq e (d , F.fzero)

      fixed-full : (b : B) (z : Z.ℤ) → act z (repr b) ≡ repr b
        → Σ[ q ∈ Z.ℤ ] Z.pos (suc (l b)) Z.· q ≡ z
      fixed-full b z p = residue-kernel (l b) z
        (F.toℕ-injective {k = suc (l b)}
          (cong (λ (u : Coordinates) → u .snd .fst) (fixed-coordinates b b z p)))

      separate : (b d : B) (z : Z.ℤ) → act z (repr b) ≡ repr d → b ≡ d
      separate b d z p = cong fst (fixed-coordinates b d z p)

      cover : (x : X) → PT.∥ Σ[ b ∈ B ] Σ[ z ∈ Z.ℤ ] act z (repr b) ≡ x ∥₁
      cover x = PT.∣ b , Z.pos (q .fst) ,
        integer-start b (Z.pos (q .fst))
        ∙ cong (λ r → e .fst (b , r)) (CO.residue-section (l b) q)
        ∙ secEq e x ∣₁
        where
        b : B
        b = invEq e x .fst
        q : F.Fin (suc (l b))
        q = invEq e x .snd

module ConcreteAction (c : ShortCase) (k : Ch.Kind) = CoordinateAction
  (Bd c k) (ellPred c k) (Sh c) SF.isSetFin (cycleCoordinates c k)
  (modulusPred c k) (LocalReduction.hom c k)
module ConcreteStabilizers (c : ShortCase) (k : Ch.Kind) = ConcreteAction.Stabilizers c k
  (startOf c k) (cycle-start c k) (LocalReduction.integer c k)

-- C is b inverse THEN a inverse. This expression deliberately uses the
-- original signed certificate tables, rather than a new action table.
letterCode : (c : ShortCase) → BaseLetter → ℕ → ℕ
letterCode c t = P.apply (Ch.actTable (Ch.action (certOf c)) (wireLetter t))
localCode : (c : ShortCase) → Ch.Kind → ℕ → ℕ
localCode c Ch.A = letterCode c a+
localCode c Ch.B = letterCode c b+
localCode c Ch.C i = letterCode c a- (letterCode c b- i)

open import DeloopS3.Cert.Input.Sheets.Action using (act-value)

abstract
  local-value : (c : ShortCase) (k : Ch.Kind) (x : Sh c)
    → SF.toℕ (CO.FinitePermutation.permutation (localPermutation (certOf c) (rawChecks c) k) .fst x)
    ≡ localCode c k (SF.toℕ x)
  local-value c Ch.A x = act-value c x a+
  local-value c Ch.B x = act-value c x b+
  local-value c Ch.C x = act-value c (actFin (certOf c) (rawChecks c) b- x) a-
    ∙ cong (letterCode c a-) (act-value c x b-)

nextCoordinate : (c : ShortCase) (k : Ch.Kind) → Coord c k → Coord c k
nextCoordinate c k (b , q) = b , GroupStr._·_ (Cyclic (ellPred c k b) .snd)
  q (CO.residue (ellPred c k b) .fst (Z.pos 1))

next-check : (c : ShortCase) (k : Ch.Kind) → Bool
next-check c k = allFin (λ b → allF (suc (ellPred c k b)) (λ q →
  SF.toℕ (cycleEntry c k (nextCoordinate c k (b , q))) ≡ᵇ
  localCode c k (SF.toℕ (cycleEntry c k (b , q)))))

abstract
  next-ok : (c : ShortCase) (k : Ch.Kind) → next-check c k ≡ true
  next-ok octa Ch.A = refl
  next-ok octa Ch.B = refl
  next-ok octa Ch.C = refl
  next-ok icosa Ch.A = refl
  next-ok icosa Ch.B = refl
  next-ok icosa Ch.C = refl

  next-entry : (c : ShortCase) (k : Ch.Kind) (u : Coord c k)
    → cycleEntry c k (nextCoordinate c k u)
    ≡ CO.FinitePermutation.permutation (localPermutation (certOf c) (rawChecks c) k) .fst (cycleEntry c k u)
  next-entry c k (b , q) = SF.toℕ-injective
    (natEq-sound _ _
      (allF-sound (suc (ellPred c k b)) (λ q →
        SF.toℕ (cycleEntry c k (nextCoordinate c k (b , q))) ≡ᵇ
        localCode c k (SF.toℕ (cycleEntry c k (b , q))))
        (allFin-sound (λ b → allF (suc (ellPred c k b)) (λ q →
          SF.toℕ (cycleEntry c k (nextCoordinate c k (b , q))) ≡ᵇ
          localCode c k (SF.toℕ (cycleEntry c k (b , q))))) (next-ok c k) b) q)
     ∙ sym (local-value c k (cycleEntry c k (b , q))))

  generator-action : (c : ShortCase) (k : Ch.Kind)
    → ConcreteAction.action c k .fst (CO.residue (modulusPred c k) .fst (Z.pos 1))
    ≡ CO.FinitePermutation.permutation (localPermutation (certOf c) (rawChecks c) k)
  generator-action c k = equivEq (funExt (λ x →
    cong (ConcreteStabilizers.act c k (Z.pos 1)) (sym (cycle-sec c k x))
    ∙ ConcreteStabilizers.integer-coordinate c k
        (cycleLocate c k x .fst) (Z.pos 1) (cycleLocate c k x .snd)
    ∙ next-entry c k (cycleLocate c k x)
    ∙ cong (CO.FinitePermutation.permutation (localPermutation (certOf c) (rawChecks c) k) .fst)
        (cycle-sec c k x)))

  orbit-factor : (c : ShortCase) (k : Ch.Kind) (b : Bd c k)
    → suc (modulusPred c k) ≡ suc (ellPred c k b) N.· suc (orderPred c k b)
  orbit-factor c k b = natEq-sound _ _ (allFin-sound (λ b →
    suc (modulusPred c k) ≡ᵇ (suc (ellPred c k b) N.· suc (orderPred c k b)))
    (factor-ok c k) b)

short-orbits : (c : ShortCase) (k : Ch.Kind)
  → CO.CyclicOrbitData (localPermutation (certOf c) (rawChecks c) k)
CO.CyclicOrbitData.modulus-1 (short-orbits c k) = modulusPred c k
CO.CyclicOrbitData.action (short-orbits c k) = ConcreteAction.action c k
CO.CyclicOrbitData.generator-action (short-orbits c k) = generator-action c k
CO.CyclicOrbitData.Rep (short-orbits c k) = Bd c k
CO.CyclicOrbitData.rep-set (short-orbits c k) = SF.isSetFin
CO.CyclicOrbitData.repr (short-orbits c k) = startOf c k
CO.CyclicOrbitData.length-1 (short-orbits c k) = ellPred c k
CO.CyclicOrbitData.order-1 (short-orbits c k) = orderPred c k
CO.CyclicOrbitData.factor (short-orbits c k) = orbit-factor c k
CO.CyclicOrbitData.fixed-multiple (short-orbits c k) = ConcreteStabilizers.fixed-multiple c k
CO.CyclicOrbitData.fixed-full (short-orbits c k) = ConcreteStabilizers.fixed-full c k
CO.CyclicOrbitData.separate (short-orbits c k) = ConcreteStabilizers.separate c k
CO.CyclicOrbitData.cover (short-orbits c k) = ConcreteStabilizers.cover c k

short-input : (c : ShortCase) → ShortInput c
ShortInput.checked (short-input c) = rawChecks c
ShortInput.sheets (short-input c) = SheetData.e (sheet-data c)
ShortInput.sheets-at-rep (short-input c) = SheetData.at-rep (sheet-data c)
ShortInput.action-square (short-input c) = SheetData.square (sheet-data c)
ShortInput.orbits (short-input c) = short-orbits c
ShortInput.orbit-index (short-input c) k = idEquiv (Bd c k)
ShortInput.orbit-start (short-input c) k b = sym (firstSheet-value c k b _)
ShortInput.orbit-length (short-input c) = ellPred-value c
ShortInput.orbit-order (short-input c) = orderPred-value c

short-orbit-modulus : (c : ShortCase) (k : Ch.Kind)
  → suc (CO.CyclicOrbitData.modulus-1 (ShortInput.orbits (short-input c) k)) ≡ localOrder c k
short-orbit-modulus c Ch.A = refl
short-orbit-modulus c Ch.B = refl
short-orbit-modulus octa Ch.C = refl
short-orbit-modulus icosa Ch.C = refl
