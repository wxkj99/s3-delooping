{-# OPTIONS --cubical --safe #-}
module DeloopS3.Assembly.DefB where

-- Construct the delooping from a natural diagram of localized loop spaces
-- using arithmetic fracture. Assembly.Final supplies the geometric data;
-- the final loop equivalence is pointed by a translation in its source.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path
  using (flipSquareEquiv ; compPathlEquiv ; compPathrEquiv)
open import Cubical.Foundations.GroupoidLaws using (rUnit)
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma using (_×_ ; Σ-cong-equiv ; Σ-cong-equiv-snd)
open import Cubical.Homotopy.Connected using (isConnected ; isConnectedPath)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (north)
open import DeloopS3.Local.Base using (L)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations
  using (PB ; connected-Σ)
open import DeloopS3.Local.Fracture.Fracture.Maps
  using (ι_m ; ι_n ; fracture-unit)
open import DeloopS3.Local.Fracture.Fracture
  using (arithmetic-fracture-S³)

-- This operation changes the underlying equivalence by a translation in
-- its SOURCE loop space. It requires no pointedness/coherence of e.
-- We claim a pointed equivalence, not that its underlying map is e.
abstract
  point-loop-equivalence : (X Y : Pointed ℓ-zero)
    → typ (Ω X) ≃ typ Y → Ω X ≃∙ Y
  point-loop-equivalence X Y e =
    compEquiv (compPathlEquiv r) e ,
    (cong (equivFun e) (sym (rUnit r)) ∙ secEq e (pt Y))
    where
    r : pt X ≡ pt X
    r = invEq e (pt Y)

  -- Equivalence of cospans, with PATH-valued commuting squares.
  PB-cong : {A B C A' B' C' : Type}
    (f : A → C) (g : B → C) (f' : A' → C') (g' : B' → C')
    (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C')
    (hA : (a : A) → f' (equivFun eA a) ≡ equivFun eC (f a))
    (hB : (b : B) → g' (equivFun eB b) ≡ equivFun eC (g b))
    → PB f g ≃ PB f' g'
  PB-cong {A} {B} {C} {A'} {B'} {C'} f g f' g' eA eB eC hA hB =
    Σ-cong-equiv {A = A} {A' = A'}
      {B = λ a → Σ[ b ∈ B ] f a ≡ g b}
      {B' = λ a' → Σ[ b' ∈ B' ] f' a' ≡ g' b'} eA λ a →
    Σ-cong-equiv {A = B} {A' = B'}
      {B = λ b → f a ≡ g b}
      {B' = λ b' → f' (equivFun eA a) ≡ g' b'} eB λ b →
    compEquiv (congEquiv {x = f a} {y = g b} eC)
      (compEquiv
        (compPathlEquiv {z = equivFun eC (g b)} (hA a))
        (compPathrEquiv {x = f' (equivFun eA a)} (sym (hB b))))

module _ (Q1 Q2 T : Pointed ℓ-zero)
  (u1 : Q1 →∙ T) (u2 : Q2 →∙ T) where

  -- Double composition makes the endpoint-moving square below literal.
  -- This is the usual path u1(pt Q1) -> pt T -> u2(pt Q2).
  B-seam : fst u1 (pt Q1) ≡ fst u2 (pt Q2)
  B-seam = snd u1 ∙∙ refl ∙∙ sym (snd u2)

  B-def : Pointed ℓ-zero
  B-def = PB (fst u1) (fst u2) , (pt Q1 , pt Q2 , B-seam)

  abstract
    B-connected : isConnected 2 (typ Q1) → isConnected 2 (typ Q2)
      → isConnected 3 (typ T) → isConnected 2 (typ B-def)
    B-connected c1 c2 cT = connected-Σ (typ Q1)
      (λ a → Σ[ b ∈ typ Q2 ] fst u1 a ≡ fst u2 b) c1 λ a →
      connected-Σ (typ Q2) (λ b → fst u1 a ≡ fst u2 b) c2 λ b →
      isConnectedPath 2 {A = typ T} cT (fst u1 a) (fst u2 b)

  PB-loops : Pointed ℓ-zero
  PB-loops = PB (fst (Ω→ u1)) (fst (Ω→ u2)) ,
    (refl , refl , snd (Ω→ u1) ∙ sym (snd (Ω→ u2)))

  private
    LoopSquares : Type
    LoopSquares = Σ[ a ∈ typ (Ω Q1) ] Σ[ b ∈ typ (Ω Q2) ]
      Square B-seam B-seam (cong (fst u1) a) (cong (fst u2) b)

    -- The two nested Σ-path characterizations, definitionally inverse.
    loop-squares : Iso (typ (Ω B-def)) LoopSquares
    Iso.fun loop-squares p =
      (λ i → fst (p i)) , (λ i → fst (snd (p i))) ,
      (λ i → snd (snd (p i)))
    Iso.inv loop-squares (a , b , s) i = a i , b i , s i
    Iso.sec loop-squares _ = refl
    Iso.ret loop-squares _ = refl

  abstract
    -- Move the four vertices along the pointing paths. At the far end
    -- both seams are refl, so transposing the square is a path of loops.
    square-to-loop-path : (a : typ (Ω Q1)) (b : typ (Ω Q2))
      → Square B-seam B-seam (cong (fst u1) a) (cong (fst u2) b)
        ≃ (fst (Ω→ u1) a ≡ fst (Ω→ u2) b)
    square-to-loop-path a b = compEquiv
      (pathToEquiv (λ i → Square (seam i) (seam i) (left i) (right i)))
      flipSquareEquiv
      where
      seam : (i : I) → snd u1 i ≡ snd u2 i
      seam i = doubleCompPath-filler (snd u1) refl (sym (snd u2)) (~ i)
      left : (i : I) → snd u1 i ≡ snd u1 i
      left i = doubleCompPath-filler (sym (snd u1)) (cong (fst u1) a) (snd u1) i
      right : (i : I) → snd u2 i ≡ snd u2 i
      right i = doubleCompPath-filler (sym (snd u2)) (cong (fst u2) b) (snd u2) i

    ΩB≃PB-loops-unpointed : typ (Ω B-def) ≃ typ PB-loops
    ΩB≃PB-loops-unpointed = compEquiv (isoToEquiv loop-squares)
      (Σ-cong-equiv-snd {A = typ (Ω Q1)}
        {B = λ a → Σ[ b ∈ typ (Ω Q2) ]
          Square B-seam B-seam (cong (fst u1) a) (cong (fst u2) b)}
        {B' = λ a → Σ[ b ∈ typ (Ω Q2) ] fst (Ω→ u1) a ≡ fst (Ω→ u2) b}
        (λ a → Σ-cong-equiv-snd {A = typ (Ω Q2)}
          {B = λ b → Square B-seam B-seam (cong (fst u1) a) (cong (fst u2) b)}
          {B' = λ b → fst (Ω→ u1) a ≡ fst (Ω→ u2) b}
          (square-to-loop-path a)))

    -- Pointed existence; the loop-translation adjustment is not asserted
    -- to commute with the two projections. The transfer uses the explicit
    -- UNPOINTED comparison above, and is pointed only at the last step.
    ΩB≃PB-loops : Ω B-def ≃∙ PB-loops
    ΩB≃PB-loops = point-loop-equivalence B-def PB-loops ΩB≃PB-loops-unpointed

  -- Geometry supplies these connected corners, equivalences, and actual
  -- homotopies. No naturality or basepoint coherence is silently inferred.
  record NaturalLoopData : Type where
    field
      Q1-connected : isConnected 2 (typ Q1)
      Q2-connected : isConnected 2 (typ Q2)
      T-simply-connected : isConnected 3 (typ T)
      φ1 : typ (Ω Q1) ≃ L 3 (S₊ 3)
      φ2 : typ (Ω Q2) ≃ L 10 (S₊ 3)
      φT : typ (Ω T) ≃ L 30 (S₊ 3)
      h1 : (a : typ (Ω Q1))
        → ι_m 3 10 (S₊ 3) (equivFun φ1 a) ≡ equivFun φT (fst (Ω→ u1) a)
      h2 : (b : typ (Ω Q2))
        → ι_n 3 10 (S₊ 3) (equivFun φ2 b) ≡ equivFun φT (fst (Ω→ u2) b)

  abstract
    ΩB≃fracture : NaturalLoopData
      → typ (Ω B-def) ≃ PB (ι_m 3 10 (S₊ 3)) (ι_n 3 10 (S₊ 3))
    ΩB≃fracture d = compEquiv ΩB≃PB-loops-unpointed
      (PB-cong (fst (Ω→ u1)) (fst (Ω→ u2))
        (ι_m 3 10 (S₊ 3)) (ι_n 3 10 (S₊ 3))
        (φ1 d) (φ2 d) (φT d) (h1 d) (h2 d))
      where open NaturalLoopData

    ΩB≃S³-unpointed : NaturalLoopData → typ (Ω B-def) ≃ S₊ 3
    ΩB≃S³-unpointed d = compEquiv (ΩB≃fracture d)
      (invEquiv (fracture-unit 3 10 (S₊ 3) , arithmetic-fracture-S³))

    ΩB≃S³ : NaturalLoopData → Ω B-def ≃∙ (S₊ 3 , north)
    ΩB≃S³ d = point-loop-equivalence B-def (S₊ 3 , north) (ΩB≃S³-unpointed d)

    Deloop-from-data : NaturalLoopData
      → Σ[ B ∈ Pointed ℓ-zero ] (isConnected 2 (typ B) × (Ω B ≃∙ (S₊ 3 , north)))
    Deloop-from-data d = B-def ,
      B-connected (Q1-connected d) (Q2-connected d) (T-simply-connected d) ,
      ΩB≃S³ d
      where open NaturalLoopData
