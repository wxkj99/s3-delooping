{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- All action coherences are
-- supplied by dependent definitions on B = 2-EltType₀.
module DeloopS3.Seifert.TwistedBundle.Coherent where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Data.NatMinusOne
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (Unit; tt; isContr→≃Unit)
open import Cubical.Data.Bool using (false)
open import Cubical.Data.Int using (ℤ)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import Cubical.HITs.Pushout.Flattening using (module FlatteningLemma)
open import Cubical.HITs.RPn.Base using (Bool*; 2-EltPointed₀; isContr-2-EltPointed; cov⁻¹)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Move.CancelMinimal using (C; mulC; _+C_; Σ-over-equiv)
open import DeloopS3.Seifert.TwistedBundle.SignCircle
open import DeloopS3.Seifert.TwistedBundle.Base using (R; w₁; A; pr₁; cap; fA)
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)

Â : B → Type₁
Â T = Σ R (λ x → w₁ x ≡ T)

Reg : B → Type
Reg = fst

SAct : B → Type₁
SAct T = Pushout {A = Â T × Reg T} fst snd

backPoint : (T : B) → Â T → Reg T → A
backPoint T (x , p) y = x , subst Reg (sym p) y

module Action (e : ℤ) where
  clutching : (T : B) → Â T → Reg T → SignC T
  clutching T a y = invEq (ε T y) (mulC e (fA .fst (backPoint T a y)))

  FAct : (T : B) → SAct T → Type
  FAct T (inl a) = SignC T
  FAct T (inr y) = SignC T
  FAct T (push (a , y) i) = ua (rot {T = T} (clutching T a y)) i

  module Fibrewise (T : B) where
    module Flat = FlatteningLemma {A = Â T × Reg T} fst snd
      (λ _ → SignC T) (λ _ → SignC T)
      (λ { (a , y) → rot {T = T} (clutching T a y) })

    family-flat : (s : SAct T) → FAct T s ≃ Flat.E s
    family-flat (inl a) = idEquiv _
    family-flat (inr y) = idEquiv _
    family-flat (push z i) = idEquiv _

    flattenAction : Σ (SAct T) (FAct T) ≃ Pushout Flat.Σf Flat.Σg
    flattenAction = compEquiv (Σ-cong-equiv-snd family-flat) Flat.flatten

  -- This is the complete seam equation, as a dependent function
  -- of T,p,y,t; it is not only an equality on homotopy groups.
  clutching-seam : (T : B) (a : Â T) (y : Reg T) (t : SignC T)
    → ε T y .fst (_+S_ {T = T} t (clutching T a y))
      ≡ ε T y .fst t +C mulC e (fA .fst (backPoint T a y))
  clutching-seam T a y t = ε-add T y t (clutching T a y)
    ∙ cong (ε T y .fst t +C_)
      (secEq (ε T y) (mulC e (fA .fst (backPoint T a y))))

QuotientBase : Type₁
QuotientBase = Σ B SAct

Left : Type₁
Left = Σ B Â

Right : Type₁
Right = Σ B Reg

Overlap : Type₁
Overlap = Σ B (λ T → Â T × Reg T)

qLeft : Overlap → Left
qLeft (T , a , y) = T , a

qRight : Overlap → Right
qRight (T , a , y) = T , y

-- Dependent sums distribute over the fibrewise pushout; both inverse
-- homotopies retain the push constructor, not just the vertices.
quotientSpan : QuotientBase ≃ Pushout qLeft qRight
quotientSpan = isoToEquiv (iso to from sec ret)
  where
  to : QuotientBase → Pushout qLeft qRight
  to (T , inl a) = inl (T , a)
  to (T , inr y) = inr (T , y)
  to (T , push (a , y) i) = push (T , a , y) i
  from : Pushout qLeft qRight → QuotientBase
  from (inl (T , a)) = T , inl a
  from (inr (T , y)) = T , inr y
  from (push (T , a , y) i) = T , push (a , y) i
  sec : (z : Pushout qLeft qRight) → to (from z) ≡ z
  sec (inl z) = refl
  sec (inr z) = refl
  sec (push z i) = refl
  ret : (z : QuotientBase) → from (to z) ≡ z
  ret (T , inl a) = refl
  ret (T , inr y) = refl
  ret (T , push z i) = refl

leftChart : Left ≃ R
leftChart = isoToEquiv (iso (λ { (T , x , p) → x })
  (λ x → w₁ x , x , refl) (λ _ → refl)
  (λ { (T , x , p) i → p i , x , (λ j → p (i ∧ j)) }))

rightContractible : isContr Right
rightContractible = isOfHLevelRetractFromIso 0 chart isContr-2-EltPointed
  where
  chart : Iso Right 2-EltPointed₀
  chart = iso (λ { ((X , h) , y) → X , y , h })
    (λ { (X , y , h) → (X , h) , y }) (λ _ → refl) (λ _ → refl)

rightChart : Right ≃ Unit
rightChart = isContr→≃Unit rightContractible

overlapChart : Overlap ≃ A
overlapChart = isoToEquiv (iso to from sec ret)
  where
  to : Overlap → A
  to (T , a , y) = backPoint T a y
  from : A → Overlap
  from (x , z) = w₁ x , (x , refl) , z
  sec : (a : A) → to (from a) ≡ a
  sec (x , z) = ΣPathP (refl , transportRefl z)
  ret : (z : Overlap) → from (to z) ≡ z
  ret (T , (x , p) , y) = J
    (λ T p → (y : Reg T) → from (to (T , (x , p) , y)) ≡ (T , (x , p) , y))
    (λ y → cong {A = Reg (w₁ x)} {B = λ _ → Overlap}
      (λ z → w₁ x , (x , refl) , z) (transportRefl y)) p y

quotientMap : QuotientBase → RP²
quotientMap (T , inl (x , p)) = inl x
quotientMap (T , inr y) = inr tt
quotientMap (T , push (a , y) i) = push (backPoint T a y) i

abstract
  baseQuotient : QuotientBase ≃ RP²
  baseQuotient = compEquiv quotientSpan
    (pushoutEquiv qLeft qRight pr₁ cap overlapChart leftChart rightChart refl refl)

  framePath : (T : B) (y : Reg T) → T ≡ Bool*
  framePath T y i = ua (frame T y) i , isProp→PathP
    (λ i → PT.squash₁ {A = ua (frame T y) i ≃ _})
    (snd T) PT.∣ idEquiv _ ∣₁ i

  -- The seam square. Path induction also retains its
  -- dependence on p and y, and hence all higher action instances.
  frameSquare : (x : R) {T : B} (p : w₁ x ≡ T) (y : Reg T)
    → Square (sym p) (framePath T y) refl
        (framePath (w₁ x) (subst Reg (sym p) y))
  frameSquare x p = J
    (λ T p → (y : Reg T) → Square (sym p) (framePath T y) refl
      (framePath (w₁ x) (subst Reg (sym p) y)))
    (λ y → compPath→Square
      (cong (refl ∙_) (cong (framePath (w₁ x)) (sym (transportRefl y))))) p

  quotientMap-over : (s : QuotientBase) → fst s ≡ cov⁻¹ 2 (quotientMap s)
  quotientMap-over (T , inl (x , p)) = sym p
  quotientMap-over (T , inr y) = framePath T y
  quotientMap-over (T , push ((x , p) , y) i) = frameSquare x p y i

  quotient-agrees : (s : QuotientBase) → baseQuotient .fst s ≡ quotientMap s
  quotient-agrees (T , inl a) = refl
  quotient-agrees (T , inr y) = refl
  quotient-agrees (T , push (a , y) i) j = normalize (push (backPoint T a y)) j i
    where
    normalize : ∀ {ℓ} {X : Type ℓ} {x y : X} (p : x ≡ y)
      → refl ∙∙ p ∙∙ refl ≡ p
    normalize p = doubleCompPath-elim refl p refl
      ∙ sym (rUnit (refl ∙ p)) ∙ sym (lUnit p)

  baseQuotient-over : (s : QuotientBase) → fst s ≡ cov⁻¹ 2 (baseQuotient .fst s)
  baseQuotient-over s = quotientMap-over s
    ∙ cong (cov⁻¹ 2) (sym (quotient-agrees s))

  -- The cover is the ACTUAL recursive library cover, not a separately
  -- chosen two-fold covering space with an unspecified classifier.
  coverTotalEquiv : Σ QuotientBase (Reg ∘ fst) ≃ Σ RP² (Reg ∘ cov⁻¹ 2)
  coverTotalEquiv = Σ-over-equiv Reg {m = fst} {n = cov⁻¹ 2}
    (baseQuotient , baseQuotient-over)

  coverTotal-over : (s : Σ QuotientBase (Reg ∘ fst))
    → fst (coverTotalEquiv .fst s) ≡ baseQuotient .fst (fst s)
  coverTotal-over s = refl

  baseQuotient-cap : baseQuotient .fst (Bool* , inr false) ≡ inr tt
  baseQuotient-cap = refl

-- The small family lives in Type although the action base lives in Type₁.
-- No resizing is used.
module Descended (e : ℤ) where
  open Action e

  Fdescent : RP² → Type
  Fdescent b = FAct (fst (invEq baseQuotient b)) (snd (invEq baseQuotient b))

  Mdescent : Type
  Mdescent = Σ RP² Fdescent

  pdescent : Mdescent → RP²
  pdescent = fst

  action-circle : (T : B) (s : SAct T) → PT.∥ FAct T s ≃ C ∥₁
  action-circle T (inl a) = sign-circle T
  action-circle T (inr y) = sign-circle T
  action-circle T (push (a , y) i) = isProp→PathP
    (λ i → PT.squash₁ {A = FAct T (push (a , y) i) ≃ C})
    (sign-circle T) (sign-circle T) i

  descent-circle : (b : RP²) → PT.∥ Fdescent b ≃ C ∥₁
  descent-circle b = action-circle (fst (invEq baseQuotient b))
    (snd (invEq baseQuotient b))
