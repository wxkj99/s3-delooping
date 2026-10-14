{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.ProductQuotient where

-- Endpoint reduction for the selected product cellular map h × id.
-- The general naturality comparison is an equivalence of square types.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
  using (congEquiv ; preCompEquiv ; postCompEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.Susp using
  (Susp ; north ; south ; merid ; suspFun ; congSuspIso)
open import Cubical.HITs.SphereBouquet using
  (SphereBouquet ; BouquetIso-gen ; sphereBouquetSuspIso ; bouquetSusp→)
open import Cubical.CW.Base using (cofibCW ; module CWskel-fields)
open import Cubical.CW.Map using (module prefunctoriality)
open import DeloopS3.Bridge.ComponentHomology.ProductCells
  using (module RoseProduct)
open import DeloopS3.Bridge.CellularPushout.Cellular using (restrictCell)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductMaps
  using (module ProductMap)

ProductQuotientGoal : (n m : ℕ)
  (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices m))
  (h₀ : h north ≡ north) → Type
ProductQuotientGoal n m h h₀ =
  prefunctoriality.bouquetFunct 3
    (restrictCell (ProductMap.cellular n m h h₀) 3) (2 , <ᵗsuc {m = 2})
  ≡ bouquetSusp→
      (fst (RoseProduct.suspension-chart m) ∘ h
        ∘ invEq (RoseProduct.suspension-chart n))

-- Explicit source and target types for both quotient charts.
ProductCofibre : ℕ → Type
ProductCofibre n = cofibCW 2 (RoseProduct.skeleton n)

DoubleSuspension : ℕ → Type
DoubleSuspension n = Susp (Susp (RoseProduct.Vertices n))

cellular-bouquet-chart : (n : ℕ)
  → Iso (ProductCofibre n) (SphereBouquet 2 (Fin n))
cellular-bouquet-chart n = BouquetIso-gen 2
  (CWskel-fields.card (RoseProduct.skeleton n) 2)
  (CWskel-fields.α (RoseProduct.skeleton n) 2)
  (CWskel-fields.e (RoseProduct.skeleton n) 2)

double-suspension-chart : (n : ℕ)
  → Iso (DoubleSuspension n) (SphereBouquet 2 (Fin n))
double-suspension-chart n = compIso
  (congSuspIso (equivToIso (RoseProduct.suspension-chart n)))
  sphereBouquetSuspIso

quotient-suspension-chart : (n : ℕ)
  → Iso (ProductCofibre n) (DoubleSuspension n)
quotient-suspension-chart n = compIso (cellular-bouquet-chart n)
  (invIso (double-suspension-chart n))

product-cofibre-map : (n m : ℕ)
  (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices m))
  (h₀ : h north ≡ north) → ProductCofibre n → ProductCofibre m
product-cofibre-map n m h h₀ = prefunctoriality.fn+1/fn 3
  (restrictCell (ProductMap.cellular n m h h₀) 3) (2 , <ᵗsuc {m = 2})

-- The quotient square has domain cofibCW 2 (RoseProduct.skeleton n)
-- and codomain Susp (Susp (RoseProduct.Vertices m)).
ProductQuotientSquare : (n m : ℕ)
  (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices m))
  (h₀ : h north ≡ north) → Type
ProductQuotientSquare n m h h₀ =
  Iso.fun (quotient-suspension-chart m) ∘ product-cofibre-map n m h h₀
  ≡ suspFun h ∘ Iso.fun (quotient-suspension-chart n)

private
  -- This generic leaf keeps the path-space proof away from the large
  -- concrete CW equivalences.  The two endpoint cancellations are the
  -- retractions of cA and dB; no chart naturality is assumed here.
  abstract
    conjugate-square-equiv : {A B A' B' U V : Type}
      (cA : Iso A A') (cB : Iso B B')
      (dA : Iso U A') (dB : Iso V B')
      (q : A → B) (s : U → V) (t : A' → B')
      (dt : Iso.fun dB ∘ s ∘ Iso.inv dA ≡ t)
      → (Iso.fun cB ∘ q ∘ Iso.inv cA ≡ t)
      ≃ (Iso.inv dB ∘ Iso.fun cB ∘ q
           ≡ s ∘ Iso.inv dA ∘ Iso.fun cA)
    conjugate-square-equiv {A = A} {B = B} {A' = A'} {B' = B'}
      {U = U} {V = V} cA cB dA dB q s t dt =
      compEquiv (congEquiv change)
        (pathToEquiv (λ i → left-endpoint i ≡ right-endpoint i))
      where
      change : (A' → B') ≃ (A → V)
      change = compEquiv
        (postCompEquiv (isoToEquiv (invIso dB)))
        (preCompEquiv (isoToEquiv cA))

      left-endpoint : fst change (Iso.fun cB ∘ q ∘ Iso.inv cA)
        ≡ Iso.inv dB ∘ Iso.fun cB ∘ q
      left-endpoint = funExt λ x →
        cong (Iso.inv dB ∘ Iso.fun cB ∘ q) (Iso.ret cA x)

      right-endpoint : fst change t
        ≡ s ∘ Iso.inv dA ∘ Iso.fun cA
      right-endpoint = cong (fst change) (sym dt)
        ∙ funExt (λ x → Iso.ret dB (s (Iso.inv dA (Iso.fun cA x))))

    susp-conjugate : {A B C D : Type}
      (e : Iso A B) (f : Iso C D) (h : C → A)
      → Iso.fun (congSuspIso e) ∘ suspFun h ∘ Iso.inv (congSuspIso f)
        ≡ suspFun (Iso.fun e ∘ h ∘ Iso.inv f)
    susp-conjugate e f h i north = north
    susp-conjugate e f h i south = south
    susp-conjugate e f h i (merid x j) =
      merid (Iso.fun e (h (Iso.inv f x))) j

abstract
  -- This is only the right-hand-side chart calculation.  It is valid for
  -- arbitrary h, without representing h as a suspension of a vertex map.
  double-suspension-conjugate : (n m : ℕ)
    (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices m))
    → Iso.fun (double-suspension-chart m) ∘ suspFun h
        ∘ Iso.inv (double-suspension-chart n)
      ≡ bouquetSusp→
          (fst (RoseProduct.suspension-chart m) ∘ h
            ∘ invEq (RoseProduct.suspension-chart n))
  double-suspension-conjugate n m h =
    cong (λ (k : Susp (RoseProduct.Rose n) → Susp (RoseProduct.Rose m))
      → Iso.fun (sphereBouquetSuspIso {A = Fin m} {n = 1}) ∘ k
          ∘ Iso.inv (sphereBouquetSuspIso {A = Fin n} {n = 1}))
      (susp-conjugate
        (equivToIso (RoseProduct.suspension-chart m))
        (equivToIso (RoseProduct.suspension-chart n)) h)

  product-quotient-goal≃square : (n m : ℕ)
    (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices m))
    (h₀ : h north ≡ north)
    → ProductQuotientGoal n m h h₀ ≃ ProductQuotientSquare n m h h₀
  product-quotient-goal≃square n m h h₀ =
    conjugate-square-equiv
      (cellular-bouquet-chart n) (cellular-bouquet-chart m)
      (double-suspension-chart n) (double-suspension-chart m)
      (product-cofibre-map n m h h₀) (suspFun h)
      (bouquetSusp→ (fst (RoseProduct.suspension-chart m) ∘ h
        ∘ invEq (RoseProduct.suspension-chart n)))
      (double-suspension-conjugate n m h)

  product-quotient-from-square : (n m : ℕ)
    (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices m))
    (h₀ : h north ≡ north)
    → ProductQuotientSquare n m h h₀ → ProductQuotientGoal n m h h₀
  product-quotient-from-square n m h h₀ =
    invEq (product-quotient-goal≃square n m h h₀)

  product-quotient-to-square : (n m : ℕ)
    (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices m))
    (h₀ : h north ≡ north)
    → ProductQuotientGoal n m h h₀ → ProductQuotientSquare n m h h₀
  product-quotient-to-square n m h h₀ =
    fst (product-quotient-goal≃square n m h h₀)

private
  empty-bouquet-contract : (x : SphereBouquet 2 (Fin 0)) → inl tt ≡ x
  empty-bouquet-contract (inl tt) = refl
  empty-bouquet-contract (inr ((k , ()) , x))
  empty-bouquet-contract (push (k , ()) i)

abstract
  product-quotient-empty-target : (n : ℕ)
    (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices 0))
    (h₀ : h north ≡ north) → ProductQuotientGoal n 0 h h₀
  product-quotient-empty-target n h h₀ = funExt λ x →
    sym (empty-bouquet-contract
      (prefunctoriality.bouquetFunct 3
        (restrictCell (ProductMap.cellular n 0 h h₀) 3) (2 , <ᵗsuc {m = 2}) x))
    ∙ empty-bouquet-contract
        (bouquetSusp→ (fst (RoseProduct.suspension-chart 0) ∘ h
          ∘ invEq (RoseProduct.suspension-chart n)) x)

  product-quotient-empty-source : (m : ℕ)
    (h : Susp (RoseProduct.Vertices 0) → Susp (RoseProduct.Vertices m))
    (h₀ : h north ≡ north) → ProductQuotientGoal 0 m h h₀
  product-quotient-empty-source m h h₀ = funExt λ x →
    cong (prefunctoriality.bouquetFunct 3
      (restrictCell (ProductMap.cellular 0 m h h₀) 3) (2 , <ᵗsuc {m = 2}))
      (sym (empty-bouquet-contract x))
    ∙ cong (bouquetSusp→ (fst (RoseProduct.suspension-chart m) ∘ h
        ∘ invEq (RoseProduct.suspension-chart 0))) (empty-bouquet-contract x)
