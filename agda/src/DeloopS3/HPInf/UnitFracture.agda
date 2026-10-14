{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.HPInf.UnitFracture where

-- Relative fracture recognizes the supplied cone, including its seam.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.GroupoidLaws using (lUnit)
open import Cubical.Foundations.Path using (compPathlEquiv; compPathrEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (Σ-cong-equiv; ΣPathP)
open import Cubical.Homotopy.Connected using (isConnected)
import Cubical.HITs.Localization.Properties as Loc
import DeloopS3.Local.Base as Base
open Base using (Local; L; η)
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Local.Fracture.Overlap using (product-locality)
open import DeloopS3.Local.Fracture.Arithmetic.Bezout using (bezout-3-10)
open import DeloopS3.Local.Fracture.Fracture using
  (PB; ι_m; ι_n; fracture-unit; arithmetic-fracture-2-connected)

local-extension : (m : ℕ) {A X : Type}
  → Local m X → (A → X) → L m A → X
local-extension m {A} {X} = Loc.rec {F = Base.F m} {X = A} {Y = X}

-- Its forward function stays transparent, unlike DefB.PB-cong.
pullback-cong : {A B C A' B' C' : Type}
  (f : A → C) (g : B → C) (f' : A' → C') (g' : B' → C')
  (eA : A ≃ A') (eB : B ≃ B') (eC : C ≃ C')
  (hA : (a : A) → f' (equivFun eA a) ≡ equivFun eC (f a))
  (hB : (b : B) → g' (equivFun eB b) ≡ equivFun eC (g b))
  → PB f g ≃ PB f' g'
pullback-cong {A} {B} {C} {A'} {B'} {C'} f g f' g' eA eB eC hA hB =
  Σ-cong-equiv {A = A} {A' = A'}
    {B = λ a → Σ[ b ∈ B ] f a ≡ g b}
    {B' = λ a' → Σ[ b' ∈ B' ] f' a' ≡ g' b'} eA λ a →
  Σ-cong-equiv {A = B} {A' = B'}
    {B = λ b → f a ≡ g b}
    {B' = λ b' → f' (equivFun eA a) ≡ g' b'} eB λ b →
  compEquiv (congEquiv {x = f a} {y = g b} eC)
    (compEquiv
      (compPathrEquiv {x = equivFun eC (f a)} (sym (hB b)))
      (compPathlEquiv {z = g' (equivFun eB b)} (hA a)))

module Recognition {F X3 X10 X30 : Type}
  (a : X3 → X30) (b : X10 → X30)
  (c3 : F → X3) (c10 : F → X10)
  (γ : (z : F) → a (c3 z) ≡ b (c10 z))
  (l3 : Local 3 X3) (l10 : Local 10 X10) (l30 : Local 30 X30) where

  c : F → PB a b
  c z = c3 z , c10 z , γ z

  e3 : L 3 F → X3
  e3 = local-extension 3 l3 c3

  e10 : L 10 F → X10
  e10 = local-extension 10 l10 c10

  e30 : L 30 F → X30
  e30 = local-extension 30 l30 (a ∘ c3)

  private
    l30-as-3 : Local 3 X30
    l30-as-3 = fst (equivFun (product-locality 3 10 X30) l30)

    l30-as-10 : Local 10 X30
    l30-as-10 = snd (equivFun (product-locality 3 10 X30) l30)

  left-square : (x : L 3 F) → a (e3 x) ≡ e30 (ι_m 3 10 F x)
  left-square = Unique.≡onη {F = Base.F 3} {X = F} {Y = X30}
    l30-as-3 (a ∘ e3) (e30 ∘ ι_m 3 10 F) (λ _ → refl)

  right-square : (y : L 10 F) → b (e10 y) ≡ e30 (ι_n 3 10 F y)
  right-square = Unique.≡onη {F = Base.F 10} {X = F} {Y = X30}
    l30-as-10 (b ∘ e10) (e30 ∘ ι_n 3 10 F) (λ z → sym (γ z))

  comparison : PB (ι_m 3 10 F) (ι_n 3 10 F) → PB a b
  comparison (x , y , s) = e3 x , e10 y ,
    left-square x ∙ cong e30 s ∙ sym (right-square y)

  abstract
    comparison-isEquiv : isEquiv e3 → isEquiv e10 → isEquiv e30
      → isEquiv comparison
    comparison-isEquiv q3 q10 q30 = snd
      (pullback-cong (ι_m 3 10 F) (ι_n 3 10 F) a b
        (e3 , q3) (e10 , q10) (e30 , q30) left-square right-square)

    comparison-unit : (z : F) → comparison (fracture-unit 3 10 F z) ≡ c z
    comparison-unit z = ΣPathP (refl , ΣPathP (refl ,
      (sym (lUnit (refl ∙ γ z)) ∙ sym (lUnit (γ z)))))

    recognize : isConnected 4 F
      → isEquiv e3 → isEquiv e10 → isEquiv e30 → isEquiv c
    recognize connected q3 q10 q30 = subst isEquiv
      (funExt comparison-unit)
      (snd (compEquiv
        (fracture-unit 3 10 F ,
          arithmetic-fracture-2-connected 3 10 F connected bezout-3-10)
        (comparison , comparison-isEquiv q3 q10 q30)))

unit-aware-fracture : {F X3 X10 X30 : Type}
  (a : X3 → X30) (b : X10 → X30)
  (c3 : F → X3) (c10 : F → X10)
  (γ : (z : F) → a (c3 z) ≡ b (c10 z))
  (l3 : Local 3 X3) (l10 : Local 10 X10) (l30 : Local 30 X30)
  → isConnected 4 F
  → isEquiv (local-extension 3 l3 c3)
  → isEquiv (local-extension 10 l10 c10)
  → isEquiv (local-extension 30 l30 (a ∘ c3))
  → isEquiv (λ z → c3 z , c10 z , γ z)
unit-aware-fracture = Recognition.recognize
