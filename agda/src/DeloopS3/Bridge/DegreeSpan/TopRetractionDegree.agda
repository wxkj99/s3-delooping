{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.TopRetractionDegree where

-- Derive coefficient naturality from a quotient-level square.
-- No construction or naturality proof for the retractions is assumed here.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.HITs.Susp using
  (Susp ; north ; south ; merid ; suspFun ; congSuspIso)
open import Cubical.HITs.SphereBouquet using
  (SphereBouquet ; BouquetIso-gen ; sphereBouquetSuspIso ; bouquetSusp→)
open import Cubical.HITs.SphereBouquet.Degree using
  (bouquetDegree ; bouquetDegreeComp ; bouquetDegreeSusp)
open import Cubical.Algebra.AbGroup using (AbGroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
open import Cubical.CW.Base using (CWskel ; cofibCW)
open import Cubical.CW.Map using (cellMap ; module prefunctoriality)
open import Cubical.CW.Homotopy using (cofibIso)
open import DeloopS3.Bridge.CellularPushout.Cellular using
  (Z ; restrictCell ; cellular-coefficients)

Q : {S T : CWskel ℓ-zero} (h : cellMap S T) (n : ℕ)
  → cofibCW n S → cofibCW n T
Q h n = prefunctoriality.fn+1/fn (suc n)
  (restrictCell h (suc n)) (n , <ᵗsuc)

private
  BQ : (T : CWskel ℓ-zero) (n : ℕ)
    → Iso (cofibCW n T) (SphereBouquet n (Fin (snd T .fst n)))
  BQ T n = BouquetIso-gen n (snd T .fst n)
    (snd T .snd .fst n) (snd T .snd .snd .snd n)

  abstract
    suspIso-suspFun-local : ∀ {ℓ₁ ℓ₂ ℓ₃ ℓ₄}
      {A : Type ℓ₁} {B : Type ℓ₂} {C : Type ℓ₃} {D : Type ℓ₄}
      (e₁ : Iso A B) (e₂ : Iso C D) (f : C → A)
      → Iso.fun (congSuspIso e₁) ∘ suspFun f ∘ Iso.inv (congSuspIso e₂)
       ≡ suspFun (Iso.fun e₁ ∘ f ∘ Iso.inv e₂)
    suspIso-suspFun-local e₁ e₂ f i north = north
    suspIso-suspFun-local e₁ e₂ f i south = south
    suspIso-suspFun-local e₁ e₂ f i (merid a j) =
      merid ((Iso.fun e₁ ∘ f ∘ Iso.inv e₂) a) j

    cofibIso-suspFun-local : (n : ℕ) (S T : CWskel ℓ-zero)
      (f : cofibCW n S → cofibCW n T)
      → Iso.fun (cofibIso n T) ∘ suspFun f ∘ Iso.inv (cofibIso n S)
       ≡ bouquetSusp→ (Iso.fun (BQ T n) ∘ f ∘ Iso.inv (BQ S n))
    cofibIso-suspFun-local n S T f =
      cong (λ k → Iso.fun sphereBouquetSuspIso ∘ k
        ∘ Iso.inv sphereBouquetSuspIso)
        (suspIso-suspFun-local (BQ T n) (BQ S n) f)

module RetractionDegree (Xs Xt Ys Yt : CWskel ℓ-zero)
  (u : cellMap Xs Xt) (Φ : cellMap Ys Yt)
  (rs : cofibCW 3 Ys → Susp (cofibCW 2 Xs))
  (rt : cofibCW 3 Yt → Susp (cofibCW 2 Xt)) where

  private
    φbar : SphereBouquet 3 (Fin (snd Ys .fst 3))
      → SphereBouquet 3 (Fin (snd Yt .fst 3))
    φbar = Iso.fun (BQ Yt 3) ∘ Q Φ 3 ∘ Iso.inv (BQ Ys 3)

    ubar : SphereBouquet 2 (Fin (snd Xs .fst 2))
      → SphereBouquet 2 (Fin (snd Xt .fst 2))
    ubar = Iso.fun (BQ Xt 2) ∘ Q u 2 ∘ Iso.inv (BQ Xs 2)

    rsbar : SphereBouquet 3 (Fin (snd Ys .fst 3))
      → SphereBouquet 3 (Fin (snd Xs .fst 2))
    rsbar = Iso.fun (cofibIso 2 Xs) ∘ rs ∘ Iso.inv (BQ Ys 3)

    rtbar : SphereBouquet 3 (Fin (snd Yt .fst 3))
      → SphereBouquet 3 (Fin (snd Xt .fst 2))
    rtbar = Iso.fun (cofibIso 2 Xt) ∘ rt ∘ Iso.inv (BQ Yt 3)

    Ubar : SphereBouquet 3 (Fin (snd Xs .fst 2))
      → SphereBouquet 3 (Fin (snd Xt .fst 2))
    Ubar = Iso.fun (cofibIso 2 Xt) ∘ suspFun (Q u 2)
      ∘ Iso.inv (cofibIso 2 Xs)

  Rs : AbGroupHom (Z Ys 3) (Z Xs 2)
  Rs = bouquetDegree rsbar

  Rt : AbGroupHom (Z Yt 3) (Z Xt 2)
  Rt = bouquetDegree rtbar

  private
    abstract
      suspended-quotient-degree : bouquetDegree Ubar ≡ cellular-coefficients u 2
      suspended-quotient-degree =
        cong bouquetDegree (cofibIso-suspFun-local 2 Xs Xt (Q u 2))
        ∙ sym (bouquetDegreeSusp ubar)

  abstract
    retraction-degree-natural : rt ∘ Q Φ 3 ≡ suspFun (Q u 2) ∘ rs
      → compGroupHom (cellular-coefficients Φ 3) Rt
       ≡ compGroupHom Rs (cellular-coefficients u 2)
    retraction-degree-natural natural =
      sym (bouquetDegreeComp rtbar φbar)
      ∙ cong bouquetDegree (funExt λ z →
          cong (Iso.fun (cofibIso 2 Xt) ∘ rt)
            (Iso.ret (BQ Yt 3) (Q Φ 3 (Iso.inv (BQ Ys 3) z))))
      ∙ cong bouquetDegree
          (cong (λ k → Iso.fun (cofibIso 2 Xt) ∘ k ∘ Iso.inv (BQ Ys 3))
            natural)
      ∙ cong bouquetDegree (funExt λ z →
          cong (Iso.fun (cofibIso 2 Xt) ∘ suspFun (Q u 2))
            (sym (Iso.ret (cofibIso 2 Xs) (rs (Iso.inv (BQ Ys 3) z)))))
      ∙ bouquetDegreeComp Ubar rsbar
      ∙ cong (compGroupHom Rs) suspended-quotient-degree
