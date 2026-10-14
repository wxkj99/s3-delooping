{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Paths where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (tt)
open import Cubical.HITs.Susp using (Susp ; north ; toSusp)
import Cubical.HITs.Join as J
import Cubical.HITs.Pushout as P
open import Cubical.HITs.Wedge using (_⋁_ ; ⋁↪)
open import DeloopS3.Compat.Whitehead using (joinTo⋁)

-- Path algebra for the suspension calculation.
abstract
  double-left : {X : Type} {x : X} (p : x ≡ x)
    → (refl ∙∙ refl ∙∙ p) ≡ p
  double-left p = doubleCompPath-elim refl refl p
    ∙ cong (_∙ p) (sym (lUnit refl)) ∙ sym (lUnit p)

  double-right : {X : Type} {x : X} (p : x ≡ x)
    → (p ∙∙ refl ∙∙ refl) ≡ p
  double-right p = doubleCompPath-elim p refl refl
    ∙ sym (rUnit (p ∙ refl)) ∙ sym (rUnit p)

  product-diagonal : {X Y : Type} {x : X} {y : Y}
    (p : x ≡ x) (q : y ≡ y)
    → ((λ i → x , q i) ∙∙ refl ∙∙ (λ i → p i , y))
      ≡ (λ i → p i , q i)
  product-diagonal {x = x} {y = y} p q k i =
    (cong-∙∙ fst (λ i → x , q i) refl (λ i → p i , y)
      ∙ double-left p) k i ,
    (cong-∙∙ snd (λ i → x , q i) refl (λ i → p i , y)
      ∙ double-right q) k i

  diagonal-square : {X Y : Type} {x : X} {y : Y}
    (p : x ≡ x) (q : y ≡ y) (e : (x , y) ≡ (x , y))
    → e ≡ (λ i → p i , q i)
    → PathP (λ i → e i ≡ (x , y))
        (λ j → p j , y) (λ j → x , q (~ j))
  diagonal-square {x = x} {y = y} p q e eq =
    subst (λ r → PathP (λ i → r i ≡ (x , y))
      (λ j → p j , y) (λ j → x , q (~ j)))
      (sym eq) (λ i j → p (i ∨ j) , q (i ∧ ~ j))

module JoinNull (A B : Type) (a₀ : A) (b₀ : B) where
  private
    W : J.join A B → (Susp A , north) ⋁ (Susp B , north)
    W = joinTo⋁ {A = A , a₀} {B = B , b₀}

    p : A → Path (Susp A) north north
    p = toSusp (A , a₀)

    q : B → Path (Susp B) north north
    q = toSusp (B , b₀)

  abstract
    edge-diagonal : (a : A) (b : B)
      → cong (λ z → ⋁↪ (W z)) (J.push a b)
        ≡ (λ i → p a i , q b i)
    edge-diagonal a b =
      cong-∙∙ ⋁↪ (λ i → P.inr (q b i))
        (sym (P.push tt)) (λ i → P.inl (p a i))
      ∙ product-diagonal (p a) (q b)

    edge-square : (a : A) (b : B)
      → PathP (λ i → Path (Susp A × Susp B)
          (⋁↪ (W (J.push a b i))) (north , north))
          (λ j → p a j , north) (λ j → north , q b (~ j))
    edge-square a b = diagonal-square (p a) (q b)
      (cong (λ z → ⋁↪ (W z)) (J.push a b)) (edge-diagonal a b)

  abstract
    join-to-product-null : (z : J.join A B)
      → Path (Susp A × Susp B) (⋁↪ (W z)) (north , north)
    join-to-product-null (J.inl a) j = p a j , north
    join-to-product-null (J.inr b) j = north , q b (~ j)
    join-to-product-null (J.push a b i) = edge-square a b i
