{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.Coproduct where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Transport using (transportTransport⁻)
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; suc-≤-suc ; <-trans)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty using (⊥)
import Cubical.Data.Sum as Sum
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.CW.Instances.Empty using (hasCWskel⊥ ; CWskel⊥)
open import Cubical.HITs.Pushout using (Pushout ; inl ; inr)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map)
open import DeloopS3.Bridge.ComponentHomology.ChainTools using (chosen-zero ; no-cells-homology)
open import DeloopS3.Bridge.DMCExactness.Geometric
open import DeloopS3.Bridge.CellularPushout.PrismChains.Packaging
  using (PushoutLES ; finite-pushoutLES-merely)
import DeloopS3.Bridge.SpanCells as Cells
open import DeloopS3.Bridge.Profile.BaseSeifert.Groups
open import DeloopS3.Bridge.Profile.BaseSeifert.Functor

open IsGroupHom

emptyCW : CW₀
emptyCW = ⊥ , PT.∣ hasCWskel⊥ ∣₁

abstract
  empty-H-zero : (n : ℕ) → Hzero emptyCW n
  empty-H-zero n = chosen-zero emptyCW hasCWskel⊥ n (no-cells-homology CWskel⊥ n refl)

-- A finite coproduct theorem with the actual inclusions as its forward
-- map. It is deliberately restricted to positive degrees 1,...,4.
-- In degree zero a disjoint union has an extra reduced summand.
module Coproduct (X Y S : CW₀) (chart : fst S ≃ (fst X Sum.⊎ fst Y))
  (dX dY : ℕ) (finX : Finite≤ dX (fst X)) (finY : Finite≤ dY (fst Y)) where

  left : fst X → fst S
  left = invEq chart ∘ Sum.inl
  right : fst Y → fst S
  right = invEq chart ∘ Sum.inr

  sum-map : (n : ℕ)
    → GroupHom (DirProd (H̃ᶜʷ X (suc n)) (H̃ᶜʷ Y (suc n))) (H̃ᶜʷ S (suc n))
  sum-map n = sum-hom X Y S n left right

  private
    module U = Cells.Disjoint (fst X) (fst Y)
    P : CW₀
    P = Pushout U.left U.right , finite≤→isCW
      (pushout-finite≤ U.left U.right 0 dX dY Cells.empty-finite finX finY)

    LES : Type₁
    LES = PushoutLES emptyCW X Y U.left U.right P

    abstract
      les : PT.∥ LES ∥₁
      les = finite-pushoutLES-merely emptyCW X Y U.left U.right
        0 dX dY Cells.empty-finite finX finY

    module FromLES (witness : LES) (n : ℕ) (bound : n < 4) where
      private
        p = fst witness
        module L = SpanSequenceData (snd witness)

        chartP : fst P ≃ fst S
        chartP = compEquiv (pathToEquiv p) (compEquiv (invEquiv U.sumEquiv) (invEquiv chart))

        t : fst P → fst S
        t = equivFun chartP

        k : GroupHom (H̃ᶜʷ P (suc n)) (H̃ᶜʷ S (suc n))
        k = cellular-map P S (suc n) t

        t-left : t ∘ (transport (sym p) ∘ inl) ≡ left
        t-left = funExt λ x → cong (invEq chart ∘ U.toSum) (transportTransport⁻ p (inl x))

        t-right : t ∘ (transport (sym p) ∘ inr) ≡ right
        t-right = funExt λ y → cong (invEq chart ∘ U.toSum) (transportTransport⁻ p (inr y))

        agreement : (xy : fst (DirProd (H̃ᶜʷ X (suc n)) (H̃ᶜʷ Y (suc n))))
          → fst k (fst (L.sum-map (suc n)) xy) ≡ fst (sum-map n) xy
        agreement (x , y) = cong (fst k) (L.sum-agrees (suc n) (x , y))
          ∙ pres· (snd k)
              (fst (cellular-map X P (suc n) (transport (sym p) ∘ inl)) x)
              (fst (cellular-map Y P (suc n) (transport (sym p) ∘ inr)) y)
          ∙ cong₂ (GroupStr._·_ (snd (H̃ᶜʷ S (suc n))))
              (map-square X P S (suc n) (transport (sym p) ∘ inl) t left t-left x)
              (map-square Y P S (suc n) (transport (sym p) ∘ inr) t right t-right y)
          ∙ sym (sum-hom-eval X Y S n left right x y)

      abstract
        is-equivalence : isEquiv (fst (sum-map n))
        is-equivalence = subst isEquiv (funExt agreement)
          (snd (compEquiv
            (fst (L.sum-map (suc n)) , exact-ends-equiv
              (L.source-map (suc n)) (L.sum-map (suc n)) (L.boundary n)
              (L.exact-target (suc n) (suc-≤-suc bound))
              (L.exact-total n (<-trans bound (0 , refl)))
              (empty-H-zero (suc n)) (empty-H-zero n))
            (fst k , map-equiv P S (suc n) chartP)))

  abstract
    sum-is-equiv : (n : ℕ) → n < 4 → isEquiv (fst (sum-map n))
    sum-is-equiv n bound = PT.rec (isPropIsEquiv (fst (sum-map n)))
      (λ witness → FromLES.is-equivalence witness n bound) les

    sum-equiv : (n : ℕ) → n < 4
      → GroupEquiv (DirProd (H̃ᶜʷ X (suc n)) (H̃ᶜʷ Y (suc n))) (H̃ᶜʷ S (suc n))
    sum-equiv n bound = (fst (sum-map n) , sum-is-equiv n bound) , snd (sum-map n)

    sum-equiv-eval : (n : ℕ) (bound : n < 4)
      (x : fst (H̃ᶜʷ X (suc n))) (y : fst (H̃ᶜʷ Y (suc n)))
      → equivFun (fst (sum-equiv n bound)) (x , y)
        ≡ GroupStr._·_ (snd (H̃ᶜʷ S (suc n)))
          (fst (cellular-map X S (suc n) left) x) (fst (cellular-map Y S (suc n) right) y)
    sum-equiv-eval n bound x y = sum-hom-eval X Y S n left right x y
