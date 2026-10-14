{-# OPTIONS --safe --cubical --guardedness --lossy-unification #-}
module DeloopS3.Bridge.DegreeSpan.FiniteCoproductGroups where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Sigma
import Cubical.Data.SumFin as SF
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Pi

open IsGroupHom

product-equiv : {G H K L : Group₀} → GroupEquiv G H → GroupEquiv K L
  → GroupEquiv (DirProd G K) (DirProd H L)
product-equiv e f = Σ-cong-equiv (fst e) (λ _ → fst f) ,
  makeIsGroupHom (λ x y → ΣPathP (pres· (snd e) (fst x) (fst y) ,
    pres· (snd f) (snd x) (snd y)))

module Vectors (G : AbGroup ℓ-zero) where
  private
    module G = AbGroupStr (snd G)

  ΠG : Type₀ → Group₀
  ΠG I = AbGroup→Group (ΠAbGroup {X = I} (λ _ → G))

  V : ℕ → Group₀
  V n = ΠG (SF.Fin n)

  join : {n : ℕ} → fst G × fst (V n) → fst (V (suc n))
  join (a , v) SF.fzero = a
  join (a , v) (SF.fsuc i) = v i

  split : (n : ℕ) → GroupEquiv (DirProd (AbGroup→Group G) (V n)) (V (suc n))
  split n = GroupIso→GroupEquiv (iso join (λ v → v SF.fzero , v ∘ SF.fsuc)
    (λ v → funExt λ { SF.fzero → refl ; (SF.fsuc i) → refl })
    (λ _ → refl) , makeIsGroupHom λ _ _ → funExt λ { SF.fzero → refl ; (SF.fsuc i) → refl })

  reindex : {I J : Type₀} → I ≃ J → GroupEquiv (ΠG J) (ΠG I)
  reindex e = GroupIso→GroupEquiv (iso (λ v → v ∘ equivFun e) (λ v → v ∘ invEq e)
    (λ v → funExt λ i → cong v (retEq e i))
    (λ v → funExt λ j → cong v (secEq e j)) , makeIsGroupHom λ _ _ → refl)

  empty-equiv : (H : Group₀) → isContr (fst H) → GroupEquiv H (V 0)
  empty-equiv H h = GroupIso→GroupEquiv (iso (λ _ ()) (λ _ → fst h)
    (λ v → funExt λ ()) (snd h) , makeIsGroupHom λ _ _ → funExt λ ())

  point : {n : ℕ} → SF.Fin n → fst G → fst (V n)
  point {suc n} SF.fzero a SF.fzero = a
  point {suc n} SF.fzero a (SF.fsuc j) = G.0g
  point {suc n} (SF.fsuc i) a SF.fzero = G.0g
  point {suc n} (SF.fsuc i) a (SF.fsuc j) = point i a j

  tail : (n : ℕ) → GroupHom (V n) (V (suc n))
  fst (tail n) v = join (G.0g , v)
  snd (tail n) = makeIsGroupHom λ _ _ → funExt λ
    { SF.fzero → sym (G.+IdR G.0g) ; (SF.fsuc i) → refl }

  abstract
    hom-ext : (n : ℕ) {H : Group₀} (f g : GroupHom (V n) H)
      → ((i : SF.Fin n) (a : fst G) → fst f (point i a) ≡ fst g (point i a))
      → (v : fst (V n)) → fst f v ≡ fst g v
    hom-ext zero {H} f g p v = cong (fst f) (funExt λ ())
      ∙ pres1 (snd f) ∙ sym (pres1 (snd g)) ∙ cong (fst g) (funExt λ ())
    hom-ext (suc n) {H} f g p v = cong (fst f) decompose
      ∙ pres· (snd f) (point SF.fzero (v SF.fzero)) (fst (tail n) (v ∘ SF.fsuc))
      ∙ cong₂ (GroupStr._·_ (snd H)) (p SF.fzero (v SF.fzero))
          (hom-ext n (compGroupHom (tail n) f) (compGroupHom (tail n) g)
            (λ i a → cong (fst f) (funExt λ { SF.fzero → refl ; (SF.fsuc j) → refl })
              ∙ p (SF.fsuc i) a
              ∙ cong (fst g) (funExt λ { SF.fzero → refl ; (SF.fsuc j) → refl }))
            (v ∘ SF.fsuc))
      ∙ sym (pres· (snd g) (point SF.fzero (v SF.fzero)) (fst (tail n) (v ∘ SF.fsuc)))
      ∙ cong (fst g) (sym decompose)
      where
      decompose : v ≡ GroupStr._·_ (snd (V (suc n)))
        (point SF.fzero (v SF.fzero)) (fst (tail n) (v ∘ SF.fsuc))
      decompose = funExt λ { SF.fzero → sym (G.+IdR (v SF.fzero))
                           ; (SF.fsuc i) → sym (G.+IdL (v (SF.fsuc i))) }
