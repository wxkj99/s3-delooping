{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Quotient where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.QuotientGroup
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.Algebra.ChainComplex.Homology
open import Cubical.Relation.Binary.Base
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT

open ChainComplex
open IsGroupHom
open BinaryRelation

private variable ℓ : Level

-- Effectiveness of the actual quotient relation, not a replacement
-- definition of homology. This works for every normal subgroup.
module QuotientKernel (G : Group ℓ) (N : NormalSubgroup G) where
  private
    module G = GroupStr (snd G)
    open GroupTheory G
    open isSubgroup (snd (fst N))
    R : fst G → fst G → Type ℓ
    R = _~_ G (fst N) (snd N)

    abstract
      rr : (x : fst G) → R x x
      rr x = subst (λ z → fst (fst (fst N) z)) (sym (G.·InvR x)) id-closed

      rs : (x y : fst G) → R x y → R y x
      rs x y r = subst (λ z → fst (fst (fst N) z))
        (invDistr x (G.inv y) ∙ cong (G._· G.inv x) (invInv y)) (inv-closed r)

      rt : (x y z : fst G) → R x y → R y z → R x z
      rt x y z p q = subst (λ w → fst (fst (fst N) w))
        (sym (G.·Assoc x (G.inv y) (G._·_ y (G.inv z)))
         ∙ cong (G._·_ x) (G.·Assoc (G.inv y) y (G.inv z)
           ∙ cong (G._· G.inv z) (G.·InvL y) ∙ G.·IdL (G.inv z)))
        (op-closed p q)

  abstract
    class-zero→member : (x : fst G)
      → Path (fst (G / N)) SQ.[ x ] SQ.[ G.1g ]
      → fst (fst (fst N) x)
    class-zero→member x p = subst (λ z → fst (fst (fst N) z))
      (cong (G._·_ x) inv1g ∙ G.·IdR x)
      (SQ.effective (λ _ _ → snd (fst (fst N) _) )
        (equivRel rr rs rt) x G.1g p)

module Homology (C : ChainComplex ℓ) (n : ℕ) where
  Z : Group ℓ
  Z = ker∂n n C
  H : Group ℓ
  H = homology n C
  module H = GroupStr (snd H)
  module X = AbGroupStr (snd (chain C (suc n)))
  module W = AbGroupStr (snd (chain C (suc (suc n))))
  Cycle : Type ℓ
  Cycle = fst Z
  class : Cycle → fst H
  class = SQ.[_]
  zeroCycle : Cycle
  zeroCycle = GroupStr.1g (snd Z)
  boundary : fst (chain C (suc (suc n))) → Cycle
  boundary = fst (∂ker n C)

  abstract
    cycle-path : {x y : Cycle} → fst x ≡ fst y → x ≡ y
    cycle-path = kerGroup≡ (bdry C n)

    class-path : {x y : Cycle} → fst x ≡ fst y → class x ≡ class y
    class-path p = cong class (cycle-path p)

    boundary-zero : (v : fst (chain C (suc (suc n)))) → class (boundary v) ≡ H.1g
    boundary-zero v = SQ.eq/ _ _ PT.∣ v , cycle-path
      (sym (cong (X._+_ (fst (boundary v)))
        (GroupTheory.inv1g (AbGroup→Group (chain C (suc n)))) ∙ X.+IdR _)) ∣₁

    zero→boundary : (x : Cycle) → class x ≡ H.1g
      → PT.∥ Σ[ v ∈ fst (chain C (suc (suc n))) ]
           fst (bdry C (suc n)) v ≡ fst x ∥₁
    zero→boundary x p = PT.map (λ v → fst v , cong fst (snd v))
      (QuotientKernel.class-zero→member Z (img∂+1⊂ker∂n n C) x p)

    boundary→zero : (x : Cycle) (v : fst (chain C (suc (suc n))))
      → fst (bdry C (suc n)) v ≡ fst x → class x ≡ H.1g
    boundary→zero x v p = sym (class-path p) ∙ boundary-zero v

    difference→path : (x y : Cycle) (v : fst (chain C (suc (suc n))))
      → fst (bdry C (suc n)) v ≡ X._+_ (fst x) (X.- fst y)
      → class x ≡ class y
    difference→path x y v p = SQ.eq/ x y PT.∣ v , cycle-path p ∣₁

    boundary-add-path : (x y : Cycle) (v : fst (chain C (suc (suc n))))
      → X._+_ (fst (bdry C (suc n)) v) (fst x) ≡ fst y
      → class x ≡ class y
    boundary-add-path x y v p = sym
      (sym (class-path {x = GroupStr._·_ (snd Z) (boundary v) x} {y = y} p)
        ∙ cong (λ h → H._·_ h (class x)) (boundary-zero v) ∙ H.·IdL (class x))

  HAb : AbGroup ℓ
  HAb = Group→AbGroup H
    (SQ.elimProp2 (λ _ _ → H.is-set _ _) λ x y → class-path (X.+Comm _ _))

-- A homomorphism on cycles descending through a specified boundary lift.
module Descent {C D : ChainComplex ℓ} {m n : ℕ}
  (u : GroupHom (ker∂n m C) (ker∂n n D))
  (lift : fst (chain C (suc (suc m))) → fst (chain D (suc (suc n))))
  (comm : (v : fst (chain C (suc (suc m))))
    → fst (∂ker n D) (lift v) ≡ fst u (fst (∂ker m C) v)) where

  induced : GroupHom (homology m C) (homology n D)
  induced = Hom/ u (λ x y → PT.map λ v → lift (fst v) ,
    comm (fst v) ∙ cong (fst u) (snd v) ∙ pres· (snd u) _ _
      ∙ cong (GroupStr._·_ (snd (ker∂n n D)) (fst u x)) (presinv (snd u) y))
