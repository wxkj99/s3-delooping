{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.MooreMarked.Quotient where

-- Quotient UP first, on abstract groups.  The only concrete input needed
-- below is a map-compatible cokernel calculation, not a general LES.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Int using (ℤ ; pos) renaming (·IdR to int-mul-unit)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup ; ℤHom)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Algebra.Group.ZAction using
  (imℤHomSubGroup ; ℤHom→ℤ/im≅ℤ/im1 ; homPresℤ· ; rUnitℤ·ℤ)
open import Cubical.Algebra.Group.QuotientGroup using (_/_)
open import Cubical.Relation.Binary.Base using (module BinaryRelation)
open BinaryRelation using (isEquivRel ; equivRel)
open import Cubical.Functions.Surjection using (isSurjection)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetQuotients as SQ

abstract
  integer-homs-agree : (G : Group₀) (f g : GroupHom ℤGroup G)
    → fst f (pos 1) ≡ fst g (pos 1) → fst f ≡ fst g
  integer-homs-agree G f g one = funExt λ z →
    cong (fst f) (sym (rUnitℤ·ℤ z)) ∙ homPresℤ· f (pos 1) z
    ∙ cong (λ x → Cubical.Algebra.Group.ZAction._ℤ[_]·_ z G x) one
    ∙ sym (homPresℤ· g (pos 1) z)
    ∙ cong (fst g) (rUnitℤ·ℤ z)

module Modulus (n : ℕ) where
  multiply : GroupHom ℤGroup ℤGroup
  multiply = ℤHom (pos (suc n))

  Q : Group₀
  Q = ℤGroup / imℤHomSubGroup multiply

  residue : GroupEquiv Q (ℤGroup/ suc n)
  residue = BijectionIsoToGroupEquiv
    (ℤHom→ℤ/im≅ℤ/im1 multiply n (int-mul-unit (pos (suc n))))

  projection : GroupHom ℤGroup Q
  projection = SQ.[_] , makeIsGroupHom (λ _ _ → refl)

  private
    open GroupStr (snd ℤGroup) renaming (_·_ to _+z_ ; inv to -z_)
    R : ℤ → ℤ → Type
    R a b = PT.∥ fiber (fst multiply) (a +z (-z b)) ∥₁

    difference-inverse : (a b : ℤ) → -z (a +z (-z b)) ≡ b +z (-z a)
    difference-inverse a b = GroupTheory.invDistr ℤGroup a (-z b)
      ∙ cong (_+z (-z a)) (GroupTheory.invInv ℤGroup b)

    difference-compose : (a b c : ℤ)
      → (a +z (-z b)) +z (b +z (-z c)) ≡ a +z (-z c)
    difference-compose a b c = sym (·Assoc a (-z b) (b +z (-z c)))
      ∙ cong (a +z_) (·Assoc (-z b) b (-z c)
        ∙ cong (_+z (-z c)) (·InvL b) ∙ ·IdL (-z c))

    relation-equivalence : isEquivRel R
    relation-equivalence = equivRel
      (λ a → PT.∣ pos 0 , (IsGroupHom.pres1 (snd multiply) ∙ sym (·InvR a)) ∣₁)
      (λ a b → PT.map λ { (z , p) → (-z z) ,
        (IsGroupHom.presinv (snd multiply) z ∙ cong -z_ p ∙ difference-inverse a b) })
      (λ a b c → PT.rec2 PT.squash₁ λ { (x , p) (y , q) → PT.∣ (x +z y) ,
        (IsGroupHom.pres· (snd multiply) x y ∙ cong₂ _+z_ p q ∙ difference-compose a b c) ∣₁ })

  abstract
    quotient-kernel : (z : ℤ) → Path (fst Q) SQ.[ z ] SQ.[ pos 0 ]
      → PT.∥ fiber (fst multiply) z ∥₁
    quotient-kernel z p = PT.map (λ { (x , q) → x , (q ∙ ·IdR z) })
      (SQ.effective (λ _ _ → PT.squash₁) relation-equivalence z (pos 0) p)

  -- Exactness data for the SPECIFIED map q, obtained from the concrete
  -- bouquet computation.  This is not an unmarked isomorphism of groups.
  record ExactBottom (G : Group₀) (q : GroupHom ℤGroup G) : Type where
    field
      onto : isSurjection (fst q)
      kills : (z : ℤ) → fst q (fst multiply z) ≡ GroupStr.1g (snd G)
      kernel : (z : ℤ) → fst q z ≡ GroupStr.1g (snd G)
        → PT.∥ fiber (fst multiply) z ∥₁

  abstract
    exact-from-cokernel : (G : Group₀) (q : GroupHom ℤGroup G)
      (e : GroupEquiv Q G) → ((z : ℤ) → equivFun (fst e) SQ.[ z ] ≡ fst q z)
      → ExactBottom G q
    ExactBottom.onto (exact-from-cokernel G q e beta) y =
      SQ.elimProp {P = λ t → equivFun (fst e) t ≡ y → PT.∥ fiber (fst q) y ∥₁}
        (λ t → isPropΠ λ _ → PT.squash₁)
        (λ z p → PT.∣ z , (sym (beta z) ∙ p) ∣₁)
        (invEq (fst e) y) (secEq (fst e) y)
    ExactBottom.kills (exact-from-cokernel G q e beta) z =
      sym (beta (fst multiply z))
      ∙ cong (equivFun (fst e)) (SQ.eq/ _ _ PT.∣ z , refl ∣₁)
      ∙ IsGroupHom.pres1 (snd e)
    ExactBottom.kernel (exact-from-cokernel G q e beta) z p = quotient-kernel z
      (sym (retEq (fst e) SQ.[ z ])
      ∙ cong (invEq (fst e)) (beta z ∙ p ∙ sym (IsGroupHom.pres1 (snd e)))
      ∙ retEq (fst e) SQ.[ pos 0 ])

  module FromExact (G : Group₀) (q : GroupHom ℤGroup G) (exact : ExactBottom G q) where
    private
      open GroupStr (snd G) using (_·_ ; inv) renaming (is-set to G-is-set)
      open ExactBottom exact
      respects : (a b : ℤ) → R a b → fst q a ≡ fst q b
      respects a b = PT.rec (G-is-set _ _) λ { (z , p) →
        GroupTheory.invUniqueL G
          (sym (cong₂ _·_ refl (IsGroupHom.presinv (snd q) b))
          ∙ sym (IsGroupHom.pres· (snd q) a (GroupStr.inv (snd ℤGroup) b))
          ∙ cong (fst q) (sym p) ∙ kills z)
        ∙ GroupTheory.invInv G (fst q b) }

    quotient-map : GroupHom Q G
    fst quotient-map = SQ.rec G-is-set (fst q) respects
    snd quotient-map = makeIsGroupHom
      (SQ.elimProp2 (λ _ _ → G-is-set _ _) (IsGroupHom.pres· (snd q)))

    abstract
      quotient-map-equiv : isEquiv (fst quotient-map)
      quotient-map-equiv = snd (fst (BijectionIsoToGroupEquiv bijection))
        where
        bijection : BijectionIso Q G
        BijectionIso.fun bijection = quotient-map
        BijectionIso.inj bijection = SQ.elimProp (λ _ → isPropΠ λ _ → SQ.squash/ _ _)
          (λ z p → SQ.eq/ _ _ (kernel z p))
        BijectionIso.surj bijection y = PT.map (λ { (z , p) → SQ.[ z ] , p }) (onto y)

    quotient-equivalence : GroupEquiv Q G
    quotient-equivalence = (fst quotient-map , quotient-map-equiv) , snd quotient-map

    cyclic-to-group : GroupEquiv (ℤGroup/ suc n) G
    cyclic-to-group = compGroupEquiv (invGroupEquiv residue) quotient-equivalence

  -- Use the library computation only to establish exactness of q; the
  -- final map is the quotient recursor above, on the actual bottom map.
  module Calibrate (G : Group₀) (q : GroupHom ℤGroup G)
    (seed : GroupEquiv G (ℤGroup/ suc n))
    (mark : equivFun (fst seed) (fst q (pos 1))
      ≡ equivFun (fst residue) SQ.[ pos 1 ]) where

    private
      comparison : GroupEquiv Q G
      comparison = compGroupEquiv residue (invGroupEquiv seed)

      beta : (z : ℤ) → equivFun (fst comparison) SQ.[ z ] ≡ fst q z
      beta = funExt⁻ (integer-homs-agree G
        (compGroupHom projection (GroupEquiv→GroupHom comparison)) q
        (cong (invEq (fst seed)) (sym mark) ∙ retEq (fst seed) (fst q (pos 1))))

    exact-bottom : ExactBottom G q
    exact-bottom = exact-from-cokernel G q comparison beta

    module UP = FromExact G q exact-bottom

    marked-from-bottom : GroupEquiv G (ℤGroup/ suc n)
    marked-from-bottom = invGroupEquiv UP.cyclic-to-group

    abstract
      marked-from-bottom-generator :
        equivFun (fst marked-from-bottom) (fst q (pos 1))
        ≡ equivFun (fst residue) SQ.[ pos 1 ]
      marked-from-bottom-generator =
        cong (invEq (fst UP.cyclic-to-group))
          (sym (cong (fst UP.quotient-map) (retEq (fst residue) SQ.[ pos 1 ])))
        ∙ retEq (fst UP.cyclic-to-group) (equivFun (fst residue) SQ.[ pos 1 ])
