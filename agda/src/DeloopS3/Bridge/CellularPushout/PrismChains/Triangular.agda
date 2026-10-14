{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Triangular where

-- Generic triangular algebra. No support/diagonal-sign hypothesis.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import DeloopS3.Bridge.CellularPushout.Algebra
open IsGroupHom

module Triangular (B C A V : AbGroup ℓ-zero)
  (split : AbGroupEquiv V (dirProdAb B (dirProdAb C A)))
  (jB : AbGroupHom B V) (jC : AbGroupHom C V)
  (k : AbGroupHom A V) (r : AbGroupHom V A)
  (sB : compGroupHom jB (GroupEquiv→GroupHom split)
    ≡ pairHom idGroupHom (pairHom trivGroupHom trivGroupHom))
  (sC : compGroupHom jC (GroupEquiv→GroupHom split)
    ≡ pairHom trivGroupHom (pairHom idGroupHom trivGroupHom))
  (rk : compGroupHom k r ≡ idGroupHom)
  (rB : compGroupHom jB r ≡ trivGroupHom)
  (rC : compGroupHom jC r ≡ trivGroupHom) where

  W : AbGroup ℓ-zero
  W = dirProdAb B (dirProdAb C A)

  private
    module BG = AbGroupStr (snd B)
    module CG = AbGroupStr (snd C)
    module AG = AbGroupStr (snd A)
    module VG = AbGroupStr (snd V)
    module WG = AbGroupStr (snd W)

  s : AbGroupHom V W
  s = GroupEquiv→GroupHom split

  si : AbGroupHom W V
  si = GroupEquiv→GroupHom (invGroupEquiv split)

  pB : AbGroupHom W B
  pB = fstHom B (dirProdAb C A)
  pC : AbGroupHom W C
  pC = compGroupHom (sndHom B (dirProdAb C A)) (fstHom C A)
  pA : AbGroupHom W A
  pA = compGroupHom (sndHom B (dirProdAb C A)) (sndHom C A)

  q : AbGroupHom W V
  q = addGroupHom W V
    (addGroupHom W V (compGroupHom pB jB) (compGroupHom pC jC))
    (compGroupHom pA k)

  χ : AbGroupHom V W
  χ = pairHom
    (subtrGroupHom V B (compGroupHom s pB)
      (compGroupHom (compGroupHom r k) (compGroupHom s pB)))
    (pairHom
      (subtrGroupHom V C (compGroupHom s pC)
        (compGroupHom (compGroupHom r k) (compGroupHom s pC))) r)

  abstract
    rq : (b : fst B) (c : fst C) (a : fst A)
      → fst r (fst q (b , c , a)) ≡ a
    rq b c a = pres· (snd r) _ _
      ∙ cong₂ AG._+_
        (pres· (snd r) _ _
          ∙ cong₂ AG._+_ (funExt⁻ (cong fst rB) b) (funExt⁻ (cong fst rC) c)
          ∙ AG.+IdR AG.0g)
        (funExt⁻ (cong fst rk) a)
      ∙ AG.+IdL a

    sq : (b : fst B) (c : fst C) (a : fst A)
      → fst s (fst q (b , c , a))
       ≡ (BG._+_ b (fst (fst s (fst k a)))
         , CG._+_ c (fst (snd (fst s (fst k a))))
         , snd (snd (fst s (fst k a))))
    sq b c a = pres· (snd s) _ _
      ∙ cong (λ z → WG._+_ z (fst s (fst k a)))
        (pres· (snd s) _ _
          ∙ cong₂ WG._+_ (funExt⁻ (cong fst sB) b) (funExt⁻ (cong fst sC) c))
      ∙ ΣPathP
        (cong (λ z → BG._+_ z (fst (fst s (fst k a)))) (BG.+IdR b)
        , ΣPathP
          (cong (λ z → CG._+_ z (fst (snd (fst s (fst k a))))) (CG.+IdL c)
          , cong (λ z → AG._+_ z (snd (snd (fst s (fst k a))))) (AG.+IdR AG.0g) ∙ AG.+IdL _))

    χq : compGroupHom q χ ≡ idGroupHom
    χq = GroupHom≡ (funExt λ (b , c , a) →
      cong₂ (λ z a' → BG._+_ (fst z) (BG.-_ (fst (fst s (fst k a'))))
        , CG._+_ (fst (snd z)) (CG.-_ (fst (snd (fst s (fst k a'))))) , a')
        (sq b c a) (rq b c a)
      ∙ ΣPathP
        (sym (BG.+Assoc b _ _) ∙ cong (BG._+_ b) (BG.+InvR _) ∙ BG.+IdR b
        , ΣPathP
          (sym (CG.+Assoc c _ _) ∙ cong (CG._+_ c) (CG.+InvR _) ∙ CG.+IdR c
          , refl)))

    χ-jB : compGroupHom jB χ ≡ pairHom idGroupHom (pairHom trivGroupHom trivGroupHom)
    χ-jB = GroupHom≡ (funExt λ b →
      cong₂ (λ z a → BG._+_ (fst z) (BG.-_ (fst (fst s (fst k a))))
        , CG._+_ (fst (snd z)) (CG.-_ (fst (snd (fst s (fst k a))))) , a)
        (funExt⁻ (cong fst sB) b) (funExt⁻ (cong fst rB) b)
      ∙ ΣPathP
        (minusHomZero (compGroupHom k (compGroupHom s pB)) b
        , ΣPathP (minusHomZero (compGroupHom k (compGroupHom s pC)) CG.0g , refl)))

    χ-jC : compGroupHom jC χ ≡ pairHom trivGroupHom (pairHom idGroupHom trivGroupHom)
    χ-jC = GroupHom≡ (funExt λ c →
      cong₂ (λ z a → BG._+_ (fst z) (BG.-_ (fst (fst s (fst k a))))
        , CG._+_ (fst (snd z)) (CG.-_ (fst (snd (fst s (fst k a))))) , a)
        (funExt⁻ (cong fst sC) c) (funExt⁻ (cong fst rC) c)
      ∙ ΣPathP
        (minusHomZero (compGroupHom k (compGroupHom s pB)) BG.0g
        , ΣPathP (minusHomZero (compGroupHom k (compGroupHom s pC)) c , refl)))

  -- Only this algebraic property of V is needed for the other inverse.
  -- It is NOT silently inferred for arbitrary abelian groups.
  module Complete
    (direct-finite : (u t : AbGroupHom V V)
      → compGroupHom u t ≡ idGroupHom → compGroupHom t u ≡ idGroupHom) where
    private
      u t : AbGroupHom V V
      u = compGroupHom s q
      t = compGroupHom χ si

      tu : compGroupHom u t ≡ idGroupHom
      tu = GroupHom≡ (funExt λ z →
        cong (fst si) (funExt⁻ (cong fst χq) (fst s z)) ∙ retEq (fst split) z)

    abstract
      qχ : compGroupHom χ q ≡ idGroupHom
      qχ = GroupHom≡ (funExt λ z →
        sym (cong (fst q) (secEq (fst split) (fst χ z)))
        ∙ funExt⁻ (cong fst (direct-finite u t tu)) z)

    qIso : Iso (fst W) (fst V)
    Iso.fun qIso = fst q
    Iso.inv qIso = fst χ
    Iso.sec qIso = funExt⁻ (cong fst qχ)
    Iso.ret qIso = funExt⁻ (cong fst χq)

    qEquiv : AbGroupEquiv W V
    qEquiv = isoToEquiv qIso , snd q
