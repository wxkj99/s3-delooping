{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Transport where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.DMCExactness.Exactness using (exact-from-kernel)
open import DeloopS3.Bridge.DMCExactness.Groups using (exact-composite)

open IsGroupHom

conjugateHom : {G H G′ H′ : Group₀}
  → GroupEquiv G G′ → GroupEquiv H H′ → GroupHom G H → GroupHom G′ H′
conjugateHom eG eH u = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv eG))
  (compGroupHom u (GroupEquiv→GroupHom eH))

productEquiv : {G H G′ H′ : Group₀} → GroupEquiv G G′ → GroupEquiv H H′
  → GroupEquiv (DirProd G H) (DirProd G′ H′)
productEquiv eG eH = ≃-× (fst eG) (fst eH) , makeIsGroupHom
  (λ x y → ΣPathP (pres· (snd eG) (fst x) (fst y) , pres· (snd eH) (snd x) (snd y)))

abstract
  conjugate-exact : {G H K G′ H′ K′ : Group₀}
    (eG : GroupEquiv G G′) (eH : GroupEquiv H H′) (eK : GroupEquiv K K′)
    (u : GroupHom G H) (v : GroupHom H K)
    → Exact₃ u v → Exact₃ (conjugateHom eG eH u) (conjugateHom eH eK v)
  conjugate-exact {K = K} {G′ = G′} {H′ = H′} {K′ = K′} eG eH eK u v ex = exact-from-kernel
    (conjugateHom eG eH u) (conjugateHom eH eK v) kernel composite
    where
    kernel : (h : fst H′)
      → fst (conjugateHom eH eK v) h ≡ GroupStr.1g (snd K′)
      → PT.∥ fiber (fst (conjugateHom eG eH u)) h ∥₁
    kernel h p = PT.map (λ { (x , q) → equivFun (fst eG) x ,
      cong (equivFun (fst eH)) (cong (fst u) (retEq (fst eG) x) ∙ q) ∙ secEq (fst eH) h })
      (equivFun (ex (invEq (fst eH) h))
        (sym (retEq (fst eK) (fst v (invEq (fst eH) h)))
          ∙ cong (invEq (fst eK)) (p ∙ sym (pres1 (snd eK)))
          ∙ retEq (fst eK) (GroupStr.1g (snd K))))

    composite : (x : fst G′)
      → fst (conjugateHom eH eK v) (fst (conjugateHom eG eH u) x)
       ≡ GroupStr.1g (snd K′)
    composite x = cong (equivFun (fst eK))
      (cong (fst v) (retEq (fst eH) (fst u (invEq (fst eG) x)))
        ∙ exact-composite {u = u} {v = v} ex (invEq (fst eG) x)) ∙ pres1 (snd eK)
