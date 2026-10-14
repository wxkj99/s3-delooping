{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.DMCExactness.Groups where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)

open IsGroupHom

abstract
  contr→zero : (G : Group₀) → isContr (fst G) → (x : fst G) → x ≡ GroupStr.1g (snd G)
  contr→zero G c x = sym (snd c x) ∙ snd c (GroupStr.1g (snd G))

  equiv-kernel-zero : {G H : Group₀} (u : GroupHom G H) → isEquiv (fst u)
    → (x : fst G) → fst u x ≡ GroupStr.1g (snd H) → x ≡ GroupStr.1g (snd G)
  equiv-kernel-zero u e x p = sym (retEq (fst u , e) x)
    ∙ cong (invEq (fst u , e)) (p ∙ sym (pres1 (snd u)))
    ∙ retEq (fst u , e) _

  exact-composite : {G H K : Group₀} {u : GroupHom G H} {v : GroupHom H K}
    → Exact₃ u v → (x : fst G) → fst v (fst u x) ≡ GroupStr.1g (snd K)
  exact-composite ex x = invEq (ex _) PT.∣ x , refl ∣₁

  exact-after-equiv-zero : {G H K : Group₀} {u : GroupHom G H} {v : GroupHom H K}
    → Exact₃ u v → isEquiv (fst u) → (h : fst H) → fst v h ≡ GroupStr.1g (snd K)
  exact-after-equiv-zero {u = u} ex e h = invEq (ex h)
    PT.∣ invEq (fst u , e) h , secEq (fst u , e) h ∣₁

  exact-before-equiv-zero : {G H K : Group₀} {u : GroupHom G H} {v : GroupHom H K}
    → Exact₃ u v → isEquiv (fst v) → (x : fst G) → fst u x ≡ GroupStr.1g (snd H)
  exact-before-equiv-zero {u = u} {v = v} ex e x =
    equiv-kernel-zero v e (fst u x) (exact-composite {u = u} {v = v} ex x)

  exact-zero-map-middle : {G H K : Group₀} (u : GroupHom G H) (v : GroupHom H K)
    → Exact₃ u v → ((x : fst G) → fst u x ≡ GroupStr.1g (snd H))
    → ((h : fst H) → fst v h ≡ GroupStr.1g (snd K))
    → isContr (fst H)
  exact-zero-map-middle {H = H} u v ex uz vz = GroupStr.1g (snd H) , λ h →
    PT.rec (GroupStr.is-set (snd H) _ _)
      (λ { (x , p) → sym (sym p ∙ uz x) }) (equivFun (ex h) (vz h))

  exact-zero-middle : {G H K : Group₀} (u : GroupHom G H) (v : GroupHom H K)
    → Exact₃ u v → isContr (fst G) → isContr (fst K) → isContr (fst H)
  exact-zero-middle {G = G} {K = K} u v ex cg ck = exact-zero-map-middle u v ex
    (λ x → cong (fst u) (contr→zero G cg x) ∙ pres1 (snd u))
    (λ h → contr→zero K ck (fst v h))

  exact-zero-middle-injective : {G H K L : Group₀}
    (u : GroupHom G H) (v : GroupHom H K) (w : GroupHom K L)
    → Exact₃ u v → Exact₃ v w → isContr (fst G) → isEquiv (fst w) → isContr (fst H)
  exact-zero-middle-injective {G = G} u v w ex₁ ex₂ cg ew = exact-zero-map-middle u v ex₁
    (λ x → cong (fst u) (contr→zero G cg x) ∙ pres1 (snd u))
    (exact-before-equiv-zero {u = v} {v = w} ex₂ ew)

  exact-middle-equiv : {G H K L M : Group₀}
    (u : GroupHom G H) (v : GroupHom H K) (w : GroupHom K L) (t : GroupHom L M)
    → Exact₃ u v → Exact₃ v w → Exact₃ w t
    → isContr (fst G) → isEquiv (fst t) → isEquiv (fst v)
  exact-middle-equiv {G = G} {H = H} u v w t ex₁ ex₂ ex₃ cg et =
    snd (fst (BijectionIsoToGroupEquiv (bijIso v
      (λ x p → PT.rec (GroupStr.is-set (snd H) _ _)
        (λ { (y , q) → sym q ∙ cong (fst u) (contr→zero G cg y) ∙ pres1 (snd u) })
        (equivFun (ex₁ x) p))
      (λ x → equivFun (ex₂ x) (exact-before-equiv-zero {u = w} {v = t} ex₃ et x)))))
