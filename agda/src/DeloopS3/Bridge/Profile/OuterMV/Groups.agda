{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.OuterMV.Groups where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Subgroup using (kerGroup ; kerGroup≡)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.DMCExactness.Groups public

open IsGroupHom

-- Every endpoint here is an arbitrary group, not a cellular computation.
abstract
  product-zero : {B C : Group₀}
    → isContr (fst B) → isContr (fst C) → isContr (fst (DirProd B C))
  product-zero b0 c0 = (fst b0 , fst c0) , λ x → ΣPathP (snd b0 (fst x) , snd c0 (snd x))

  exact-left-injective : {G H K : Group₀}
    (u : GroupHom G H) (v : GroupHom H K)
    → Exact₃ u v → isContr (fst G) → isInjective v
  exact-left-injective {G = G} {H = H} u v ex cg x p =
    PT.rec (GroupStr.is-set (snd H) _ _)
      (λ { (y , q) → sym q ∙ cong (fst u) (contr→zero G cg y) ∙ pres1 (snd u) })
      (equivFun (ex x) p)

  exact-right-surjective : {G H K : Group₀}
    (u : GroupHom G H) (v : GroupHom H K)
    → Exact₃ u v → isContr (fst K) → isSurjective u
  exact-right-surjective {K = K} u v ex ck h =
    equivFun (ex h) (contr→zero K ck (fst v h))

  exact-zero-middle-mono : {G H K L : Group₀}
    (u : GroupHom G H) (v : GroupHom H K) (w : GroupHom K L)
    → Exact₃ u v → Exact₃ v w
    → isContr (fst G) → isInjective w → isContr (fst H)
  exact-zero-middle-mono {G = G} u v w ex₁ ex₂ cg iw =
    exact-zero-map-middle u v ex₁
      (λ x → cong (fst u) (contr→zero G cg x) ∙ pres1 (snd u))
      (λ x → iw (fst v x) (exact-composite {u = v} {v = w} ex₂ x))

  -- 0 → H → K → L identifies H with the actual kernel subgroup of K → L.
  -- Both lifting and injectivity use only propositional image witnesses.
  exact-zero-left-ker-equiv : {G H K L : Group₀}
    (u : GroupHom G H) (v : GroupHom H K) (w : GroupHom K L)
    → Exact₃ u v → Exact₃ v w → isContr (fst G)
    → GroupEquiv H (kerGroup w)
  exact-zero-left-ker-equiv {H = H} u v w ex₁ ex₂ cg =
    BijectionIsoToGroupEquiv (bijIso kernel-lift injective surjective)
    where
    kernel-lift : GroupHom H (kerGroup w)
    fst kernel-lift x = fst v x , exact-composite {u = v} {v = w} ex₂ x
    snd kernel-lift = makeIsGroupHom λ x y → kerGroup≡ w (pres· (snd v) x y)

    injective : isInjective kernel-lift
    injective x p = exact-left-injective u v ex₁ cg x (cong fst p)

    surjective : isSurjective kernel-lift
    surjective (x , p) = PT.map
      (λ { (h , q) → h , kerGroup≡ w q }) (equivFun (ex₂ x) p)

  exact-after-surjective-zero : {G H K : Group₀}
    (u : GroupHom G H) (v : GroupHom H K)
    → Exact₃ u v → isSurjective u
    → (x : fst H) → fst v x ≡ GroupStr.1g (snd K)
  exact-after-surjective-zero u v ex onto x = invEq (ex x) (onto x)
