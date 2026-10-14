{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.Groups where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.DirProd
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.CofibreHomology using (Exact₃)
open import DeloopS3.Bridge.DMCExactness.Groups

open IsGroupHom

-- All elimination of merely-given fibres is justified by injectivity.
-- These lemmas never unfold a cellular homology group.
abstract
  exact-ends-equiv : {G H K L : Group₀}
    (u : GroupHom G H) (v : GroupHom H K) (w : GroupHom K L)
    → Exact₃ u v → Exact₃ v w
    → isContr (fst G) → isContr (fst L) → isEquiv (fst v)
  exact-ends-equiv {G} {H} {K} {L} u v w ex₁ ex₂ cg cl =
    snd (fst (BijectionIsoToGroupEquiv (bijIso v
      (λ x p → PT.rec (GroupStr.is-set (snd H) _ _)
        (λ { (y , q) → sym q ∙ cong (fst u) (contr→zero G cg y) ∙ pres1 (snd u) })
        (equivFun (ex₁ x) p))
      (λ x → equivFun (ex₂ x) (contr→zero L cl (fst w x))))))

module KernelSequence {V P A W : Group₀}
  (u : GroupHom V P) (δ : GroupHom P A) (s : GroupHom A W)
  (atP : Exact₃ u δ) (atA : Exact₃ δ s) (vzero : isContr (fst V)) where

  into-kernel : GroupHom P (kerGroup s)
  fst into-kernel x = fst δ x , exact-composite {u = δ} {v = s} atA x
  snd into-kernel = makeIsGroupHom λ x y → kerGroup≡ s (pres· (snd δ) x y)

  abstract
    kernel-equiv : GroupEquiv P (kerGroup s)
    kernel-equiv = BijectionIsoToGroupEquiv (bijIso into-kernel
      (λ x p → PT.rec (GroupStr.is-set (snd P) _ _)
        (λ { (y , q) → sym q ∙ cong (fst u) (contr→zero V vzero y) ∙ pres1 (snd u) })
        (equivFun (atP x) (cong fst p)))
      (λ { (a , k) → PT.map
        (λ { (x , q) → x , kerGroup≡ s q }) (equivFun (atA a) k) }))

    kernel-equiv-coordinate : (x : fst P)
      → fst (equivFun (fst kernel-equiv) x) ≡ fst δ x
    kernel-equiv-coordinate x = refl

abstract
  exact-surjective-zero : {A W P : Group₀}
    (s : GroupHom A W) (j : GroupHom W P)
    → Exact₃ s j → ((w : fst W) → PT.∥ fiber (fst s) w ∥₁)
    → (w : fst W) → fst j w ≡ GroupStr.1g (snd P)
  exact-surjective-zero s j ex onto w = invEq (ex w) (onto w)

  exact-injective-zero : {P A W : Group₀}
    (δ : GroupHom P A) (s : GroupHom A W)
    → Exact₃ δ s
    → ((a : fst A) → fst s a ≡ GroupStr.1g (snd W) → a ≡ GroupStr.1g (snd A))
    → (x : fst P) → fst δ x ≡ GroupStr.1g (snd A)
  exact-injective-zero δ s ex injective x =
    injective (fst δ x) (exact-composite {u = δ} {v = s} ex x)

  middle-zero : {A₂ W₂ P₂ A₁ W₁ : Group₀}
    (s₂ : GroupHom A₂ W₂) (j₂ : GroupHom W₂ P₂)
    (δ₁ : GroupHom P₂ A₁) (s₁ : GroupHom A₁ W₁)
    → Exact₃ s₂ j₂ → Exact₃ j₂ δ₁ → Exact₃ δ₁ s₁
    → ((w : fst W₂) → PT.∥ fiber (fst s₂) w ∥₁)
    → ((a : fst A₁) → fst s₁ a ≡ GroupStr.1g (snd W₁)
        → a ≡ GroupStr.1g (snd A₁))
    → isContr (fst P₂)
  middle-zero s₂ j₂ δ₁ s₁ ex₁ ex₂ ex₃ onto injective =
    exact-zero-map-middle j₂ δ₁ ex₂
      (exact-surjective-zero s₂ j₂ ex₁ onto)
      (exact-injective-zero δ₁ s₁ ex₃ injective)

-- Coordinate changes retaining the actual map square.
module ChangeKernel {A W A′ W′ : Group₀}
  (eA : GroupEquiv A A′) (eW : GroupEquiv W W′)
  (s : GroupHom A W) (d : GroupHom A′ W′)
  (square : (a : fst A) → equivFun (fst eW) (fst s a)
    ≡ fst d (equivFun (fst eA) a)) where

  private
    zero-back : (w : fst W) → equivFun (fst eW) w ≡ GroupStr.1g (snd W′)
      → w ≡ GroupStr.1g (snd W)
    zero-back = equiv-kernel-zero (GroupEquiv→GroupHom eW) (snd (fst eW))

  kernel-map : GroupHom (kerGroup s) (kerGroup d)
  fst kernel-map (a , p) = equivFun (fst eA) a ,
    sym (square a) ∙ cong (equivFun (fst eW)) p ∙ pres1 (snd eW)
  snd kernel-map = makeIsGroupHom λ x y → kerGroup≡ d (pres· (snd eA) (fst x) (fst y))

  abstract
    kernel-change : GroupEquiv (kerGroup s) (kerGroup d)
    kernel-change = BijectionIsoToGroupEquiv (bijIso kernel-map
      (λ x p → kerGroup≡ s
        (equiv-kernel-zero (GroupEquiv→GroupHom eA) (snd (fst eA)) (fst x) (cong fst p)))
      (λ { (a′ , p) → PT.∣
        (invEq (fst eA) a′ , zero-back (fst s (invEq (fst eA) a′))
          (square (invEq (fst eA) a′) ∙ cong (fst d) (secEq (fst eA) a′) ∙ p)) ,
        kerGroup≡ d (secEq (fst eA) a′) ∣₁ }))

    kernel-change-coordinate : (x : fst (kerGroup s))
      → fst (equivFun (fst kernel-change) x) ≡ equivFun (fst eA) (fst x)
    kernel-change-coordinate x = refl

    onto-from-section : (section : fst W′ → fst A′)
      → ((w : fst W′) → fst d (section w) ≡ w)
      → (w : fst W) → PT.∥ fiber (fst s) w ∥₁
    onto-from-section section split w = PT.∣ invEq (fst eA) (section (equivFun (fst eW) w)) ,
      sym (retEq (fst eW) (fst s (invEq (fst eA) (section (equivFun (fst eW) w)))))
      ∙ cong (invEq (fst eW))
        (square (invEq (fst eA) (section (equivFun (fst eW) w)))
         ∙ cong (fst d) (secEq (fst eA) (section (equivFun (fst eW) w)))
         ∙ split (equivFun (fst eW) w))
      ∙ retEq (fst eW) w ∣₁

    injective-from-kernel :
      ((a′ : fst A′) → fst d a′ ≡ GroupStr.1g (snd W′)
        → a′ ≡ GroupStr.1g (snd A′))
      → (a : fst A) → fst s a ≡ GroupStr.1g (snd W)
      → a ≡ GroupStr.1g (snd A)
    injective-from-kernel kill a p =
      equiv-kernel-zero (GroupEquiv→GroupHom eA) (snd (fst eA)) a
        (kill (equivFun (fst eA) a)
          (sym (square a) ∙ cong (equivFun (fst eW)) p ∙ pres1 (snd eW)))
