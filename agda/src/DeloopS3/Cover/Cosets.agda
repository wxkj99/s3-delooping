{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cover.Cosets where

-- Coset-cover equivalences use no finiteness or choice.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Functions.Embedding
open import Cubical.Functions.Surjection
open import Cubical.Functions.Fibration using (fiber≡)
import Cubical.HITs.SetQuotients as SQ
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.HITs.EilenbergMacLane1.Base
import Cubical.HITs.EilenbergMacLane1.Properties as EM
import Cubical.Homotopy.EilenbergMacLane.Properties as ΩEM
open import DeloopS3.Groups.Bmap public

private
  variable
    ℓ ℓH ℓG ℓO ℓA ℓB ℓD : Level
    H : Group ℓH
    G : Group ℓG

record SubgroupEmbedding (H : Group ℓH) (G : Group ℓG)
  : Type (ℓ-max ℓH ℓG) where
  constructor subgroupEmbedding
  field
    hom : GroupHom H G
    mono : isMono hom
open SubgroupEmbedding public

-- Encode/decode is used only at the basepoint; propositions extend to all
-- points by EM₁ elimination. This avoids normalizing a large concrete group.
loopCode : (G : Group ℓG) → Path (EM₁ G) embase embase → G .fst
loopCode G = Iso.fun (ΩEM.ΩEM₁Iso G)

loopCode-loop : (G : Group ℓG) (g : G .fst)
  → loopCode G (emloop g) ≡ g
loopCode-loop G = Iso.sec (ΩEM.ΩEM₁Iso G)

loop-codeLoop : (G : Group ℓG) (p : Path (EM₁ G) embase embase)
  → emloop (loopCode G p) ≡ p
loop-codeLoop G = Iso.ret (ΩEM.ΩEM₁Iso G)

emloop-injective : (G : Group ℓG) {g h : G .fst}
  → emloop {Group = G} g ≡ emloop h → g ≡ h
emloop-injective G {g} {h} p = sym (loopCode-loop G g)
  ∙ cong (loopCode G) p ∙ loopCode-loop G h

abstract
  Bmap-faithful : (j : SubgroupEmbedding H G) (x y : EM₁ H)
    → isEmbedding (cong {x = x} {y = y} (Bmap (hom j)))
  Bmap-faithful {H = H} {G = G} j = EM.elimProp2 H
    (λ x y → isPropIsEmbedding) (injEmbedding (emsquash embase embase) inject)
    where
    inject : {p q : Path (EM₁ H) embase embase}
      → cong (Bmap (hom j)) p ≡ cong (Bmap (hom j)) q → p ≡ q
    inject {p} {q} e = sym (loop-codeLoop H p)
      ∙ cong emloop (mono j (emloop-injective G
          (cong (cong (Bmap (hom j))) (loop-codeLoop H p)
           ∙ e ∙ sym (cong (cong (Bmap (hom j))) (loop-codeLoop H q)))))
      ∙ loop-codeLoop H q

  subgroupCover : (j : SubgroupEmbedding H G) (b : EM₁ G)
    → isSet (fiber (Bmap (hom j)) b)
  subgroupCover j b u v = subst isProp (sym (fiber≡ u v))
    (isEmbedding→hasPropFibers (Bmap-faithful j (u .fst) (v .fst))
      (u .snd ∙∙ refl ∙∙ sym (v .snd)))

CosetFamily : {H : Group ℓH} {G : Group ℓG}
  → (j : SubgroupEmbedding H G) → EM₁ G → hSet (ℓ-max ℓH ℓG)
CosetFamily j b = fiber (Bmap (hom j)) b , subgroupCover j b

PB : {A : Type ℓA} {B : Type ℓB} {D : Type ℓD}
  → (A → D) → (B → D) → Type (ℓ-max ℓA (ℓ-max ℓB ℓD))
PB {A = A} {B = B} f g = Σ[ a ∈ A ] Σ[ b ∈ B ] f a ≡ g b

O_H : {H : Group ℓH} {G : Group ℓG} {O : Type ℓO} (j : SubgroupEmbedding H G)
  → (O → EM₁ G) → Type (ℓ-max ℓO (ℓ-max ℓH ℓG))
O_H {O = O} j ρ = Σ[ x ∈ O ] CosetFamily j (ρ x) .fst

coverToBase : {O : Type ℓO} (j : SubgroupEmbedding H G)
  (ρ : O → EM₁ G) → O_H j ρ → O
coverToBase j ρ = fst

coverToSubgroup : {O : Type ℓO} (j : SubgroupEmbedding H G)
  (ρ : O → EM₁ G) → O_H j ρ → EM₁ H
coverToSubgroup j ρ z = z .snd .fst

subgroupCoverPullback : {O : Type ℓO} (j : SubgroupEmbedding H G)
  (ρ : O → EM₁ G) → O_H j ρ ≃ PB ρ (Bmap (hom j))
subgroupCoverPullback j ρ = isoToEquiv
  (iso (λ (x , y , p) → x , y , sym p)
       (λ (x , y , p) → x , y , sym p)
       (λ _ → refl) (λ _ → refl))

subgroupCoverPullback-base : {O : Type ℓO} (j : SubgroupEmbedding H G)
  (ρ : O → EM₁ G) (z : O_H j ρ)
  → subgroupCoverPullback j ρ .fst z .fst ≡ coverToBase j ρ z
subgroupCoverPullback-base j ρ z = refl

subgroupCoverPullback-subgroup : {O : Type ℓO} (j : SubgroupEmbedding H G)
  (ρ : O → EM₁ G) (z : O_H j ρ)
  → subgroupCoverPullback j ρ .fst z .snd .fst ≡ coverToSubgroup j ρ z
subgroupCoverPullback-subgroup j ρ z = refl

pullbackCosetFamily : {C : Type ℓO} (j : SubgroupEmbedding H G)
  (f : C → EM₁ G)
  → PB (Bmap (hom j)) f ≃ (Σ[ y ∈ C ] CosetFamily j (f y) .fst)
pullbackCosetFamily j f = isoToEquiv
  (iso (λ (x , y , p) → y , x , p)
       (λ (y , x , p) → x , y , p)
       (λ _ → refl) (λ _ → refl))

-- The orientation of the cover action: fibre transport appends the base
-- path on the RIGHT, rather than appending its inverse.
fiber-transport : {A : Type ℓA} {B : Type ℓB} (f : A → B)
  {b b' : B} (q : b ≡ b') (z : fiber f b)
  → subst (fiber f) q z ≡ (z .fst , z .snd ∙ q)
fiber-transport f {b} q z = J
  (λ b' q → subst (fiber f) q z ≡ (z .fst , z .snd ∙ q))
  (substRefl {B = fiber f} z ∙ (λ k → z .fst , rUnit (z .snd) k)) q

cosetPoint : (j : SubgroupEmbedding H G) → G .fst → CosetFamily j embase .fst
cosetPoint j g = embase , emloop g

cosetPoint-action : (j : SubgroupEmbedding H G) (g t : G .fst)
  → subst (λ b → CosetFamily j b .fst) (emloop t) (cosetPoint j g)
    ≡ cosetPoint j (GroupStr._·_ (G .snd) g t)
cosetPoint-action {G = G} j g t = fiber-transport (Bmap (hom j)) (emloop t) (cosetPoint j g)
  ∙ (λ k → embase , emloop-comp G g t (~ k))

-- Actual right cosets H\G, not just a suggestive name for the fibre.
-- g ~ h means g = j(a) h; quotients need not start with a truncated
-- relation, since their equality types are propositions already.
module RightCosets {H : Group ℓH} {G : Group ℓG}
  (j : SubgroupEmbedding H G) where
  private
    module G = GroupStr (G .snd)
    jh = hom j

  Rel : G .fst → G .fst → Type (ℓ-max ℓH ℓG)
  Rel g h = Σ[ a ∈ H .fst ] jh .fst a G.· h ≡ g

  Cosets : Type (ℓ-max ℓH ℓG)
  Cosets = (G .fst) SQ./ Rel

  point-respects : (g h : G .fst) → Rel g h → cosetPoint j g ≡ cosetPoint j h
  point-respects g h (a , eq) k = emloop a k , square k
    where
    square : Square (emloop g) (emloop h) (emloop (jh .fst a)) refl
    square = compPath→Square
      (sym (emloop-comp G (jh .fst a) h) ∙ cong emloop eq ∙ rUnit (emloop g))

  toFiber : Cosets → CosetFamily j embase .fst
  toFiber = SQ.rec (subgroupCover j embase) (cosetPoint j) point-respects

  point-effective : (g h : G .fst) → cosetPoint j g ≡ cosetPoint j h → Rel g h
  point-effective g h p = a , emloop-injective G
    (emloop-comp G (jh .fst a) h
     ∙ cong (_∙ emloop h) (cong (cong (Bmap jh)) (loop-codeLoop H (cong fst p)))
     ∙ Square→compPath (λ k l → p k .snd l)
     ∙ sym (rUnit (emloop g)))
    where
    a = loopCode H (cong fst p)

  toFiber-injective : (x y : Cosets) → toFiber x ≡ toFiber y → x ≡ y
  toFiber-injective = SQ.elimProp2
    {P = λ x y → toFiber x ≡ toFiber y → x ≡ y}
    (λ x y → isPropΠ λ _ → SQ.squash/ x y)
    (λ g h p → SQ.eq/ g h (point-effective g h p))

  toFiber-surjective : isSurjection toFiber
  toFiber-surjective (x , p) = EM.elimProp H
    {B = λ x → (p : Bmap jh x ≡ embase) → PT.∥ fiber toFiber (x , p) ∥₁}
    (λ x → isPropΠ λ p → PT.squash₁)
    (λ p → PT.∣ SQ.[ loopCode G p ] , (λ k → embase , loop-codeLoop G p k) ∣₁) x p

  cosets≃fiber : Cosets ≃ CosetFamily j embase .fst
  cosets≃fiber = toFiber , isEmbedding×isSurjection→isEquiv
    (injEmbedding (subgroupCover j embase) (toFiber-injective _ _) , toFiber-surjective)

  fiber≃cosets : CosetFamily j embase .fst ≃ Cosets
  fiber≃cosets = invEquiv cosets≃fiber

  rightAction : G .fst → Cosets → Cosets
  rightAction t = SQ.rec SQ.squash/ (λ g → SQ.[ g G.· t ])
    (λ g h (a , eq) → SQ.eq/ (g G.· t) (h G.· t)
      (a , G.·Assoc (jh .fst a) h t ∙ cong (G._· t) eq))

  rightAction-unit : (x : Cosets) → rightAction G.1g x ≡ x
  rightAction-unit = SQ.elimProp (λ x → SQ.squash/ _ _)
    (λ g → cong SQ.[_] (G.·IdR g))

  rightAction-product : (t u : G .fst) (x : Cosets)
    → rightAction u (rightAction t x) ≡ rightAction (t G.· u) x
  rightAction-product t u = SQ.elimProp (λ x → SQ.squash/ _ _)
    (λ g → cong SQ.[_] (sym (G.·Assoc g t u)))

  transport-is-rightAction : (t : G .fst) (x : Cosets)
    → subst (λ b → CosetFamily j b .fst) (emloop t) (toFiber x)
      ≡ toFiber (rightAction t x)
  transport-is-rightAction t = SQ.elimProp
    {P = λ x → subst (λ b → CosetFamily j b .fst) (emloop t) (toFiber x)
      ≡ toFiber (rightAction t x)}
    (λ x → subgroupCover j embase _ _) (λ g → cosetPoint-action j g t)
