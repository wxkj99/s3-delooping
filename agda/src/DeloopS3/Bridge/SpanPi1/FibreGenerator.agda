{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Bridge.SpanPi1.FibreGenerator where

-- The actual circle-fibre loop generates the kernel of the bundle leg.
-- Integer powers need not be injective: the connecting map from π₂(RP 2)
-- can impose torsion in this image.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Isomorphism using (Iso)
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Data.Sigma
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Int using (ℤ; pos)
open import Cubical.Algebra.Group.Base using (Group; GroupStr)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.Group.ZAction
  using (_ℤ[_]·_; homPresℤ·; rUnitℤ·; rUnitℤ·ℤ)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop; emloop-comp)
open import Cubical.HITs.Pushout.Base using (inr)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
open import Cubical.Homotopy.EilenbergMacLane.Properties using (ΩEM₁Iso)
import DeloopS3.Move.CancelMinimal as Circle
import DeloopS3.Seifert.MarkedSeifert.FinalDone as Final
open import DeloopS3.Bridge.OriginalSpan
open import DeloopS3.Bridge.SpanPi1.Fibre

abstract
  -- Retain the projected-loop equation while changing the fibre's
  -- pointing path; doing only a type equivalence would lose this marking.
  lift-null-loop : ∀ {ℓ ℓ'} {Y : Type ℓ} {Z : Type ℓ'}
    (f : Y → Z) (a : Y) (b : Z) (pointing : f a ≡ b)
    (s : a ≡ a) → cong f s ≡ refl
    → Σ[ l ∈ Path (fiber f b) (a , pointing) (a , pointing) ]
        cong fst l ≡ s
  lift-null-loop f a b pointing = J
    (λ b pointing → (s : a ≡ a) → cong f s ≡ refl
      → Σ[ l ∈ Path (fiber f b) (a , pointing) (a , pointing) ]
          cong fst l ≡ s)
    (λ s h → (λ i → s i , (λ j → h j i)) , refl) pointing

module CircleFibre {ℓ ℓ'} {Y : Type ℓ} {Z : Type ℓ'}
  (f : Y → Z) (b : Z) (chart : Circle.C ≃ fiber f b) where

  point : Y
  point = fst (equivFun chart Circle.0C)
  pointing : f point ≡ b
  pointing = snd (equivFun chart Circle.0C)
  include : Circle.C → Y
  include = fst ∘ equivFun chart
  module F = Map f point

  power : ℤ → fst F.sourceπ
  power n = ST.∣ cong include (emloop n) ∣₂
  generator : fst F.sourceπ
  generator = power (pos 1)

  abstract
    powerHom : GroupHom ℤGroup F.sourceπ
    powerHom = power , makeIsGroupHom λ n m → cong ST.∣_∣₂
      (cong (cong include) (emloop-comp ℤGroup n m)
        ∙ cong-∙ include (emloop n) (emloop m))

    power-is-power : (n : ℤ) → power n ≡ n ℤ[ F.sourceπ ]· generator
    power-is-power n = cong power (sym (rUnitℤ·ℤ n))
      ∙ homPresℤ· powerHom (pos 1) n

    -- This is generation of the UNTRUNCATED fibre loop type by emloop n,
    -- transported by precisely chart, with its inverse laws retained.
    fibre-loop-word : (l : Path (fiber f b)
      (equivFun chart Circle.0C) (equivFun chart Circle.0C))
      → Σ[ n ∈ ℤ ] cong (equivFun chart) (emloop n) ≡ l
    fibre-loop-word l = n , cong (cong (equivFun chart))
      (Iso.ret (ΩEM₁Iso ℤGroup) s) ∙ secEq loopEquiv l
      where
      loopEquiv : (Circle.0C ≡ Circle.0C)
        ≃ (equivFun chart Circle.0C ≡ equivFun chart Circle.0C)
      loopEquiv = congEquiv {x = Circle.0C} {y = Circle.0C} chart
      s : Circle.0C ≡ Circle.0C
      s = invEq loopEquiv l
      n : ℤ
      n = Iso.fun (ΩEM₁Iso ℤGroup) s

    kernel-word : (s : point ≡ point) → cong f s ≡ refl
      → Σ[ n ∈ ℤ ] cong include (emloop n) ≡ s
    kernel-word s h = fst word , cong (cong fst) (snd word) ∙ snd lifted
      where
      lifted : Σ[ l ∈ Path (fiber f b)
        (point , pointing) (point , pointing) ] cong fst l ≡ s
      lifted = lift-null-loop f point b pointing s h
      word : Σ[ n ∈ ℤ ]
        cong (equivFun chart) (emloop n) ≡ fst lifted
      word = fibre-loop-word (fst lifted)

    kernel-generated : (u : fst F.sourceπ) → F.mapπ u ≡ ST.∣ refl ∣₂
      → PT.∥ Σ[ n ∈ ℤ ] (n ℤ[ F.sourceπ ]· generator) ≡ u ∥₁
    kernel-generated = ST.elim
      (λ _ → isProp→isSet (isPropΠ (λ _ → PT.squash₁)))
      (λ s eq → PT.rec PT.squash₁
        (λ h → PT.∣ fst (kernel-word s h) ,
          sym (power-is-power (fst (kernel-word s h)))
            ∙ cong ST.∣_∣₂ (snd (kernel-word s h)) ∣₁)
        (Iso.fun ST.PathIdTrunc₀Iso eq))

    power-in-kernel : (n : ℤ) → F.mapπ (power n) ≡ ST.∣ refl ∣₂
    power-in-kernel n = cong ST.∣_∣₂
      (fibre-loop-null f point b pointing (cong (equivFun chart) (emloop n)))

    -- Universal normal-generation form: killing the marked fibre loop
    -- kills the whole kernel in any target group, with no choice principle.
    kill-generator-kills-kernel : ∀ {ℓG} (G : Group ℓG)
      (h : GroupHom F.sourceπ G)
      → fst h generator ≡ GroupStr.1g (snd G)
      → (u : fst F.sourceπ) → F.mapπ u ≡ ST.∣ refl ∣₂
      → fst h u ≡ GroupStr.1g (snd G)
    kill-generator-kills-kernel G h kill u ku =
      PT.rec (GroupStr.is-set (snd G) _ _)
        (λ { (n , eq) → cong (fst h) (sym eq)
          ∙ homPresℤ· h generator n
          ∙ cong (λ t → n ℤ[ G ]· t) kill ∙ rUnitℤ· G n })
        (kernel-generated u ku)

abstract
  qπ-kernel-generated : (c : ShortCase) (u : fst (Aπ c))
    → qπ c u ≡ GroupStr.1g (snd (Rπ c))
    → PT.∥ Σ[ n ∈ ℤ ] (n ℤ[ Aπ c ]· rπ c) ≡ u ∥₁
  qπ-kernel-generated c = CircleFibre.kernel-generated
    (q c) (inr tt) (invEquiv (Final.capFibre (pos (e c))))

  qπ-kill-r-kills-kernel : ∀ {ℓG} (c : ShortCase) (G : Group ℓG)
    (h : GroupHom (Aπ c) G)
    → fst h (rπ c) ≡ GroupStr.1g (snd G)
    → (u : fst (Aπ c)) → qπ c u ≡ GroupStr.1g (snd (Rπ c))
    → fst h u ≡ GroupStr.1g (snd G)
  qπ-kill-r-kills-kernel c = CircleFibre.kill-generator-kills-kernel
    (q c) (inr tt) (invEquiv (Final.capFibre (pos (e c))))
