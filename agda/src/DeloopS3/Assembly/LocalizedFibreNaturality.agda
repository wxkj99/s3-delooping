{-# OPTIONS --cubical --safe #-}
module DeloopS3.Assembly.LocalizedFibreNaturality where

-- Naturality of localized fibre comparisons along the specified
-- m/n → m*n cospan, retaining its actual leg maps.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv using (fiber ; equivFun)
open import Cubical.Foundations.GroupoidLaws using (cong-∙)
open import Cubical.Data.Nat using (ℕ ; _·_)
open import DeloopS3.Local.Base using (F ; L ; η ; Local)
open import DeloopS3.Local.Unique using (module Unique)
open import DeloopS3.Assembly.LocalizationMaps using (L-map)
import DeloopS3.Local.RouteB2 as B2
import DeloopS3.Local.Fracture.Fracture.Maps as Maps
open import DeloopS3.Local.Fracture.Overlap using (product-locality)
import Cubical.HITs.Localization.Properties as Loc

data Leg : Type where
  left right : Leg

source-modulus : (m n : ℕ) → Leg → ℕ
source-modulus m n left = m
source-modulus m n right = n

-- Keeping rec outside the case split retains the unit computation even
-- for an unspecified leg. At each leg this is definitionally Maps.ι_m/n.
overlap-local : (m n : ℕ) (leg : Leg) (A : Type)
  → Local (source-modulus m n leg) (L (m · n) A)
overlap-local m n left = Maps.overlap-local-m m n
overlap-local m n right = Maps.overlap-local-n m n

jG : (m n : ℕ) (leg : Leg) (A : Type)
  → L (source-modulus m n leg) A → L (m · n) A
jG m n leg A = Loc.rec {F = F (source-modulus m n leg)}
  {X = A} {Y = L (m · n) A} (overlap-local m n leg A) (η {m · n} {A})

abstract
  jG-left : (m n : ℕ) (A : Type) → jG m n left A ≡ Maps.ι_m m n A
  jG-left m n A = refl

  jG-right : (m n : ℕ) (A : Type) → jG m n right A ≡ Maps.ι_n m n A
  jG-right m n A = refl

  jG-β : (m n : ℕ) (leg : Leg) (A : Type) (x : A)
    → jG m n leg A (η {source-modulus m n leg} {A} x) ≡ η {m · n} {A} x
  jG-β m n leg A x = refl

  factor-local : (m n : ℕ) (leg : Leg) (A : Type)
    → Local (m · n) A → Local (source-modulus m n leg) A
  factor-local m n left A lA = fst (equivFun (product-locality m n A) lA)
  factor-local m n right A lA = snd (equivFun (product-locality m n A) lA)

module Square (m n : ℕ) (leg : Leg)
  (E P E* P* : Type) (t : E → P) (t* : E* → P*)
  (a : E → E*) (b : P → P*) (H : t* ∘ a ≡ b ∘ t)
  (p₀ : P) (p*₀ : P*) (d : b p₀ ≡ p*₀) where

  r : ℕ
  r = source-modulus m n leg

  k : ℕ
  k = m · n

  UG : fiber t p₀ → fiber t* p*₀
  UG (x , s) = a x , funExt⁻ H x ∙ cong b s ∙ d

  aGᴸ : L r E → L k E*
  aGᴸ = L-map k a ∘ jG m n leg E

  bGᴸ : L r P → L k P*
  bGᴸ = L-map k b ∘ jG m n leg P

  abstract
    HᴸG : (x : L r E) → L-map k t* (aGᴸ x) ≡ bGᴸ (L-map r t x)
    HᴸG = Unique.≡onη {F = F r} {X = E} {Y = L k P*}
      (overlap-local m n leg P*) (L-map k t* ∘ aGᴸ)
      (bGᴸ ∘ L-map r t) (λ x → cong (η {k} {P*}) (funExt⁻ H x))

    HᴸG-β : (x : E) → HᴸG (η {r} {E} x) ≡ cong (η {k} {P*}) (funExt⁻ H x)
    HᴸG-β x = refl

  dᴸG : bGᴸ (η {r} {P} p₀) ≡ η {k} {P*} p*₀
  dᴸG = cong (η {k} {P*}) d

  VG : fiber (L-map r t) (η {r} {P} p₀)
    → fiber (L-map k t*) (η {k} {P*} p*₀)
  VG (x , s) = aGᴸ x , HᴸG x ∙ cong bGᴸ s ∙ dᴸG

  θG : L r (fiber t p₀) → fiber (L-map r t) (η {r} {P} p₀)
  θG = B2.fiber-comparison r t p₀

  θ* : L k (fiber t* p*₀) → fiber (L-map k t*) (η {k} {P*} p*₀)
  θ* = B2.fiber-comparison k t* p*₀

  localized-UG : L r (fiber t p₀) → L k (fiber t* p*₀)
  localized-UG = L-map k UG ∘ jG m n leg (fiber t p₀)

  abstract
    target-local : Local r (fiber (L-map k t*) (η {k} {P*} p*₀))
    target-local = factor-local m n leg _ (B2.fiber-target-local k t* p*₀)

    localized-fibre-natural-onη : (v : fiber t p₀)
      → VG (θG (η {r} {fiber t p₀} v))
        ≡ θ* (localized-UG (η {r} {fiber t p₀} v))
    localized-fibre-natural-onη (x , s) = cong
      {B = λ _ → fiber (L-map k t*) (η {k} {P*} p*₀)} (η {k} {E*} (a x) ,_)
      (cong (λ h → h ∙ cong bGᴸ (cong (η {r} {P}) s) ∙ dᴸG) (HᴸG-β x)
      ∙ sym (cong-∙ (η {k} {P*}) (funExt⁻ H x) (cong b s ∙ d)
        ∙ cong (cong (η {k} {P*}) (funExt⁻ H x) ∙_)
            (cong-∙ (η {k} {P*}) (cong b s) d)))

    localized-fibre-natural-G : VG ∘ θG ≡ θ* ∘ L-map k UG ∘ jG m n leg (fiber t p₀)
    localized-fibre-natural-G = funExt
      (Unique.≡onη {F = F r} {X = fiber t p₀}
        {Y = fiber (L-map k t*) (η {k} {P*} p*₀)} target-local
        (VG ∘ θG) (θ* ∘ localized-UG) localized-fibre-natural-onη)

    localized-fibre-natural-G-β : (v : fiber t p₀)
      → funExt⁻ localized-fibre-natural-G (η {r} {fiber t p₀} v)
        ≡ localized-fibre-natural-onη v
    localized-fibre-natural-G-β v = refl
