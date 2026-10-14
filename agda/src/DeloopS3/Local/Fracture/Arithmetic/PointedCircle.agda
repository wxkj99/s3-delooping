{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Arithmetic.PointedCircle where

-- The finite pointed-circle presentation.  Precomposition fixes
-- the basepoint strictly; postcomposition and precomposition commute.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (ΣPathP ; Σ-cong-equiv-snd)
open import Cubical.HITs.S1.Base using (S¹ ; base ; loop)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→ ; Ω→∘)
open import DeloopS3.Local.Base using (deg₁ ; powLoop)
open import DeloopS3.Local.Powers using (cong-powLoop)

Circle : Pointed ℓ-zero
Circle = S¹ , base

Maps : Pointed ℓ-zero → Type
Maps A = Circle →∙ A

constant : (A : Pointed ℓ-zero) → Maps A
constant A = (λ _ → pt A) , refl

Maps∙ : Pointed ℓ-zero → Pointed ℓ-zero
Maps∙ A = Maps A , constant A

pre : (A : Pointed ℓ-zero) (r : ℕ) → Maps A → Maps A
pre A r (g , p) = g ∘ deg₁ r , p

pre∙ : (A : Pointed ℓ-zero) (r : ℕ) → Maps∙ A →∙ Maps∙ A
pre∙ A r = pre A r , refl

post : (A B : Pointed ℓ-zero) → A →∙ B → Maps A → Maps B
post A B f g = f ∘∙ g

circleLoop : (A : Pointed ℓ-zero) → Maps A → typ (Ω A)
circleLoop A g = fst (Ω→ {A = Circle} {B = A} g) loop

recLoop : (A : Pointed ℓ-zero) → typ (Ω A) → Maps A
fst (recLoop A p) base = pt A
fst (recLoop A p) (loop i) = p i
snd (recLoop A p) = refl

circleIso : (A : Pointed ℓ-zero) → Iso (Maps A) (typ (Ω A))
Iso.fun (circleIso A) = circleLoop A
Iso.inv (circleIso A) = recLoop A
Iso.sec (circleIso A) p = sym (rUnit p)
Iso.ret (circleIso A) = →∙J
  (λ a g → recLoop (typ A , a) (circleLoop (typ A , a) g) ≡ g)
  (λ g → cong (recLoop (typ A , g base)) (sym (rUnit (cong g loop)))
    ∙ ΣPathP ((funExt λ { base → refl ; (loop i) → refl }) , refl))

circleEquiv : (A : Pointed ℓ-zero) → Maps A ≃ typ (Ω A)
circleEquiv A = isoToEquiv (circleIso A)

circle-point : (A : Pointed ℓ-zero) → circleLoop A (constant A) ≡ refl
circle-point A = sym (rUnit refl)

circle-power : (A : Pointed ℓ-zero) (r : ℕ) (g : Maps A)
  → circleLoop A (pre A r g) ≡ powLoop r (circleLoop A g)
circle-power A r = →∙J
  (λ a g → circleLoop (typ A , a) (pre (typ A , a) r g)
    ≡ powLoop r (circleLoop (typ A , a) g))
  (λ g → sym (rUnit (cong g (powLoop r loop)))
    ∙ cong-powLoop g r loop ∙ cong (powLoop r) (rUnit (cong g loop)))

circle-post : (A B : Pointed ℓ-zero) (f : A →∙ B) (g : Maps A)
  → circleLoop B (post A B f g) ≡ fst (Ω→ {A = A} {B = B} f) (circleLoop A g)
circle-post A B f g = Ω→∘ f g loop

-- A corner square can be read either as the pointing of a map into a
-- fibre, or as the pointing of a nullhomotopy of a pointed map.
point-square : (B : Type) {x a b : B} (α : x ≡ a) (u : a ≡ b) (h : x ≡ b)
  → Square h u α refl ≃ Square (α ∙ u) refl h refl
point-square B α u h = compEquiv flipSquareEquiv
  (compEquiv (Square≃doubleComp α refl h u)
    (compEquiv (compPathlEquiv bridge)
      (invEquiv (Square≃doubleComp (α ∙ u) refl h refl))))
  where
  bridge : (sym h ∙∙ (α ∙ u) ∙∙ refl) ≡ (sym h ∙∙ α ∙∙ u)
  bridge = doubleCompPath-elim' (sym h) (α ∙ u) refl
    ∙ cong (sym h ∙_) (sym (rUnit (α ∙ u)))
    ∙ sym (doubleCompPath-elim' (sym h) α u)

module MappingFiber (A B : Pointed ℓ-zero) (f : A →∙ B) where
  W : Pointed ℓ-zero
  W = fiber (fst f) (pt B) , pt A , snd f

  private
    Normal₁ : Type
    Normal₁ = Σ[ g ∈ (S¹ → typ A) ]
      Σ[ h ∈ ((s : S¹) → fst f (g s) ≡ pt B) ]
      Σ[ α ∈ (g base ≡ pt A) ] Square (h base) (snd f) (cong (fst f) α) refl

    Normal₂ : Type
    Normal₂ = Σ[ g ∈ (S¹ → typ A) ] Σ[ α ∈ (g base ≡ pt A) ]
      Σ[ h ∈ ((s : S¹) → fst f (g s) ≡ pt B) ]
        Square (cong (fst f) α ∙ snd f) refl (h base) refl

    unpack : Iso (Maps W) Normal₁
    Iso.fun unpack (w , β) = (fst ∘ w) , (snd ∘ w) , cong fst β , cong snd β
    Iso.inv unpack (g , h , α , δ) = (λ s → g s , h s) , ΣPathP (α , δ)
    Iso.sec unpack _ = refl
    Iso.ret unpack _ = refl

    corners : Normal₁ ≃ Normal₂
    corners = compEquiv
      (Σ-cong-equiv-snd λ g → Σ-cong-equiv-snd λ h →
        Σ-cong-equiv-snd λ α → point-square (typ B) (cong (fst f) α) (snd f) (h base))
      (isoToEquiv (iso
        (λ { (g , h , α , δ) → g , α , h , δ })
        (λ { (g , α , h , δ) → g , h , α , δ }) (λ _ → refl) (λ _ → refl)))

    pack : Iso Normal₂ (fiber (post A B f) (constant B))
    Iso.fun pack (g , α , h , δ) = (g , α) , λ i → (λ s → h s i) , δ i
    Iso.inv pack ((g , α) , q) = g , α , (λ s i → fst (q i) s) , (λ i → snd (q i))
    Iso.sec pack _ = refl
    Iso.ret pack _ = refl

  equivalence : Maps W ≃ fiber (post A B f) (constant B)
  equivalence = compEquiv (isoToEquiv unpack) (compEquiv corners (isoToEquiv pack))

  componentwise : (r : ℕ) → fiber (post A B f) (constant B)
    → fiber (post A B f) (constant B)
  componentwise r (g , q) = pre A r g , cong (pre B r) q

  pre-compatibility : (r : ℕ) → fst equivalence ∘ pre W r
    ≡ componentwise r ∘ fst equivalence
  pre-compatibility r = refl
