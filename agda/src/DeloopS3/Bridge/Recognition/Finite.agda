{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.Finite where

-- Finite-cell detection of equivalences using finite choice.
open import DeloopS3.Bridge.Recognition.Notation
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence using (ua)
open import Cubical.Data.Nat
open import Cubical.Data.Bool using (true ; false)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.CW.Base using
  (CWskel ; module CWskel-fields ; finCWskel ; finCWskel→CWskel ; realise)
open import Cubical.CW.Properties using (CW₀-empty ; CWskel-elim ; realiseFin)
open import Cubical.HITs.Sn.Base using (S₊ ; S⁻ ; S₊∙ ; ptSn)
open import Cubical.HITs.Pushout.Base using (inl ; inr ; push)
open import Cubical.Homotopy.Connected
open import Cubical.Homotopy.Loopspace using (Ω^_)
open import Cubical.Homotopy.Group.Base using (π' ; π'Gr≅πGr)
open import Cubical.Axiom.Choice using (InductiveFinSatAC)
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.Truncation as TR

private
  loops-connected : (n k : ℕ) (A : Pointed ℓ-zero)
    → isConnected (n + k) (fst A)
    → isConnected k (fst ((Ω^ n) A))
  loops-connected zero k A conn = conn
  loops-connected (suc n) k A conn = isConnectedPath k
    (loops-connected n (suc k) A
      (subst (λ r → isConnected r (fst A)) (sym (+-suc n k)) conn))
    (snd ((Ω^ n) A)) (snd ((Ω^ n) A))

  merely-point : {A : Type} → isConnected 1 A → PT.∥ A ∥₁
  merely-point conn = Iso.inv TR.propTruncTrunc1Iso (fst conn)

  -- A boundary sphere can be filled merely.  This is a consequence of
  -- connectivity of iterated loops and effectiveness of set truncation.
  sphere-fill : (n : ℕ) {A : Type} → isConnected (2 + n) A
    → (s : S₊ n → A) → PT.∥ Σ[ a ∈ A ] ((z : S₊ n) → s z ≡ a) ∥₁
  sphere-fill zero conn s = PT.map
    (λ p → s true , λ { true → refl ; false → p })
    (merely-point (isConnectedPath 1 conn (s false) (s true)))
  sphere-fill (suc n) {A} conn s = PT.map
    (λ p → s (ptSn (suc n)) , λ z → cong (λ f → fst f z) p)
    (Iso.fun ST.PathIdTrunc₀Iso
      (isContr→isProp πzero ST.∣ s , refl ∣₂ ST.∣ (λ _ → s (ptSn (suc n))) , refl ∣₂))
    where
    A∙ : Pointed ℓ-zero
    A∙ = A , s (ptSn (suc n))

    πzero : isContr (π' (suc n) A∙)
    πzero = isOfHLevelRetractFromIso 0 (fst (π'Gr≅πGr n A∙))
      (isOfHLevelRetractFromIso 0 TR.setTruncTrunc2Iso
        (loops-connected (suc n) 2 A∙
          (subst (λ r → isConnected r A) (+-comm 2 (suc n)) conn)))

  boundary-fill : (n : ℕ) {A : Type} → isConnected (suc n) A
    → (s : S⁻ n → A) → PT.∥ Σ[ a ∈ A ] ((z : S⁻ n) → s z ≡ a) ∥₁
  boundary-fill zero conn s = PT.map (λ a → a , λ ()) (merely-point conn)
  boundary-fill (suc n) conn s = sphere-fill n conn s

  finite-choice : {k : ℕ} {P : Fin k → Type}
    → ((a : Fin k) → PT.∥ P a ∥₁) → PT.∥ ((a : Fin k) → P a) ∥₁
  finite-choice {k} {P} h = Iso.inv TR.propTruncTrunc1Iso
    (invEq (_ , InductiveFinSatAC 1 k P)
      (λ a → Iso.fun TR.propTruncTrunc1Iso (h a)))

-- Existence of a section over the (n-1)-skeleton, using n-connected
-- fibres.  Its path version below gives connectedness of sections.
skeleton-section : (C : CWskel ℓ-zero) (n : ℕ)
  (P : fst C n → Type)
  → ((x : fst C n) → isConnected n (P x))
  → PT.∥ ((x : fst C n) → P x) ∥₁
skeleton-section C zero P conn = PT.∣ (λ x → Empty.rec (CW₀-empty C x)) ∣₁
skeleton-section C (suc n) P conn = PT.rec PT.squash₁ attach
  (skeleton-section C n (λ x → P (invEq (e n) (inl x)))
    (λ x → isConnectedSubtr n 1 (conn (invEq (e n) (inl x)))))
  where
  open CWskel-fields C

  attach : ((x : fst C n) → P (invEq (e n) (inl x)))
    → PT.∥ ((x : fst C (suc n)) → P x) ∥₁
  attach old = PT.map build (finite-choice {k = card n} {P = Q} fillers)
    where
    Q : (c : Fin (card n)) → Type
    Q c = Σ[ v ∈ P (invEq (e n) (inr c)) ]
      ((z : S⁻ n) → PathP (λ i → P (invEq (e n) (push (c , z) i)))
        (old (α n (c , z))) v)

    fillers : (c : Fin (card n)) → PT.∥ Q c ∥₁
    fillers c = PT.map (λ (v , h) → v , λ z → toPathP (h z))
      (boundary-fill n (conn (invEq (e n) (inr c)))
        (λ z → subst (λ y → P (invEq (e n) y)) (push (c , z))
          (old (α n (c , z)))))

    build : ((c : Fin (card n)) → Q c) → (x : fst C (suc n)) → P x
    build fill = CWskel-elim C n old (λ c → fst (fill c))
      (λ c z → snd (fill c) z)

-- Transport the skeleton induction to a finite CW type, eliminating
-- its presentation only into propositional truncation.
finite-section : {X : Type} (d : ℕ) → Finite≤ d X
  → (P : X → Type) → ((x : X) → isConnected (suc d) (P x))
  → PT.∥ ((x : X) → P x) ∥₁
finite-section {X} d fin = PT.rec
  (isPropΠ2 (λ _ _ → PT.squash₁)) on-skeleton fin
  where
  on-skeleton : (Σ[ C ∈ finCWskel ℓ-zero (suc d) ]
      (X ≃ realise (finCWskel→CWskel (suc d) C)))
    → (P : X → Type) → ((x : X) → isConnected (suc d) (P x))
    → PT.∥ ((x : X) → P x) ∥₁
  on-skeleton (C , e) =
    subst (λ Y → (P : Y → Type)
      → ((x : Y) → isConnected (suc d) (P x))
      → PT.∥ ((x : Y) → P x) ∥₁)
      (sym (ua (compEquiv e (invEquiv (isoToEquiv (realiseFin (suc d) C))))))
      (skeleton-section (finCWskel→CWskel (suc d) C) (suc d))

finite-sections-connected : {X : Type} (d : ℕ)
  → Finite≤ d X → (P : X → Type)
  → ((x : X) → isConnected (d + 2) (P x))
  → isConnected 2 ((x : X) → P x)
finite-sections-connected {X} d fin P conn = PT.rec isPropIsContr center
  (finite-section d fin P (λ x → isConnectedSubtr (suc d) 1 (conn' x)))
  where
  conn' : (x : X) → isConnected (suc (suc d)) (P x)
  conn' x = subst (λ k → isConnected k (P x)) (+-comm d 2) (conn x)

  center : ((x : X) → P x) → isConnected 2 ((x : X) → P x)
  center s = TR.∣ s ∣ , TR.elim
    (λ _ → isOfHLevelPath 2 (TR.isOfHLevelTrunc 2) _ _)
    (λ t → PT.rec (TR.isOfHLevelTrunc 2 _ _)
      (λ h → cong TR.∣_∣ (funExt h))
      (finite-section d fin (λ x → s x ≡ t x)
        (λ x → isConnectedPath (suc d) (conn' x) (s x) (t x))))

finite4-detect-equiv : {A B : Type} (f : A → B)
  → Finite≤ 4 A → Finite≤ 4 B
  → isConnectedFun 6 f → isEquiv f
finite4-detect-equiv {A} {B} f finA finB conn = PT.rec (isPropIsEquiv f) with-section
  (finite-section 4 finB (fiber f)
    (λ b → isConnectedSubtr 5 1 (conn b)))
  where
  with-section : ((b : B) → fiber f b) → isEquiv f
  with-section s = PT.rec (isPropIsEquiv f)
    (λ h → isoToIsEquiv (iso f (λ b → fst (s b)) (λ b → snd (s b))
      (λ a → cong fst (h a))))
    (finite-section 4 finA
      (λ a → Path (fiber f (f a)) (s (f a)) (a , refl))
      (λ a → isConnectedPath 5 (conn (f a)) (s (f a)) (a , refl)))
