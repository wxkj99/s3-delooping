{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Fracture.Arithmetic.LoopFiber where

-- Loop-fibre power comparisons from the pointed-circle presentation.
-- Transport the STRICT pointed-circle calculation, including its square
-- and its fibre action, along the based-circle equivalences.  The square
-- is chosen by this construction; no equality of arbitrary fillers is used.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPathrEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Sigma using (ΣPathP ; Σ-cong-equiv-snd)
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
open import DeloopS3.Local.Base using (powLoop)
open import DeloopS3.Local.Telescope using (pow∙ ; pow-refl)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (module Square)
open import DeloopS3.Local.Fracture.Arithmetic.PointedCircle

fiberAction : (A : Type) (B : Pointed ℓ-zero) (d : A → typ B)
  (u : A → A) (v : B →∙ B)
  → ((a : A) → d (u a) ≡ fst v (d a))
  → fiber d (pt B) → fiber d (pt B)
fiberAction A B d u v h (a , p) = u a , h a ∙ (cong (fst v) p ∙ snd v)

cartesian→fiberAction-isEquiv : (A : Type) (B : Pointed ℓ-zero)
  (d : A → typ B) (u : A → A) (v : B →∙ B)
  (h : (a : A) → d (u a) ≡ fst v (d a))
  → Square.Cartesian A A (typ B) (typ B) u d d (fst v) h
  → isEquiv (fiberAction A B d u v h)
cartesian→fiberAction-isEquiv A B d u v h cart =
  subst isEquiv (funExt agrees) (snd composite)
  where
  module S = Square A A (typ B) (typ B) u d d (fst v) h
  rebase : fiber d (fst v (pt B)) ≃ fiber d (pt B)
  rebase = Σ-cong-equiv-snd (λ a → compPathrEquiv (snd v))
  composite : fiber d (pt B) ≃ fiber d (pt B)
  composite = compEquiv (S.fiber-map (pt B) , S.cartesian→fiberwise cart (pt B)) rebase
  agrees : (z : fiber d (pt B)) → fst composite z ≡ fiberAction A B d u v h z
  agrees (a , p) = ΣPathP (refl , sym (assoc (h a) (cong (fst v) p) (snd v)))

private
  -- This is constructed below, not an additional hypothesis of any theorem.
  Compatible : (C A : Type) (B : Pointed ℓ-zero) (d : A → typ B)
    (e : C ≃ fiber d (pt B)) (w : C → C) (u : A → A) (v : B →∙ B) → Type
  Compatible C A B d e w u v =
    Σ[ h ∈ ((a : A) → d (u a) ≡ fst v (d a)) ]
      (fst e ∘ w ≡ fiberAction A B d u v h ∘ fst e)

module LoopedFiber (A B : Pointed ℓ-zero) (f : A →∙ B) where
  module MF = MappingFiber A B f

  W : Pointed ℓ-zero
  W = MF.W

  d : typ (Ω A) → typ (Ω B)
  d = fst (Ω→ {A = A} {B = B} f)

  private
    PA : Maps∙ A ≡ Ω A
    PA = ua∙ (circleEquiv A) (circle-point A)
    PB : Maps∙ B ≡ Ω B
    PB = ua∙ (circleEquiv B) (circle-point B)
    PW : Maps W ≡ typ (Ω W)
    PW = ua (circleEquiv W)

    d-path : PathP (λ i → typ (PA i) → typ (PB i)) (post A B f) d
    d-path = ua→ {e = circleEquiv A}
      (λ g → ua-gluePath (circleEquiv B) (circle-post A B f g))

    F-path : I → Type
    F-path i = fiber (d-path i) (pt (PB i))

  -- Chosen once, independently of the exponent r.
  loopFiberEquiv : typ (Ω W) ≃ fiber d refl
  loopFiberEquiv = transport (λ i → PW i ≃ F-path i) MF.equivalence

  private
    E-path : PathP (λ i → PW i ≃ F-path i) MF.equivalence loopFiberEquiv
    E-path = transport-filler (λ i → PW i ≃ F-path i) MF.equivalence

    u-path : (r : ℕ) → PathP (λ i → typ (PA i) → typ (PA i))
      (pre A r) (powLoop {X = typ A} {x = pt A} r)
    u-path r = ua→ {e = circleEquiv A}
      (λ g → ua-gluePath (circleEquiv A) (circle-power A r g))

    v-path : (r : ℕ) → PathP (λ i → PB i →∙ PB i) (pre∙ B r) (pow∙ r B)
    v-path r = →∙HomogeneousPathP PB PB (isHomogeneousPath (typ B) refl)
      (ua→ {e = circleEquiv B}
        (λ g → ua-gluePath (circleEquiv B) (circle-power B r g)))

    w-path : (r : ℕ) → PathP (λ i → PW i → PW i)
      (pre W r) (powLoop {X = typ W} {x = pt W} r)
    w-path r = ua→ {e = circleEquiv W}
      (λ g → ua-gluePath (circleEquiv W) (circle-power W r g))

    initial : (r : ℕ) → Compatible (Maps W) (Maps A) (Maps∙ B)
      (post A B f) MF.equivalence (pre W r) (pre A r) (pre∙ B r)
    fst (initial r) g = refl
    snd (initial r) = MF.pre-compatibility r ∙ funExt λ z →
      ΣPathP (refl , rUnit (cong (pre B r) (snd (fst MF.equivalence z)))
        ∙ lUnit (cong (pre B r) (snd (fst MF.equivalence z)) ∙ refl))

    constructed : (r : ℕ) → Compatible (typ (Ω W)) (typ (Ω A)) (Ω B)
      d loopFiberEquiv (powLoop {X = typ W} {x = pt W} r)
      (powLoop {X = typ A} {x = pt A} r) (pow∙ r B)
    constructed r = transport
      (λ i → Compatible (PW i) (typ (PA i)) (PB i) (d-path i) (E-path i)
        (w-path r i) (u-path r i) (v-path r i)) (initial r)

  powerNaturality : (r : ℕ) (p : typ (Ω A))
    → d (powLoop r p) ≡ powLoop r (d p)
  powerNaturality r = fst (constructed r)

  fiberPowerMap : (r : ℕ) → fiber d refl → fiber d refl
  fiberPowerMap r = fiberAction (typ (Ω A)) (Ω B) d
    (powLoop {X = typ A} {x = pt A} r) (pow∙ r B) (powerNaturality r)

  -- The rebase is EXACTLY Telescope.pow-refl, retained by v-path.
  fiberPowerMap-β : (r : ℕ) (p : typ (Ω A)) (q : d p ≡ refl)
    → fiberPowerMap r (p , q)
      ≡ (powLoop r p , powerNaturality r p ∙ (cong (powLoop r) q ∙ pow-refl r B))
  fiberPowerMap-β r p q = refl

  loop-fiber-power : (r : ℕ)
    → fst loopFiberEquiv ∘ powLoop {X = typ W} {x = pt W} r
      ≡ fiberPowerMap r ∘ fst loopFiberEquiv
  loop-fiber-power r = snd (constructed r)

  cartesian-power→loop-power : (r : ℕ)
    → Square.Cartesian (typ (Ω A)) (typ (Ω A)) (typ (Ω B)) (typ (Ω B))
      (powLoop {X = typ A} {x = pt A} r) d d
      (powLoop {X = typ B} {x = pt B} r) (powerNaturality r)
    → isEquiv (powLoop {X = typ W} {x = pt W} r)
  cartesian-power→loop-power r cart = isEquiv[equivFunA≃B∘f]→isEquiv[f]
    (powLoop {X = typ W} {x = pt W} r) loopFiberEquiv
    (subst isEquiv (sym (loop-fiber-power r))
      (snd (compEquiv loopFiberEquiv
        (fiberPowerMap r , cartesian→fiberAction-isEquiv (typ (Ω A)) (Ω B) d
          (powLoop {X = typ A} {x = pt A} r) (pow∙ r B) (powerNaturality r) cart))))

open LoopedFiber public using (loopFiberEquiv ; fiberPowerMap ; powerNaturality ; loop-fiber-power)
