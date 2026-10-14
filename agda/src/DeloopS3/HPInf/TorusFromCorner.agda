{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.HPInf.TorusFromCorner where

-- A cartesian RP² corner yields a maximal torus.  No HP∞ model is used.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels using (isSet→isGroupoid)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Path using (compPathlEquiv; compPathrEquiv)
open import Cubical.Data.Sigma
open import Cubical.Functions.Fibration using (fiberEquiv)
open import Cubical.HITs.Sn.Base using (S₊)
open import Cubical.HITs.Susp.Base using (north)
open import Cubical.ZCohomology.GroupStructure using (0ₖ)
open import DeloopS3.Sphere.TruncationCartesian
  using (τ₂; η₂; τ₂-map; CartSquare; trunc₂-cartesian)
import DeloopS3.Sphere.TruncationCartesian as TC
import DeloopS3.Sphere.RP2UnitFiber as RP
open import DeloopS3.Sphere.HopfJoin using (K₂)
open import DeloopS3.Sphere.HopfUnit
  using (hopfReflectionEquiv; hopfReflection)

R N : Type
R = RP.RP²
N = τ₂ R

n₀ : N
n₀ = η₂ RP.rpBase

K₂∙ : Pointed ℓ-zero
K₂∙ = K₂ , 0ₖ 2

MaximalTorus : Pointed ℓ-zero → Type
MaximalTorus B = Σ[ t ∈ (K₂∙ →∙ B) ] fiber (fst t) (pt B) ≃ S₊ 2

-- The projection to N is part of the datum, not an arbitrary equivalence
-- between the two total spaces.
OverN : (B : Pointed ℓ-zero) (j : N → typ B) → Type
OverN B j = Σ[ e ∈ (R ≃ fiber j (pt B)) ]
  ((r : R) → fst (equivFun e r) ≡ η₂ r)

module FromCorner (B : Pointed ℓ-zero) (j : N → typ B)
  (E : Type) (α : R → E) (p : E → typ B)
  (H : (r : R) → p (α r) ≡ j (η₂ r))
  (cartesian : CartSquare η₂ p α j H)
  (contrE : isContr E) (e₀ : E) (p₀ : p e₀ ≡ pt B) where

  private
    rotateIso : Iso (TC.PB p j) (TC.PB j p)
    Iso.fun rotateIso (n , e , s) = e , n , sym s
    Iso.inv rotateIso (e , n , s) = n , e , sym s
    Iso.sec rotateIso _ = refl
    Iso.ret rotateIso _ = refl

    rotated : R ≃ TC.PB j p
    rotated = compEquiv (CartSquare.comparisonEquiv cartesian)
      (isoToEquiv rotateIso)

    toBase : (e : E) → p e ≡ pt B
    toBase e = cong p (isContr→isProp contrE e e₀) ∙ p₀

    forgetIso : Iso (E × fiber j (pt B)) (fiber j (pt B))
    Iso.fun forgetIso = snd
    Iso.inv forgetIso z = e₀ , z
    Iso.sec forgetIso z = refl
    Iso.ret forgetIso (e , z) i = isContr→isProp contrE e₀ e i , z

  cornerEquiv : R ≃ fiber j (pt B)
  cornerEquiv = compEquiv rotated
    (compEquiv
      (Σ-cong-equiv-snd (λ e → Σ-cong-equiv-snd
        (λ n → compPathrEquiv (toBase e))))
      (isoToEquiv forgetIso))

  corner-over : (r : R) → fst (equivFun cornerEquiv r) ≡ η₂ r
  corner-over r = refl

  overN : OverN B j
  overN = cornerEquiv , corner-over

module FromOverN (B : Pointed ℓ-zero) (j : N → typ B)
  (j₀ : j n₀ ≡ pt B) (corner : OverN B j) where

  private
    e : R ≃ fiber j (pt B)
    e = fst corner

    over : (r : R) → fst (equivFun e r) ≡ η₂ r
    over = snd corner

    T : Type
    T = τ₂ (S₊ 2)

    a : T → N
    a = τ₂-map RP.q

    Q : N → Type
    Q n = j n ≡ pt B

    corner-fibers : (n : N) → fiber (η₂ {A = R}) n ≃ Q n
    corner-fibers n = compEquiv
      (Σ-cong-equiv e (λ r → compPathlEquiv (over r)))
      (fiberEquiv Q n)

    cover : CartSquare RP.q a η₂ η₂ (λ _ → refl)
    cover = trunc₂-cartesian RP.q
      (λ y → isSet→isGroupoid (RP.q-fibers-are-sets y))

    swapCover : Iso (TC.PB a (η₂ {A = R}))
      (Σ[ z ∈ T ] fiber (η₂ {A = R}) (a z))
    Iso.fun swapCover (r , z , s) = z , r , sym s
    Iso.inv swapCover (z , r , s) = r , z , sym s
    Iso.sec swapCover _ = refl
    Iso.ret swapCover _ = refl

    sphere-fiber : S₊ 2 ≃ fiber (j ∘ a) (pt B)
    sphere-fiber = compEquiv (CartSquare.comparisonEquiv cover)
      (compEquiv (isoToEquiv swapCover)
        (Σ-cong-equiv-snd (λ z → corner-fibers (a z))))

    inverse-point : invEq hopfReflectionEquiv (0ₖ 2) ≡ η₂ north
    inverse-point = cong (invEq hopfReflectionEquiv) (sym (snd hopfReflection))
      ∙ retEq hopfReflectionEquiv (η₂ north)

  t : K₂∙ →∙ B
  fst t = j ∘ a ∘ invEq hopfReflectionEquiv
  snd t = cong (j ∘ a) inverse-point ∙ j₀

  t-fiber : fiber (fst t) (pt B) ≃ S₊ 2
  t-fiber = compEquiv
    (Σ-cong-equiv-fst {B = λ z → j (a z) ≡ pt B}
      (invEquiv hopfReflectionEquiv))
    (invEquiv sphere-fiber)

  maximal-torus : MaximalTorus B
  maximal-torus = t , t-fiber

module FromCartesianCorner (B : Pointed ℓ-zero) (j : N → typ B)
  (j₀ : j n₀ ≡ pt B)
  (E : Type) (α : R → E) (p : E → typ B)
  (H : (r : R) → p (α r) ≡ j (η₂ r))
  (cartesian : CartSquare η₂ p α j H) (contrE : isContr E) where

  module Corner = FromCorner B j E α p H cartesian contrE
    (α RP.rpBase) (H RP.rpBase ∙ j₀)

  open FromOverN B j j₀ Corner.overN public
    using (t; t-fiber; maximal-torus)
