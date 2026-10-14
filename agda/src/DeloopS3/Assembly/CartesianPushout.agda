{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

module DeloopS3.Assembly.CartesianPushout where

open import Cubical.Foundations.Prelude renaming (J to pathJ)
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Transport
open import Cubical.Data.Sigma
open import Cubical.Functions.Fibration using (fiberEquiv; totalEquiv)
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.Pushout.Properties
  using (ΣPushout≃PushoutΣ; PushoutΣL; PushoutΣR; pushoutEquiv)
open import Cubical.HITs.Pushout.Flattening using (module FlatteningLemma)
open import DeloopS3.Sphere.TruncationCartesian
  using (CartSquare; squareComparison; cartesianHorizontalFiber)

-- All three maps land in ONE fixed base T.
module FixedBase {ℓ : Level} {A B C T : Type ℓ}
  (f : A → B) (g : A → C) (v : B → T) (w : C → T)
  (h : (a : A) → v (f a) ≡ w (g a)) where

  t : Pushout {A = A} {B = B} {C = C} f g → T
  t (inl b) = v b
  t (inr c) = w c
  t (push a i) = h a i

  module At (z : T) where
    X : Pushout {A = A} {B = B} {C = C} f g → Type ℓ
    X x = t x ≡ z

    Lz : fiber (v ∘ f) z → fiber v z
    Lz (a , s) = f a , s

    Rz : fiber (v ∘ f) z → fiber w z
    Rz (a , s) = g a , sym (h a) ∙ s

    abstract
      right-transport : (a : A) (s : v (f a) ≡ z)
        → subst X (push {f = f} {g = g} a) s ≡ sym (h a) ∙ s
      right-transport a s = substInPathsR (h a) s

      fiberwise-pushout : fiber t z ≃ Pushout Lz Rz
      fiberwise-pushout = compEquiv
        (ΣPushout≃PushoutΣ {A = A} {B = B} {C = C} f g X)
        (pushoutEquiv
          {A₁ = fiber (v ∘ f) z} {B₁ = fiber v z} {C₁ = fiber w z}
          {A₂ = fiber (v ∘ f) z} {B₂ = fiber v z} {C₂ = fiber w z}
          (PushoutΣL f g X) (PushoutΣR f g X) Lz Rz
          (idEquiv (fiber (v ∘ f) z))
          (idEquiv (fiber v z)) (idEquiv (fiber w z))
          refl (funExt λ { (a , s) → ΣPathP (refl , right-transport a s) }))

  open At public

-- No truncation or connectivity assumptions.
module CartesianPushout
  {ℓ : Level} {A B C A' B' C' : Type ℓ}
  (f : A → B) (g : A → C)
  (f' : A' → B') (g' : A' → C')
  (u : A → A') (v : B → B') (w : C → C')
  (hL : (a : A) → f' (u a) ≡ v (f a))
  (hR : (a : A) → g' (u a) ≡ w (g a))
  (cartL : CartSquare f f' u v hL)
  (cartR : CartSquare g g' u w hR) where

  E P : Type ℓ
  E = Pushout {A = A} {B = B} {C = C} f g
  P = Pushout {A = A'} {B = B'} {C = C'} f' g'

  iB : B → E
  iB = inl {f = f} {g = g}
  iC : C → E
  iC = inr {f = f} {g = g}
  jB : B' → P
  jB = inl {f = f'} {g = g'}
  jC : C' → P
  jC = inr {f = f'} {g = g'}

  t : E → P
  t (inl b) = jB (v b)
  t (inr c) = jC (w c)
  t (push a i) =
    (cong jB (sym (hL a)) ∙ push {f = f'} {g = g'} (u a)
      ∙ cong jC (hR a)) i

  FA : A' → Type ℓ
  FA = fiber u
  FB : B' → Type ℓ
  FB = fiber v
  FC : C' → Type ℓ
  FC = fiber w

  α : (a' : A') → FA a' ≃ FB (f' a')
  α a' = cartesianHorizontalFiber
    {A = A} {B = B} {C = A'} {D = B'}
    {f = f} {g = f'} {u = u} {v = v} {comm = hL} cartL a'

  β : (a' : A') → FA a' ≃ FC (g' a')
  β a' = cartesianHorizontalFiber
    {A = A} {B = C} {C = A'} {D = C'}
    {f = g} {g = g'} {u = u} {v = w} {comm = hR} cartR a'

  e : (a' : A') → FB (f' a') ≃ FC (g' a')
  e a' = compEquiv (invEquiv (α a')) (β a')

  module FL = FlatteningLemma
    {A = A'} {B = B'} {C = C'} f' g' {ℓ = ℓ} FB FC e

  D : P → Type ℓ
  D = FL.E

  -- Rotate the left pullback. This total-space map has no transport
  -- at its chosen point, which keeps both span homotopies transparent.
  aTotal : A → Σ A' (FB ∘ f')
  aTotal a = u a , f a , sym (hL a)

  private
    swapL : Iso (Σ B (λ b → fiber f' (v b))) (Σ A' (FB ∘ f'))
    Iso.fun swapL (b , a' , p) = a' , b , sym p
    Iso.inv swapL (a' , b , p) = b , a' , sym p
    Iso.sec swapL _ = refl
    Iso.ret swapL _ = refl

  abstract
    aTotal-isEquiv : isEquiv aTotal
    aTotal-isEquiv = snd (compEquiv
      (CartSquare.comparisonEquiv cartL) (isoToEquiv swapL))

    α-base : (a : A) → equivFun (α (u a)) (a , refl) ≡ (f a , sym (hL a))
    α-base a = transportRefl (f a , sym (hL a))

    β-base : (a : A) → equivFun (β (u a)) (a , refl) ≡ (g a , sym (hR a))
    β-base a = transportRefl (g a , sym (hR a))

    e-base : (a : A)
      → equivFun (e (u a)) (f a , sym (hL a)) ≡ (g a , sym (hR a))
    e-base a = cong (equivFun (e (u a))) (sym (α-base a))
      ∙ cong (equivFun (β (u a))) (retEq (α (u a)) (a , refl))
      ∙ β-base a

  bTotal : B → Σ B' FB
  bTotal b = v b , b , refl
  cTotal : C → Σ C' FC
  cTotal c = w c , c , refl

  left-span : (a : A) → bTotal (f a) ≡ FL.Σf (aTotal a)
  left-span a i = hL a (~ i) , f a , (λ j → hL a (~ i ∨ ~ j))

  right-span : (a : A) → cTotal (g a) ≡ FL.Σg (aTotal a)
  right-span a = ΣPathP (sym (hR a) , q)
    where
    q : PathP (λ i → FC (hR a (~ i))) (g a , refl)
          (equivFun (e (u a)) (f a , sym (hL a)))
    q = subst
      (λ y → PathP (λ i → FC (hR a (~ i))) (g a , refl) y)
      (sym (e-base a))
      (λ i → g a , (λ j → hR a (~ i ∨ ~ j)))

  spanEquiv : E ≃ Pushout FL.Σf FL.Σg
  spanEquiv = pushoutEquiv
    {A₁ = A} {B₁ = B} {C₁ = C}
    {A₂ = Σ A' (FB ∘ f')} {B₂ = Σ B' FB} {C₂ = Σ C' FC}
    f g FL.Σf FL.Σg
    (aTotal , aTotal-isEquiv) (totalEquiv v) (totalEquiv w)
    (funExt left-span) (funExt right-span)

  totalComparison : E → Σ P D
  totalComparison = FL.FlattenIso.fwd ∘ equivFun spanEquiv

  abstract
    totalComparison-isEquiv : isEquiv totalComparison
    totalComparison-isEquiv = snd (compEquiv spanEquiv (invEquiv FL.flatten))

  private
    kB : Σ B' FB → Pushout FL.Σf FL.Σg
    kB = inl {f = FL.Σf} {g = FL.Σg}
    kC : Σ C' FC → Pushout FL.Σf FL.Σg
    kC = inr {f = FL.Σf} {g = FL.Σg}
    kPush : (a : A) → kB (FL.Σf (aTotal a)) ≡ kC (FL.Σg (aTotal a))
    kPush a = push {f = FL.Σf} {g = FL.Σg} (aTotal a)

  -- The projection comparison includes the seam, not only the vertices.
  abstract
    projection-seam : (a : A)
      → cong (fst ∘ totalComparison) (push {f = f} {g = g} a)
        ≡ (cong jB (sym (hL a)) ∙ push {f = f'} {g = g'} (u a)
             ∙ cong jC (hR a))
    projection-seam a =
      cong-∙∙ {A = Pushout FL.Σf FL.Σg} {B = P}
        (fst ∘ FL.FlattenIso.fwd)
        (cong kB (left-span a)) (kPush a) (cong kC (sym (right-span a)))
      ∙ doubleCompPath-elim'
        (cong jB (sym (hL a))) (push {f = f'} {g = g'} (u a))
        (cong jC (hR a))

  projection : (x : E) → fst (totalComparison x) ≡ t x
  projection (inl b) = refl
  projection (inr c) = refl
  projection (push a i) j = projection-seam a j i

  -- Rectify the projection so that fst J is definitionally the stated t.
  s : (x : E) → D (t x)
  s x = subst D (projection x) (snd (totalComparison x))

  J : E → Σ P D
  J x = t x , s x

  abstract
    J-isEquiv : isEquiv J
    J-isEquiv = subst (λ k → isEquiv k)
      (funExt λ x → ΣPathP (projection x ,
        subst-filler D (projection x) (snd (totalComparison x))))
      totalComparison-isEquiv

  λB : (b' : B') → fiber v b' → fiber t (jB b')
  λB b' (b , p) = iB b , cong jB p

  λC : (c' : C') → fiber w c' → fiber t (jC c')
  λC c' (c , p) = iC c , cong jC p

  K : (p : P) → fiber t p → D p
  K p (x , q) = subst D q (s x)

  abstract
    K-isEquiv : (p : P) → isEquiv (K p)
    K-isEquiv p = snd (compEquiv
      (Σ-cong-equiv-fst {A = E} {A' = Σ P D}
        {B = λ y → fst y ≡ p} (J , J-isEquiv))
      (fiberEquiv {B = P} D p))

    K-λB : (b' : B') (y : fiber v b') → K (jB b') (λB b' y) ≡ y
    K-λB b' (b , p) = pathJ
      {x = v b}
      (λ (b'' : B') q → K (jB b'') (λB b'' (b , q)) ≡ (b , q))
      (transportRefl (s (iB b)) ∙ transportRefl (b , refl)) p

    K-λC : (c' : C') (y : fiber w c') → K (jC c') (λC c' y) ≡ y
    K-λC c' (c , p) = pathJ
      {x = w c}
      (λ (c'' : C') q → K (jC c'') (λC c'' (c , q)) ≡ (c , q))
      (transportRefl (s (iC c)) ∙ transportRefl (c , refl)) p

    λB-isEquiv : (b' : B') → isEquiv (λB b')
    λB-isEquiv b' = isEquiv→sectionIsEquiv
      {A = fiber t (jB b')} {B = fiber v b'}
      {f = K (jB b')} {g = λB b'} (K-isEquiv (jB b')) (K-λB b')

    λC-isEquiv : (c' : C') → isEquiv (λC c')
    λC-isEquiv c' = isEquiv→sectionIsEquiv
      {A = fiber t (jC c')} {B = fiber w c'}
      {f = K (jC c')} {g = λC c'} (K-isEquiv (jC c')) (K-λC c')

  private
    swapB : Iso (Σ B' (λ b' → fiber t (jB b')))
                (Σ E (λ x → fiber jB (t x)))
    Iso.fun swapB (b' , x , p) = x , b' , sym p
    Iso.inv swapB (x , b' , p) = b' , x , sym p
    Iso.sec swapB _ = refl
    Iso.ret swapB _ = refl

    swapC : Iso (Σ C' (λ c' → fiber t (jC c')))
                (Σ E (λ x → fiber jC (t x)))
    Iso.fun swapC (c' , x , p) = x , c' , sym p
    Iso.inv swapC (x , c' , p) = c' , x , sym p
    Iso.sec swapC _ = refl
    Iso.ret swapC _ = refl

  abstract
    descend-left : CartSquare iB jB v t (λ _ → refl)
    CartSquare.comparison-isEquiv descend-left = snd (compEquiv
      (totalEquiv {B = B'} {E = B} v)
      (compEquiv
        (Σ-cong-equiv-snd {A = B'} {B = FB}
          {B' = λ b' → fiber t (jB b')}
          (λ b' → λB b' , λB-isEquiv b'))
        (isoToEquiv swapB)))

    descend-right : CartSquare iC jC w t (λ _ → refl)
    CartSquare.comparison-isEquiv descend-right = snd (compEquiv
      (totalEquiv {B = C'} {E = C} w)
      (compEquiv
        (Σ-cong-equiv-snd {A = C'} {B = FC}
          {B' = λ c' → fiber t (jC c')}
          (λ c' → λC c' , λC-isEquiv c'))
        (isoToEquiv swapC)))
