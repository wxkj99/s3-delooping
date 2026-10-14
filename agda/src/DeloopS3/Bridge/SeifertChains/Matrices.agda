{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.SeifertChains.Matrices where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Subgroup
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Int
open import DeloopS3.Bridge.SeifertChains.Arithmetic

ℤ² ℤ³ ℤ⁶ : AbGroup ℓ-zero
ℤ² = dirProdAb ℤAbGroup ℤAbGroup
ℤ³ = dirProdAb ℤAbGroup ℤ²
-- Column order is (u₁,u₂,u₃,h₁,h₂,h₃), the permutation of the displayed
-- interleaved order (u₁,h₁,u₂,h₂,u₃,h₃). No generator is removed.
ℤ⁶ = dirProdAb ℤ³ ℤ³

vertex₁ : AbGroup ℓ-zero
vertex₁ = dirProdAb ℤ² (dirProdAb ℤAbGroup ℤ³)

D : AbGroupHom ℤ³ ℤ²
fst D (x , y , z) = x Z.- z , y Z.- z
snd D = makeIsGroupHom λ (x , y , z) (x' , y' , z') →
  ΣPathP (difference-add x x' z z' , difference-add y y' z z')

D-section : AbGroupHom ℤ² ℤ³
fst D-section (x , y) = x , y , pos 0
snd D-section = makeIsGroupHom λ _ _ → refl

diagonal : GroupHom ℤGroup (AbGroup→Group ℤ³)
fst diagonal t = t , t , t
snd diagonal = makeIsGroupHom λ _ _ → refl

abstract
  D-split : (v : fst ℤ²) → fst D (fst D-section v) ≡ v
  D-split (x , y) = ΣPathP (AbGroupStr.+IdR (snd ℤAbGroup) x , AbGroupStr.+IdR (snd ℤAbGroup) y)

  D-diagonal : (t : ℤ) → fst D (fst diagonal t) ≡ (pos 0 , pos 0)
  D-diagonal t = ΣPathP (Z.-Cancel t , Z.-Cancel t)

  D-kernel-diagonal : (v : fst ℤ³) → fst D v ≡ (pos 0 , pos 0)
    → v ≡ fst diagonal (snd (snd v))
  D-kernel-diagonal (x , y , z) p = ΣPathP
    (Z.-≡0 x z (cong fst p) , ΣPathP (Z.-≡0 y z (cong snd p) , refl))

D-kernel-iso : GroupIso (kerGroup D) ℤGroup
Iso.fun (fst D-kernel-iso) ((x , y , z) , _) = z
Iso.inv (fst D-kernel-iso) t = fst diagonal t , D-diagonal t
Iso.sec (fst D-kernel-iso) _ = refl
Iso.ret (fst D-kernel-iso) (v , p) = kerGroup≡ D (sym (D-kernel-diagonal v p))
snd D-kernel-iso = makeIsGroupHom λ _ _ → refl

D-kernel : GroupEquiv (kerGroup D) ℤGroup
D-kernel = GroupIso→GroupEquiv D-kernel-iso

sum₃ : AbGroupHom ℤ³ ℤAbGroup
fst sum₃ (x , y , z) = x Z.+ (y Z.+ z)
snd sum₃ = makeIsGroupHom λ (a , b , c) (d , e , f) → sum3-add a b c d e f

-- This is exactly A_raw, with only its column grouping permuted above.
Araw : (p q r : ℤ) → AbGroupHom ℤ⁶ vertex₁
fst (Araw p q r) ((u₁ , u₂ , u₃) , (h₁ , h₂ , h₃)) =
  (u₁ Z.- u₃ , u₂ Z.- u₃) ,
  (h₁ Z.+ (h₂ Z.+ h₃)) ,
  (Z.- (u₁ Z.+ p Z.· h₁)) ,
  (Z.- (u₂ Z.+ q Z.· h₂)) ,
  (Z.- ((pos 1 Z.- r) Z.· u₃ Z.+ r Z.· h₃))
snd (Araw p q r) = makeIsGroupHom λ
  { ((a , b , c) , (d , e , f)) ((a' , b' , c') , (d' , e' , f')) →
    ΣPathP (ΣPathP (difference-add a a' c c' , difference-add b b' c c') ,
    ΣPathP (sum3-add d e f d' e' f' ,
    ΣPathP (unit-row-add p a a' d d' ,
    ΣPathP (unit-row-add q b b' e e' , row-add (pos 1 Z.- r) r c c' f f')))) }

determinant : (p q r : ℤ) → ℤ
determinant p q r = p Z.· q Z.+ p Z.· r Z.+ q Z.· r Z.- p Z.· q Z.· r

-- Four unit eliminations, followed by two scalar cancellations.  In
-- particular H₂ is NOT asserted to vanish for arbitrary Seifert parameters.
abstract
  Araw-kernel : (p q r : ℤ)
    → ((x : ℤ) → q Z.· x ≡ pos 0 → x ≡ pos 0)
    → ((x : ℤ) → determinant p q r Z.· x ≡ pos 0 → x ≡ pos 0)
    → (v : fst ℤ⁶) → fst (Araw p q r) v ≡ AbGroupStr.0g (snd vertex₁)
    → v ≡ AbGroupStr.0g (snd ℤ⁶)
  Araw-kernel p q r cancel-q cancel-det ((a , b , c) , (x , y , z)) eq =
    ΣPathP (ΣPathP (ac ∙ c0 , ΣPathP (bc ∙ c0 , c0)) ,
            ΣPathP (x0 , ΣPathP (y0 , z0)))
    where
    ac : a ≡ c
    ac = Z.-≡0 a c (cong (λ v → fst (fst v)) eq)
    bc : b ≡ c
    bc = Z.-≡0 b c (cong (λ v → snd (fst v)) eq)
    h : x Z.+ (y Z.+ z) ≡ pos 0
    h = cong (λ v → fst (snd v)) eq
    za : z ≡ Z.- (x Z.+ y)
    za = solve-sum3 x y z ∙ cong (Z.- (x Z.+ y) Z.+_) h ∙ AbGroupStr.+IdR (snd ℤAbGroup) _
    first : Z.- (c Z.+ p Z.· x) ≡ pos 0
    first = cong (λ t → Z.- (t Z.+ p Z.· x)) (sym ac)
      ∙ cong (λ v → fst (snd (snd v))) eq
    ca : c ≡ Z.- (p Z.· x)
    ca = solve-unit c p x ∙ cong (λ t → (Z.- (p Z.· x)) Z.- t) first ∙ AbGroupStr.+IdR (snd ℤAbGroup) _
    e₁ : p Z.· x Z.- q Z.· y ≡ pos 0
    e₁ = sym (residual-one p q x y)
      ∙ cong (λ t → Z.- (t Z.+ q Z.· y)) (sym (bc ∙ ca))
      ∙ cong (λ v → fst (snd (snd (snd v)))) eq
    e₂ : (p Z.+ r Z.- p Z.· r) Z.· x Z.+ r Z.· y ≡ pos 0
    e₂ = sym (residual-two p r x y)
      ∙ cong₂ (λ t w → Z.- ((pos 1 Z.- r) Z.· t Z.+ r Z.· w)) (sym ca) (sym za)
      ∙ cong (λ v → snd (snd (snd (snd v)))) eq
    x0 : x ≡ pos 0
    x0 = cancel-det x (eliminate p q r x y
      ∙ cong₂ (λ t w → r Z.· t Z.+ q Z.· w) e₁ e₂
      ∙ cong₂ Z._+_ (Z.·Comm r (pos 0)) (Z.·Comm q (pos 0)))
    y0 : y ≡ pos 0
    y0 = cancel-q y (sym (Z.-Involutive (q Z.· y))
      ∙ cong Z.-_ (sym (zero-first p q y)
          ∙ cong (λ t → p Z.· t Z.- q Z.· y) (sym x0) ∙ e₁))
    c0 : c ≡ pos 0
    c0 = ca ∙ cong (λ t → Z.- (p Z.· t)) x0 ∙ cong Z.-_ (Z.·Comm p (pos 0))
    z0 : z ≡ pos 0
    z0 = za ∙ cong₂ (λ t w → Z.- (t Z.+ w)) x0 y0
