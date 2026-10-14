{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.Cases where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc ; abs)
import Cubical.Data.Int as Z
open import Cubical.Data.Fin using (isContrFin1)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Algebra.Group.ZAction using (ℤ/imIso)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.Int
open import Cubical.Algebra.CommRing.Instances.Int
open import Cubical.Tactics.CommRingSolver
open import DeloopS3.Bridge.SeifertChains.Matrices
open import DeloopS3.Bridge.Profile.H1Data.Cokernel
open import DeloopS3.Bridge.Profile.H1Data.Linear
open import DeloopS3.Bridge.Profile.H1Data.Raw

product-iso : {A B C D : Group₀} → GroupIso A B → GroupIso C D
  → GroupIso (DirProd A C) (DirProd B D)
Iso.fun (fst (product-iso f g)) (a , c) = Iso.fun (fst f) a , Iso.fun (fst g) c
Iso.inv (fst (product-iso f g)) (b , d) = Iso.inv (fst f) b , Iso.inv (fst g) d
Iso.sec (fst (product-iso f g)) (b , d) = ΣPathP (Iso.sec (fst f) b , Iso.sec (fst g) d)
Iso.ret (fst (product-iso f g)) (a , c) = ΣPathP (Iso.ret (fst f) a , Iso.ret (fst g) c)
snd (product-iso f g) = makeIsGroupHom λ a b →
  ΣPathP (IsGroupHom.pres· (snd f) (fst a) (fst b) , IsGroupHom.pres· (snd g) (snd a) (snd b))

forget-right : (G H : Group₀) → isContr (fst H) → GroupIso (DirProd G H) G
Iso.fun (fst (forget-right G H c)) = fst
Iso.inv (fst (forget-right G H c)) x = x , fst c
Iso.sec (fst (forget-right G H c)) _ = refl
Iso.ret (fst (forget-right G H c)) (x , y) = ΣPathP (refl , snd c y)
snd (forget-right G H c) = makeIsGroupHom λ _ _ → refl

forget-left : (G H : Group₀) → isContr (fst G) → GroupIso (DirProd G H) H
Iso.fun (fst (forget-left G H c)) = snd
Iso.inv (fst (forget-left G H c)) y = fst c , y
Iso.sec (fst (forget-left G H c)) _ = refl
Iso.ret (fst (forget-left G H c)) (x , y) = ΣPathP (snd c x , refl)
snd (forget-left G H c) = makeIsGroupHom λ _ _ → refl

scale : ℕ → AbGroupHom ℤAbGroup ℤAbGroup
fst (scale n) x = pos n Z.· x
snd (scale n) = makeIsGroupHom λ x y → Z.·DistR+ (pos n) x y

diagonal₂ : ℕ → ℕ → AbGroupHom ℤ² ℤ²
diagonal₂ m n = product-hom (scale m) (scale n)

abstract
  scale-cokernel : (n : ℕ) → GroupIso (Coker (scale n)) (ℤGroup/ n)
  scale-cokernel n = subst (λ z → GroupIso (Coker (scale n)) (ℤGroup/ abs z))
    (Z.·IdR (pos n)) (ℤ/imIso (scale n))

  diagonal-cokernel : (m n : ℕ)
    → GroupIso (Coker (diagonal₂ m n)) (DirProd (ℤGroup/ m) (ℤGroup/ n))
  diagonal-cokernel m n = compGroupIso (coker-product (scale m) (scale n))
    (product-iso (scale-cokernel m) (scale-cokernel n))

-- Concrete unit operations. All inverses are the integral adjugates of
-- the following determinant-one matrices (Linear.unimodular).
O-columns I-columns Q₄-columns Q₃-columns Q-rows Q₃-rows identity₂ : GroupIso (AbGroup→Group ℤ²) (AbGroup→Group ℤ²)
O-columns = unimodular (pos 4) (pos 1) (pos 3) (pos 1) refl
I-columns = unimodular (pos 5) (pos 3) (pos 3) (pos 2) refl
Q₄-columns = unimodular (pos 1) (pos 2) (pos 0) (pos 1) refl
Q₃-columns = unimodular (negsuc 0) (pos 3) (negsuc 0) (pos 2) refl
Q-rows = unimodular (pos 0) (negsuc 0) (pos 1) (pos 1) refl
Q₃-rows = unimodular (pos 0) (negsuc 0) (pos 1) (negsuc 0) refl
identity₂ = unimodular (pos 1) (pos 0) (pos 0) (pos 1) refl

abstract
  O-diagonal : (v : fst ℤ²)
    → Iso.fun (fst identity₂) (fst (B (pos 3) (pos 4)) (Iso.fun (fst O-columns) v))
      ≡ fst (diagonal₂ 2 1) v
  O-diagonal (x , y) = ΣPathP ((solve! ℤCommRing) , (solve! ℤCommRing))

  I-diagonal : (v : fst ℤ²)
    → Iso.fun (fst identity₂) (fst (B (pos 3) (pos 5)) (Iso.fun (fst I-columns) v))
      ≡ fst (diagonal₂ 1 1) v
  I-diagonal (x , y) = ΣPathP ((solve! ℤCommRing) , (solve! ℤCommRing))

  Q₄-diagonal : (v : fst ℤ²)
    → Iso.fun (fst Q-rows) (fst (B (pos 2) (pos 4)) (Iso.fun (fst Q₄-columns) v))
      ≡ fst (diagonal₂ 2 2) v
  Q₄-diagonal (x , y) = ΣPathP ((solve! ℤCommRing) , (solve! ℤCommRing))

  Q₃-diagonal : (v : fst ℤ²)
    → Iso.fun (fst Q₃-rows) (fst (B (pos 2) (pos 3)) (Iso.fun (fst Q₃-columns) v))
      ≡ fst (diagonal₂ 1 4) v
  Q₃-diagonal (x , y) = ΣPathP ((solve! ℤCommRing) , (solve! ℤCommRing))

  G₄-cokernel : GroupEquiv (Coker (Araw (pos 2) (pos 3) (pos 4))) (ℤGroup/ 2)
  G₄-cokernel = GroupIso→GroupEquiv (compGroupIso (Araw-cokernel-reduction (pos 3) (pos 4))
    (compGroupIso (coker-unimodular (B (pos 3) (pos 4)) (diagonal₂ 2 1) identity₂ O-columns O-diagonal)
      (compGroupIso (diagonal-cokernel 2 1) (forget-right (ℤGroup/ 2) (ℤGroup/ 1) isContrFin1))))

  G₅-cokernel : GroupEquiv (Coker (Araw (pos 2) (pos 3) (pos 5))) (ℤGroup/ 1)
  G₅-cokernel = GroupIso→GroupEquiv (compGroupIso (Araw-cokernel-reduction (pos 3) (pos 5))
    (compGroupIso (coker-unimodular (B (pos 3) (pos 5)) (diagonal₂ 1 1) identity₂ I-columns I-diagonal)
      (compGroupIso (diagonal-cokernel 1 1) (forget-right (ℤGroup/ 1) (ℤGroup/ 1) isContrFin1))))

  Q₄-cokernel : GroupEquiv (Coker (Araw (pos 2) (pos 2) (pos 4)))
    (DirProd (ℤGroup/ 2) (ℤGroup/ 2))
  Q₄-cokernel = GroupIso→GroupEquiv (compGroupIso (Araw-cokernel-reduction (pos 2) (pos 4))
    (compGroupIso (coker-unimodular (B (pos 2) (pos 4)) (diagonal₂ 2 2) Q-rows Q₄-columns Q₄-diagonal)
      (diagonal-cokernel 2 2)))

  Q₃-cokernel : GroupEquiv (Coker (Araw (pos 2) (pos 2) (pos 3))) (ℤGroup/ 4)
  Q₃-cokernel = GroupIso→GroupEquiv (compGroupIso (Araw-cokernel-reduction (pos 2) (pos 3))
    (compGroupIso (coker-unimodular (B (pos 2) (pos 3)) (diagonal₂ 1 4) Q₃-rows Q₃-columns Q₃-diagonal)
      (compGroupIso (diagonal-cokernel 1 4) (forget-left (ℤGroup/ 1) (ℤGroup/ 4) isContrFin1))))

import DeloopS3.Bridge.Profile.H1Data.RawPolynomial as RP
private module RowPolynomial = RP.Polynomial ℤCommRing

-- The intermediate Q_e matrix, in (r,j) coordinates.
Q : ℤ → AbGroupHom ℤ² ℤ²
Q e = matrix (pos 2) (Z.- e) (pos 0) (pos 2)

abstract
  identity₂-value : (v : fst ℤ²) → Iso.fun (fst identity₂) v ≡ v
  identity₂-value (x , y) = ΣPathP ((solve! ℤCommRing) , (solve! ℤCommRing))

  source-reduced-matrix : (e : ℤ) (v : fst ℤ²)
    → Iso.fun (fst Q-rows) (fst (B (pos 2) e) v) ≡ fst (Q e) v
  source-reduced-matrix e (s , t) = RowPolynomial.source-row-reduction e s t

  Q-reduced-cokernel : (e : ℤ) → GroupEquiv (Coker (Araw (pos 2) (pos 2) e)) (Coker (Q e))
  Q-reduced-cokernel e = GroupIso→GroupEquiv (compGroupIso (Araw-cokernel-reduction (pos 2) e)
    (coker-unimodular (B (pos 2) e) (Q e) Q-rows identity₂
      (λ v → cong (λ x → Iso.fun (fst Q-rows) (fst (B (pos 2) e) x)) (identity₂-value v)
        ∙ source-reduced-matrix e v)))
