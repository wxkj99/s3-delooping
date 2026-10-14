{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.Coordinates where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Nat.Order using (_<_)
open import Cubical.Data.Int using (ℤ ; pos)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Sum using (_⊎_)
open import Cubical.Data.Sigma
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import DeloopS3.Bridge.FiniteDim
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.DMCExactness.Groups using (contr→zero)
open import DeloopS3.Bridge.DMCExactness.Transport using (productEquiv)
open import DeloopS3.Bridge.ComponentHomology.Circle using (circleCW ; circle-H₁)
open import DeloopS3.Bridge.ComponentHomology.Finite using (torusCW ; graph×circleCW)
open import DeloopS3.Bridge.ComponentHomology.ProductBoundary2.Homology
  using (torus-H₁ ; torus-H₂ ; graph×circle-H₁ ; graph×circle-H₂
    ; torus-square-coordinate ; torus-a×h ; torus-a×h-coordinate ; graph-square-pair)
open import DeloopS3.Bridge.SeifertChains.Matrices using (ℤ² ; ℤ³ ; ℤ⁶ ; vertex₁)
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry
open import DeloopS3.Bridge.Profile.BaseSeifert.Coproduct using (module Coproduct)
import DeloopS3.Bridge.SpanCells as Cells
open import DeloopS3.Move.CancelMinimal using (C ; T²)

tori₂ circles₂ : CW₀
tori₂ = (T² ⊎ T²) , finite≤→isCW (Cells.sum2-finite Cells.torus-finite Cells.torus-finite)
circles₂ = (C ⊎ C) , finite≤→isCW (Cells.sum1-finite Cells.circle-finite Cells.circle-finite)

module TwoTori = Coproduct torusCW torusCW tori₂ (idEquiv _) 2 2 Cells.torus-finite Cells.torus-finite
module ThreeTori = Coproduct tori₂ torusCW overlapCW (idEquiv _) 2 2
  (Cells.sum2-finite Cells.torus-finite Cells.torus-finite) Cells.torus-finite
module TwoCircles = Coproduct circleCW circleCW circles₂ (idEquiv _) 1 1 Cells.circle-finite Cells.circle-finite
module ThreeCircles = Coproduct circles₂ circleCW fillingsCW (idEquiv _) 1 1
  (Cells.sum1-finite Cells.circle-finite Cells.circle-finite) Cells.circle-finite

overlap-merge : (n : ℕ) (b : n < 4)
  → fst (H̃ᶜʷ torusCW (suc n)) → fst (H̃ᶜʷ torusCW (suc n)) → fst (H̃ᶜʷ torusCW (suc n))
  → fst (H̃ᶜʷ overlapCW (suc n))
overlap-merge n b x y z = equivFun (fst (ThreeTori.sum-equiv n b))
  (equivFun (fst (TwoTori.sum-equiv n b)) (x , y) , z)

abstract
  overlap-splitting : (n : ℕ) → n < 4
    → GroupEquiv (H̃ᶜʷ overlapCW (suc n))
      (DirProd (DirProd (H̃ᶜʷ torusCW (suc n)) (H̃ᶜʷ torusCW (suc n))) (H̃ᶜʷ torusCW (suc n)))
  overlap-splitting n b = compGroupEquiv (invGroupEquiv (ThreeTori.sum-equiv n b))
    (productEquiv (invGroupEquiv (TwoTori.sum-equiv n b)) idGroupEquiv)

  overlap-merge-split : (n : ℕ) (b : n < 4)
    (x y z : fst (H̃ᶜʷ torusCW (suc n)))
    → equivFun (fst (overlap-splitting n b)) (overlap-merge n b x y z) ≡ ((x , y) , z)
  overlap-merge-split n b x y z =
    cong (equivFun (fst (productEquiv (invGroupEquiv (TwoTori.sum-equiv n b))
      (idGroupEquiv {G = H̃ᶜʷ torusCW (suc n)}))))
      (retEq (fst (ThreeTori.sum-equiv n b))
        (equivFun (fst (TwoTori.sum-equiv n b)) (x , y) , z))
    ∙ ΣPathP (retEq (fst (TwoTori.sum-equiv n b)) (x , y) , refl)

  overlap-split-merge : (n : ℕ) (b : n < 4) (a : fst (H̃ᶜʷ overlapCW (suc n)))
    → overlap-merge n b
        (fst (fst (equivFun (fst (overlap-splitting n b)) a)))
        (snd (fst (equivFun (fst (overlap-splitting n b)) a)))
        (snd (equivFun (fst (overlap-splitting n b)) a)) ≡ a
  overlap-split-merge n b a = cong (equivFun (fst (ThreeTori.sum-equiv n b)))
    (ΣPathP (secEq (fst (TwoTori.sum-equiv n b))
      (fst (invEq (fst (ThreeTori.sum-equiv n b)) a)) , refl))
    ∙ secEq (fst (ThreeTori.sum-equiv n b)) a

  fillings-splitting : (n : ℕ) → n < 4
    → GroupEquiv (H̃ᶜʷ fillingsCW (suc n))
      (DirProd (DirProd (H̃ᶜʷ circleCW (suc n)) (H̃ᶜʷ circleCW (suc n))) (H̃ᶜʷ circleCW (suc n)))
  fillings-splitting n b = compGroupEquiv (invGroupEquiv (ThreeCircles.sum-equiv n b))
    (productEquiv (invGroupEquiv (TwoCircles.sum-equiv n b)) idGroupEquiv)

private
  pair-coordinates : GroupIso (AbGroup→Group ℤ[Fin 2 ]) (AbGroup→Group ℤ²)
  Iso.fun (fst pair-coordinates) f = f fzero , f (fsuc fzero)
  Iso.inv (fst pair-coordinates) (x , y) (0 , _) = x
  Iso.inv (fst pair-coordinates) (x , y) (1 , _) = y
  Iso.sec (fst pair-coordinates) (x , y) = refl
  Iso.ret (fst pair-coordinates) f = funExt λ { (0 , _) → refl ; (1 , _) → refl }
  snd pair-coordinates = makeIsGroupHom λ _ _ → refl

  -- ProductCells orders its one-cells (h,u), whereas Araw orders (u,h).
  torus-edge-order : GroupIso (AbGroup→Group ℤ[Fin 2 ]) (AbGroup→Group ℤ²)
  Iso.fun (fst torus-edge-order) f = f (fsuc fzero) , f fzero
  Iso.inv (fst torus-edge-order) (u , h) (0 , _) = h
  Iso.inv (fst torus-edge-order) (u , h) (1 , _) = u
  Iso.sec (fst torus-edge-order) (u , h) = refl
  Iso.ret (fst torus-edge-order) f = funExt λ { (0 , _) → refl ; (1 , _) → refl }
  snd torus-edge-order = makeIsGroupHom λ _ _ → refl

  triple-order : GroupIso (DirProd (DirProd ℤGroup ℤGroup) ℤGroup) (AbGroup→Group ℤ³)
  Iso.fun (fst triple-order) ((x , y) , z) = x , y , z
  Iso.inv (fst triple-order) (x , y , z) = (x , y) , z
  Iso.sec (fst triple-order) _ = refl
  Iso.ret (fst triple-order) _ = refl
  snd triple-order = makeIsGroupHom λ _ _ → refl

  six-order : GroupIso
    (DirProd (DirProd (AbGroup→Group ℤ²) (AbGroup→Group ℤ²)) (AbGroup→Group ℤ²))
    (AbGroup→Group ℤ⁶)
  Iso.fun (fst six-order) (((u₁ , h₁) , (u₂ , h₂)) , (u₃ , h₃)) = (u₁ , u₂ , u₃) , (h₁ , h₂ , h₃)
  Iso.inv (fst six-order) ((u₁ , u₂ , u₃) , (h₁ , h₂ , h₃)) = ((u₁ , h₁) , (u₂ , h₂)) , (u₃ , h₃)
  Iso.sec (fst six-order) _ = refl
  Iso.ret (fst six-order) _ = refl
  snd six-order = makeIsGroupHom λ _ _ → refl

  vertex-order : GroupIso (DirProd (AbGroup→Group ℤ[Fin 3 ]) (AbGroup→Group ℤ³))
    (AbGroup→Group vertex₁)
  Iso.fun (fst vertex-order) (f , c₁ , c₂ , c₃) =
    (f (fsuc fzero) , f (fsuc (fsuc fzero))) , f fzero , c₁ , c₂ , c₃
  Iso.inv (fst vertex-order) ((a , b) , h , cs) =
    (λ { (0 , _) → h ; (1 , _) → a ; (2 , _) → b }) , cs
  Iso.sec (fst vertex-order) _ = refl
  Iso.ret (fst vertex-order) (f , cs) = ΣPathP
    (funExt (λ { (0 , _) → refl ; (1 , _) → refl ; (2 , _) → refl }) , refl)
  snd vertex-order = makeIsGroupHom λ _ _ → refl

  project-zero : (G H : Group₀) → isContr (fst H) → GroupIso (DirProd G H) G
  Iso.fun (fst (project-zero G H c)) = fst
  Iso.inv (fst (project-zero G H c)) g = g , GroupStr.1g (snd H)
  Iso.sec (fst (project-zero G H c)) _ = refl
  Iso.ret (fst (project-zero G H c)) (g , h) = ΣPathP (refl , sym (contr→zero H c h))
  snd (project-zero G H c) = makeIsGroupHom λ _ _ → refl

abstract
  overlap-H₂ : GroupEquiv (H̃ᶜʷ overlapCW 2) (AbGroup→Group ℤ³)
  overlap-H₂ = compGroupEquiv (overlap-splitting 1 (2 , refl))
    (compGroupEquiv (productEquiv (productEquiv torus-H₂ torus-H₂) torus-H₂)
      (GroupIso→GroupEquiv triple-order))

  overlap-H₁ : GroupEquiv (H̃ᶜʷ overlapCW 1) (AbGroup→Group ℤ⁶)
  overlap-H₁ = compGroupEquiv (overlap-splitting 0 (3 , refl))
    (compGroupEquiv (productEquiv (productEquiv t t) t) (GroupIso→GroupEquiv six-order))
    where
    t : GroupEquiv (H̃ᶜʷ torusCW 1) (AbGroup→Group ℤ²)
    t = compGroupEquiv torus-H₁ (GroupIso→GroupEquiv torus-edge-order)

  fillings-H₁ : GroupEquiv (H̃ᶜʷ fillingsCW 1) (AbGroup→Group ℤ³)
  fillings-H₁ = compGroupEquiv (fillings-splitting 0 (3 , refl))
    (compGroupEquiv (productEquiv (productEquiv circle-H₁ circle-H₁) circle-H₁)
      (GroupIso→GroupEquiv triple-order))

  vertices-H₂ : GroupEquiv (DirProd (H̃ᶜʷ graph×circleCW 2) (H̃ᶜʷ fillingsCW 2))
    (AbGroup→Group ℤ²)
  vertices-H₂ = compGroupEquiv
    (GroupIso→GroupEquiv (project-zero (H̃ᶜʷ graph×circleCW 2) (H̃ᶜʷ fillingsCW 2) fillings-H₂-zero))
    (compGroupEquiv graph×circle-H₂ (GroupIso→GroupEquiv pair-coordinates))

  vertices-H₁ : GroupEquiv (DirProd (H̃ᶜʷ graph×circleCW 1) (H̃ᶜʷ fillingsCW 1))
    (AbGroup→Group vertex₁)
  vertices-H₁ = compGroupEquiv (productEquiv graph×circle-H₁ fillings-H₁)
    (GroupIso→GroupEquiv vertex-order)

  overlap-H₂-on-components : (x y z : fst (H̃ᶜʷ torusCW 2))
    → equivFun (fst overlap-H₂) (overlap-merge 1 (2 , refl) x y z)
      ≡ (torus-square-coordinate x , torus-square-coordinate y , torus-square-coordinate z)
  overlap-H₂-on-components x y z = cong
    (equivFun (fst (compGroupEquiv (productEquiv (productEquiv torus-H₂ torus-H₂) torus-H₂)
      (GroupIso→GroupEquiv triple-order))))
    (overlap-merge-split 1 (2 , refl) x y z)

  vertices-H₂-eval : (b : fst (H̃ᶜʷ graph×circleCW 2)) (c : fst (H̃ᶜʷ fillingsCW 2))
    → equivFun (fst vertices-H₂) (b , c) ≡ graph-square-pair b
  vertices-H₂-eval b c = refl

  overlap-H₁-on-components : (x y z : fst (H̃ᶜʷ torusCW 1))
    → equivFun (fst overlap-H₁) (overlap-merge 0 (3 , refl) x y z)
      ≡ ((equivFun (fst torus-H₁) x (fsuc fzero) ,
          equivFun (fst torus-H₁) y (fsuc fzero) ,
          equivFun (fst torus-H₁) z (fsuc fzero)) ,
         (equivFun (fst torus-H₁) x fzero ,
          equivFun (fst torus-H₁) y fzero ,
          equivFun (fst torus-H₁) z fzero))
  overlap-H₁-on-components x y z = cong
    (equivFun (fst (compGroupEquiv
      (productEquiv (productEquiv t t) t) (GroupIso→GroupEquiv six-order))))
    (overlap-merge-split 0 (3 , refl) x y z)
    where
    t : GroupEquiv (H̃ᶜʷ torusCW 1) (AbGroup→Group ℤ²)
    t = compGroupEquiv torus-H₁ (GroupIso→GroupEquiv torus-edge-order)

  fillings-H₁-on-components : (x y z : fst (H̃ᶜʷ circleCW 1))
    → equivFun (fst fillings-H₁)
        (equivFun (fst (ThreeCircles.sum-equiv 0 (3 , refl)))
          (equivFun (fst (TwoCircles.sum-equiv 0 (3 , refl))) (x , y) , z))
      ≡ (equivFun (fst circle-H₁) x ,
         equivFun (fst circle-H₁) y , equivFun (fst circle-H₁) z)
  fillings-H₁-on-components x y z = cong
    (equivFun (fst (compGroupEquiv
      (productEquiv (productEquiv circle-H₁ circle-H₁) circle-H₁)
      (GroupIso→GroupEquiv triple-order))))
    (cong (equivFun (fst (productEquiv
        (invGroupEquiv (TwoCircles.sum-equiv 0 (3 , refl)))
        (idGroupEquiv {G = H̃ᶜʷ circleCW 1}))))
      (retEq (fst (ThreeCircles.sum-equiv 0 (3 , refl)))
        (equivFun (fst (TwoCircles.sum-equiv 0 (3 , refl))) (x , y) , z))
      ∙ ΣPathP (retEq (fst (TwoCircles.sum-equiv 0 (3 , refl))) (x , y) , refl))

  vertices-H₁-eval : (b : fst (H̃ᶜʷ graph×circleCW 1))
    (c : fst (H̃ᶜʷ fillingsCW 1))
    → equivFun (fst vertices-H₁) (b , c)
      ≡ ((equivFun (fst graph×circle-H₁) b (fsuc fzero) ,
          equivFun (fst graph×circle-H₁) b (fsuc (fsuc fzero))) ,
         equivFun (fst graph×circle-H₁) b fzero , equivFun (fst fillings-H₁) c)
  vertices-H₁-eval b c = refl

abstract
  core-square-hom : GroupHom (H̃ᶜʷ graph×circleCW 2) (AbGroup→Group ℤ²)
  core-square-hom = GroupEquiv→GroupHom
    (compGroupEquiv graph×circle-H₂ (GroupIso→GroupEquiv pair-coordinates))

  core-square-hom-eval : (b : fst (H̃ᶜʷ graph×circleCW 2))
    → fst core-square-hom b ≡ graph-square-pair b
  core-square-hom-eval b = refl

-- A literal sum of the three actual torus cellular fundamental classes.
overlap-ones : fst (H̃ᶜʷ overlapCW 2)
overlap-ones = overlap-merge 1 (2 , refl) torus-a×h torus-a×h torus-a×h

abstract
  overlap-ones-coordinate : equivFun (fst overlap-H₂) overlap-ones ≡ (pos 1 , pos 1 , pos 1)
  overlap-ones-coordinate = overlap-H₂-on-components torus-a×h torus-a×h torus-a×h
    ∙ ΣPathP (torus-a×h-coordinate , ΣPathP (torus-a×h-coordinate , torus-a×h-coordinate))
