{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.Cellular where

-- Assemble a whole cellular chain map from the library's finite-window
-- construction. Restriction just forgets the bounds: no choice or
-- stabilization theorem is used.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.HITs.Pushout using (inl ; inr ; push)
open import Cubical.HITs.SphereBouquet using (BouquetIso-gen)
open import Cubical.HITs.SphereBouquet.Degree using (bouquetDegree)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc ; _<ᵗ_)
open import Cubical.Data.Fin.Base using (Fin ; injectSuc)
open import Cubical.Data.Sigma
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.Data.FinSequence using (FinSequenceMap)
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_])
open import Cubical.Algebra.ChainComplex.Base
open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.ChainComplex
open import DeloopS3.Bridge.CellularPushout.Algebra

open ChainComplex
open ChainComplexMap

CW-ordinary : (X : CWskel ℓ-zero) → ChainComplex ℓ-zero
chain (CW-ordinary X) n = ℤ[Fin (snd X .fst n) ]
bdry (CW-ordinary X) n = ∂ X n
bdry²=0 (CW-ordinary X) n = ∂∂≡0 X n

CW-augmented : (X : CWskel ℓ-zero) → Augmented ℤ[Fin 1 ]
ordinary (CW-augmented X) = CW-ordinary X
ε (CW-augmented X) = augmentation.ϵ X
εd (CW-augmented X) = augmentation.ϵ∂≡0 X

restrictCell : {X Y : CWskel ℓ-zero} (h : cellMap X Y) (m : ℕ)
  → finCellMap m X Y
FinSequenceMap.fmap (restrictCell h m) n = SequenceMap.map h (fst n)
FinSequenceMap.fcomm (restrictCell h m) n = SequenceMap.comm h (fst n)

cellular-coefficients : {X Y : CWskel ℓ-zero} (h : cellMap X Y) (n : ℕ)
  → AbGroupHom (chain (CW-ordinary X) n) (chain (CW-ordinary Y) n)
cellular-coefficients h n = prefunctoriality.chainFunct (suc n)
  (restrictCell h (suc n)) (n , <ᵗsuc)

abstract
  cellular-cofib-window : {X Y : CWskel ℓ-zero} (h : cellMap X Y)
    (m n : ℕ) (p : n <ᵗ suc m)
    → prefunctoriality.fn+1/fn (suc m) (restrictCell h (suc m)) (n , p)
     ≡ prefunctoriality.fn+1/fn (suc n) (restrictCell h (suc n)) (n , <ᵗsuc)
  cellular-cofib-window h m n p = funExt
    λ { (inl _) → refl ; (inr _) → refl ; (push _ _) → refl }

  cellular-coefficients-window : {X Y : CWskel ℓ-zero} (h : cellMap X Y)
    (m n : ℕ) (p : n <ᵗ suc m)
    → prefunctoriality.chainFunct (suc m) (restrictCell h (suc m)) (n , p)
     ≡ cellular-coefficients h n
  cellular-coefficients-window {X = X} {Y = Y} h m n p =
    cong (λ k → bouquetDegree (Iso.fun (BouquetIso-gen n (snd Y .fst n)
      (snd Y .snd .fst n) (snd Y .snd .snd .snd n)) ∘ k
      ∘ Iso.inv (BouquetIso-gen n (snd X .fst n)
        (snd X .snd .fst n) (snd X .snd .snd .snd n))))
      (cellular-cofib-window h m n p)

  cellular-boundary : {X Y : CWskel ℓ-zero} (h : cellMap X Y) (n : ℕ)
    → compGroupHom (cellular-coefficients h (suc n)) (∂ Y n)
     ≡ compGroupHom (∂ X n) (cellular-coefficients h n)
  cellular-boundary {X = X} {Y = Y} h n =
    sym (cong (λ k → compGroupHom k (∂ Y n))
      (cellular-coefficients-window h (suc n) (suc n) (<ᵗsuc {n})))
    ∙ functoriality.comm∂Funct (suc n) (restrictCell h (suc (suc n))) (n , <ᵗsuc)
    ∙ cong (compGroupHom (∂ X n))
        (cellular-coefficients-window h (suc n) n (snd (injectSuc (n , <ᵗsuc))))

  cellular-augmentation : {X Y : CWskel ℓ-zero} (h : cellMap X Y)
    → compGroupHom (cellular-coefficients h 0) (augmentation.ϵ Y) ≡ augmentation.ϵ X
  cellular-augmentation {X = X} h =
    augmentationFunct.commϵFunct 0 (restrictCell h 1)
    ∙ compGroupHomId (augmentation.ϵ X)

cellular-ordinary-map : {X Y : CWskel ℓ-zero} (h : cellMap X Y)
  → ChainComplexMap (CW-ordinary X) (CW-ordinary Y)
chainmap (cellular-ordinary-map h) = cellular-coefficients h
bdrycomm (cellular-ordinary-map h) = cellular-boundary h

cellular-augmented-map : {X Y : CWskel ℓ-zero} (h : cellMap X Y)
  → AugmentedMap (CW-augmented X) (CW-augmented Y)
ordinaryMap (cellular-augmented-map h) = cellular-ordinary-map h
εcomm (cellular-augmented-map h) = cellular-augmentation h

-- Retain the specified cellular homotopy and its coherence when
-- restricting to the library's finite windows.
open import Cubical.HITs.Susp using (Susp ; north ; south ; merid)
open import Cubical.CW.Homotopy using
  (cellHom ; finCellHom ; cofibIso ; module preChainHomotopy
  ; module chainHomEquationZero ; module chainHomEquationSuc)

Z : CWskel ℓ-zero → ℕ → AbGroup ℓ-zero
Z X n = ℤ[Fin (snd X .fst n) ]

restrictCellHom : {X Y : CWskel ℓ-zero} {f g : cellMap X Y}
  → cellHom f g → (m : ℕ)
  → finCellHom m (restrictCell f m) (restrictCell g m)
finCellHom.fhom (restrictCellHom H m) n = cellHom.hom H (fst n)
finCellHom.fcoh (restrictCellHom H m) n = cellHom.coh H (fst n)

homotopy-coefficients : {X Y : CWskel ℓ-zero} {f g : cellMap X Y}
  → cellHom f g → (n : ℕ) → AbGroupHom (Z X n) (Z Y (suc n))
homotopy-coefficients {X} {Y} {f} {g} H n =
  preChainHomotopy.chainHomotopy (suc n) X Y
    (restrictCell f (suc n)) (restrictCell g (suc n))
    (restrictCellHom H (suc n)) (n , <ᵗsuc)

abstract
  homotopy-cofib-window : {X Y : CWskel ℓ-zero} {f g : cellMap X Y}
    (H : cellHom f g) (m n : ℕ) (p : n <ᵗ suc m)
    → preChainHomotopy.Hn+1/Hn (suc m) X Y
        (restrictCell f (suc m)) (restrictCell g (suc m))
        (restrictCellHom H (suc m)) (n , p)
     ≡ preChainHomotopy.Hn+1/Hn (suc n) X Y
        (restrictCell f (suc n)) (restrictCell g (suc n))
        (restrictCellHom H (suc n)) (n , <ᵗsuc)
  homotopy-cofib-window H m n p = funExt λ
    { north → refl
    ; south → refl
    ; (merid (inl _) _) → refl
    ; (merid (inr _) _) → refl
    ; (merid (push _ _) _) → refl }

  homotopy-coefficients-window : {X Y : CWskel ℓ-zero} {f g : cellMap X Y}
    (H : cellHom f g) (m n : ℕ) (p : n <ᵗ suc m)
    → preChainHomotopy.chainHomotopy (suc m) X Y
        (restrictCell f (suc m)) (restrictCell g (suc m))
        (restrictCellHom H (suc m)) (n , p)
     ≡ homotopy-coefficients H n
  homotopy-coefficients-window {X} {Y} H m n p =
    cong (λ k → bouquetDegree
      (Iso.fun (BouquetIso-gen (suc n) (snd Y .fst (suc n))
        (snd Y .snd .fst (suc n)) (snd Y .snd .snd .snd (suc n)))
        ∘ k ∘ Iso.inv (cofibIso n X)))
      (homotopy-cofib-window H m n p)

  cellular-coefficients-comp : {X Y W : CWskel ℓ-zero}
    (g : cellMap Y W) (f : cellMap X Y) (n : ℕ)
    → cellular-coefficients (composeCellMap g f) n
     ≡ compGroupHom (cellular-coefficients f n) (cellular-coefficients g n)
  cellular-coefficients-comp g f n = sym
    (chainFunct-comp (suc n) (restrictCell g (suc n))
      (restrictCell f (suc n)) (n , <ᵗsuc))

  -- The degree-zero side term is literally zero, not a shifted source
  -- augmentation. This is the library's chainHomotopyZero, not a new
  -- meridian calculation.
  homotopy-equation₀ : {X Y : CWskel ℓ-zero} {f g : cellMap X Y}
    (H : cellHom f g)
    → subtrGroupHom (Z X 0) (Z Y 0)
        (cellular-coefficients f 0) (cellular-coefficients g 0)
     ≡ addGroupHom (Z X 0) (Z Y 0)
        (compGroupHom (homotopy-coefficients H 0) (∂ Y 0)) trivGroupHom
  homotopy-equation₀ {X} {Y} {f} {g} H =
    chainHomEquationZero.chainHomotopyZero 0 X Y
      (restrictCell f 1) (restrictCell g 1) (restrictCellHom H 1)
    ∙ cong (addGroupHom (Z X 0) (Z Y 0)
        (compGroupHom (homotopy-coefficients H 0) (∂ Y 0)))
        (GroupHom≡ refl)

  homotopy-equation₊ : {X Y : CWskel ℓ-zero} {f g : cellMap X Y}
    (H : cellHom f g) (n : ℕ)
    → subtrGroupHom (Z X (suc n)) (Z Y (suc n))
        (cellular-coefficients f (suc n)) (cellular-coefficients g (suc n))
     ≡ addGroupHom (Z X (suc n)) (Z Y (suc n))
        (compGroupHom (homotopy-coefficients H (suc n)) (∂ Y (suc n)))
        (compGroupHom (∂ X n) (homotopy-coefficients H n))
  homotopy-equation₊ {X} {Y} {f} {g} H n =
    sym (cong₂ (subtrGroupHom (Z X (suc n)) (Z Y (suc n)))
      (cellular-coefficients-window f (suc n) (suc n) (<ᵗsuc {n}))
      (cellular-coefficients-window g (suc n) (suc n) (<ᵗsuc {n})))
    ∙ chainHomEquationSuc.chainHomotopySuc (suc n) X Y
        (restrictCell f (suc (suc n))) (restrictCell g (suc (suc n)))
        (restrictCellHom H (suc (suc n))) (n , <ᵗsuc)
    ∙ cong₂ (addGroupHom (Z X (suc n)) (Z Y (suc n)))
        (cong (λ k → compGroupHom k (∂ Y (suc n)))
          (homotopy-coefficients-window H (suc n) (suc n) (<ᵗsuc {n})))
        (cong (compGroupHom (∂ X n))
          (homotopy-coefficients-window H (suc n) n
            (snd (injectSuc (n , <ᵗsuc)))))

  homotopy-boundary₀ : {X Y : CWskel ℓ-zero} {f g : cellMap X Y}
    (H : cellHom f g)
    → compGroupHom (homotopy-coefficients H 0) (∂ Y 0)
     ≡ subtrGroupHom (Z X 0) (Z Y 0)
        (cellular-coefficients f 0) (cellular-coefficients g 0)
  homotopy-boundary₀ {Y = Y} H =
    sym (homotopy-equation₀ H
      ∙ GroupHom≡ (funExt λ x → AbGroupStr.+IdR (snd (Z Y 0)) _))

  homotopy-boundary₊ : {X Y : CWskel ℓ-zero} {f g : cellMap X Y}
    (H : cellHom f g) (n : ℕ)
    → compGroupHom (homotopy-coefficients H (suc n)) (∂ Y (suc n))
     ≡ subtrGroupHom (Z X (suc n)) (Z Y (suc n))
        (subtrGroupHom (Z X (suc n)) (Z Y (suc n))
          (cellular-coefficients f (suc n)) (cellular-coefficients g (suc n)))
        (compGroupHom (∂ X n) (homotopy-coefficients H n))
  homotopy-boundary₊ {X} {Y} H n = GroupHom≡ (funExt λ x →
    sym (cong (λ z → z +G (-G side x))
        (cong (λ h → fst h x) (homotopy-equation₊ H n))
      ∙ sym (+Assoc _ _ _)
      ∙ cong (λ z → fst (compGroupHom (homotopy-coefficients H (suc n))
                         (∂ Y (suc n))) x +G z) (+InvR (side x))
      ∙ +IdR _))
    where
    open AbGroupStr (snd (Z Y (suc n))) renaming (_+_ to _+G_ ; -_ to -G_)
    side : fst (Z X (suc n)) → fst (Z Y (suc n))
    side = fst (compGroupHom (∂ X n) (homotopy-coefficients H n))
