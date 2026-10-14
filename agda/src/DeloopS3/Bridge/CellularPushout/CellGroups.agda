{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.CellGroups where

-- Finite-cell group splittings preserving the single augmentation.
-- Differential compatibility is treated separately in PrismChains.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
open import Cubical.Data.Nat.Order.Inductive
open import Cubical.Data.Fin.Base
open import Cubical.Data.Fin.Properties
open import Cubical.Data.Int as Z using (ℤ ; sumFinℤ ; sumFinℤ0 ; pos)
open import Cubical.Data.Sigma
open import Cubical.Data.Sum as Sum using (_⊎_ ; inl ; inr)
open import Cubical.Data.Sum.Properties using (module ⊎Path)
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.AbGroup
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import DeloopS3.Bridge.CellularPushout.Algebra using (pairHom ; fstHom ; sndHom)

private
  abstract
    delta-self : {n : ℕ} (x : Fin n) → ℤFinGenerator x x ≡ pos 1
    delta-self x with fst x ≟ᵗ fst x
    ... | lt p = Empty.rec (<ᵗ-irrefl p)
    ... | eq p = refl
    ... | gt p = Empty.rec (<ᵗ-irrefl p)

    delta-off : {n : ℕ} (x y : Fin n) → ¬ (x ≡ y) → ℤFinGenerator x y ≡ pos 0
    delta-off x y neq with fst x ≟ᵗ fst y
    ... | lt p = refl
    ... | eq p = Empty.rec (neq (Σ≡Prop (λ _ → isProp<ᵗ) p))
    ... | gt p = refl

    sum-delta : {n : ℕ} (x : Fin n) → sumFinℤ (ℤFinGenerator x) ≡ pos 1
    sum-delta x = sumFin-choose Z._+_ (pos 0) (λ _ → refl) Z.+Comm
      (ℤFinGenerator x) (pos 1) x (delta-self x)
      (λ y neq → delta-off x y (neq ∘ sym))

module Split {N n m : ℕ} (e : Iso (Fin N) (Fin n ⊎ Fin m)) where
  private
    left : Fin n → Fin N
    left x = Iso.inv e (inl x)
    right : Fin m → Fin N
    right x = Iso.inv e (inr x)

  split : fst ℤ[Fin N ] → fst (dirProdAb ℤ[Fin n ] ℤ[Fin m ])
  split x = (x ∘ left) , (x ∘ right)

  join : fst (dirProdAb ℤ[Fin n ] ℤ[Fin m ]) → fst ℤ[Fin N ]
  join (x , y) k = Sum.rec x y (Iso.fun e k)

  abstract
    split-join : (x : fst (dirProdAb ℤ[Fin n ] ℤ[Fin m ])) → split (join x) ≡ x
    split-join (x , y) = ΣPathP
      (funExt (λ a → cong (Sum.rec x y) (Iso.sec e (inl a)))
      , funExt (λ a → cong (Sum.rec x y) (Iso.sec e (inr a))))

    join-split : (x : fst ℤ[Fin N ]) → join (split x) ≡ x
    join-split x = funExt λ k → helper (Iso.fun e k) ∙ cong x (Iso.ret e k)
      where
      helper : (s : Fin n ⊎ Fin m) → Sum.rec (x ∘ left) (x ∘ right) s ≡ x (Iso.inv e s)
      helper (inl _) = refl
      helper (inr _) = refl

  splitIso : Iso (fst ℤ[Fin N ]) (fst (dirProdAb ℤ[Fin n ] ℤ[Fin m ]))
  Iso.fun splitIso = split
  Iso.inv splitIso = join
  Iso.sec splitIso = split-join
  Iso.ret splitIso = join-split

  splitHom : AbGroupHom ℤ[Fin N ] (dirProdAb ℤ[Fin n ] ℤ[Fin m ])
  splitHom = split , makeIsGroupHom (λ _ _ → refl)

  splitEquiv : AbGroupEquiv ℤ[Fin N ] (dirProdAb ℤ[Fin n ] ℤ[Fin m ])
  splitEquiv = isoToEquiv splitIso , snd splitHom

  sum-pair : AbGroupHom (dirProdAb ℤ[Fin n ] ℤ[Fin m ]) ℤ[Fin 1 ]
  sum-pair = addGroupHom (dirProdAb ℤ[Fin n ] ℤ[Fin m ]) ℤ[Fin 1 ]
    (compGroupHom (fstHom ℤ[Fin n ] ℤ[Fin m ]) (sumCoefficients n))
    (compGroupHom (sndHom ℤ[Fin n ] ℤ[Fin m ]) (sumCoefficients m))

  private
    abstract
      left-injective : (x y : Fin n) → left x ≡ left y → x ≡ y
      left-injective x y p = cong (Sum.rec (idfun (Fin n)) (λ _ → x))
        (sym (Iso.sec e (inl x)) ∙ cong (Iso.fun e) p ∙ Iso.sec e (inl y))

      right-injective : (x y : Fin m) → right x ≡ right y → x ≡ y
      right-injective x y p = cong (Sum.rec (λ _ → x) (idfun (Fin m)))
        (sym (Iso.sec e (inr x)) ∙ cong (Iso.fun e) p ∙ Iso.sec e (inr y))

      separate : (x : Fin n) (y : Fin m) → ¬ (left x ≡ right y)
      separate x y p = ⊎Path.inl≢inr x y
        (sym (Iso.sec e (inl x)) ∙ cong (Iso.fun e) p ∙ Iso.sec e (inr y))

      left-sum : (x : Fin n) → sumFinℤ (ℤFinGenerator (left x) ∘ left) ≡ pos 1
      left-sum x = sumFin-choose Z._+_ (pos 0) (λ _ → refl) Z.+Comm
        (ℤFinGenerator (left x) ∘ left) (pos 1) x (delta-self (left x))
        (λ y neq → delta-off (left x) (left y) (λ p → neq (sym (left-injective x y p))))

      right-sum : (x : Fin m) → sumFinℤ (ℤFinGenerator (right x) ∘ right) ≡ pos 1
      right-sum x = sumFin-choose Z._+_ (pos 0) (λ _ → refl) Z.+Comm
        (ℤFinGenerator (right x) ∘ right) (pos 1) x (delta-self (right x))
        (λ y neq → delta-off (right x) (right y) (λ p → neq (sym (right-injective x y p))))

      left-other : (x : Fin n) → sumFinℤ (ℤFinGenerator (left x) ∘ right) ≡ pos 0
      left-other x = cong sumFinℤ (funExt λ y → delta-off (left x) (right y) (separate x y))
        ∙ sumFinℤ0 m

      right-other : (x : Fin m) → sumFinℤ (ℤFinGenerator (right x) ∘ left) ≡ pos 0
      right-other x = cong sumFinℤ (funExt λ y → delta-off (right x) (left y) (separate y x ∘ sym))
        ∙ sumFinℤ0 n

      sum-generator : (k : Fin N)
        → Z._+_ (sumFinℤ (ℤFinGenerator k ∘ left)) (sumFinℤ (ℤFinGenerator k ∘ right))
         ≡ sumFinℤ (ℤFinGenerator k)
      sum-generator k = subst goal (Iso.ret e k) (helper (Iso.fun e k))
        where
        goal : Fin N → Type
        goal t = Z._+_ (sumFinℤ (ℤFinGenerator t ∘ left)) (sumFinℤ (ℤFinGenerator t ∘ right))
          ≡ sumFinℤ (ℤFinGenerator t)
        helper : (s : Fin n ⊎ Fin m) → goal (Iso.inv e s)
        helper (inl x) = cong₂ Z._+_ (left-sum x) (left-other x) ∙ sym (sum-delta (left x))
        helper (inr x) = cong₂ Z._+_ (right-other x) (right-sum x) ∙ sym (sum-delta (right x))

  abstract
    split-augmentation : compGroupHom splitHom sum-pair ≡ sumCoefficients N
    split-augmentation = agreeOnℤFinGenerator→≡ (λ k → funExt λ _ → sum-generator k)

module Split₂ (n m : ℕ) = Split (invIso (Iso-Fin⊎Fin-Fin+ {n} {m}))

-- CWPushout orders the positive cells as ((B + A[-1]) + C).
-- Reorder to (B , C , A[-1]); this version does not reverse prism signs.
module Split₃ (b a c : ℕ) where
  private
    module BA = Split₂ b a
    module BAC = Split₂ (b + a) c

  triple : AbGroup ℓ-zero
  triple = dirProdAb ℤ[Fin b ] (dirProdAb ℤ[Fin c ] ℤ[Fin a ])

  split : fst ℤ[Fin ((b + a) + c) ] → fst triple
  split x = fst (BA.split (fst (BAC.split x)))
          , snd (BAC.split x)
          , snd (BA.split (fst (BAC.split x)))

  join : fst triple → fst ℤ[Fin ((b + a) + c) ]
  join (x , y , z) = BAC.join (BA.join (x , z) , y)

  abstract
    split-join : (x : fst triple) → split (join x) ≡ x
    split-join (x , y , z) =
      cong (λ w → fst (BA.split (fst w)) , snd w , snd (BA.split (fst w)))
        (BAC.split-join (BA.join (x , z) , y))
      ∙ cong (λ w → fst w , y , snd w) (BA.split-join (x , z))

    join-split : (x : fst ℤ[Fin ((b + a) + c) ]) → join (split x) ≡ x
    join-split x = cong (λ w → BAC.join (w , snd (BAC.split x)))
      (BA.join-split (fst (BAC.split x))) ∙ BAC.join-split x

  splitIso : Iso (fst ℤ[Fin ((b + a) + c) ]) (fst triple)
  Iso.fun splitIso = split
  Iso.inv splitIso = join
  Iso.sec splitIso = split-join
  Iso.ret splitIso = join-split

  splitHom : AbGroupHom ℤ[Fin ((b + a) + c) ] triple
  splitHom = split , makeIsGroupHom (λ _ _ → refl)

  splitEquiv : AbGroupEquiv ℤ[Fin ((b + a) + c) ] triple
  splitEquiv = isoToEquiv splitIso , snd splitHom

-- Label calculus for the actual (unsigned) characteristic-cell basis.
-- The group map is covariant on labels, not precomposition on chains.
open import Cubical.HITs.Pushout as PO using (push)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.SphereBouquet.Degree using (bouquetDegree ; bouquetDegreeId ; pickPetal)
open import Cubical.HITs.Sn using (S₊)
open import Cubical.HITs.Sn.Degree using (degree)

relabel : {d n m : ℕ} → (Fin n → Fin m)
  → SphereBouquet d (Fin n) → SphereBouquet d (Fin m)
relabel κ (PO.inl x) = PO.inl x
relabel κ (PO.inr (a , s)) = PO.inr (κ a , s)
relabel κ (push a i) = push (κ a) i

abstract
  label-generator : {n m : ℕ} (κ : Fin n → Fin m) (a : Fin n)
    → fst (ℤFinFunct κ) (ℤFinGenerator a) ≡ ℤFinGenerator (κ a)
  label-generator {n} κ a = funExt λ b → sumFin-choose Z._+_ (pos 0)
    (λ _ → refl) Z.+Comm (λ t → ℤFinFunctGenerator κ (ℤFinGenerator a) t b)
    (ℤFinGenerator (κ a) b) a (ℤFinFunctGenerator≡ κ a b)
    λ t neq → off t b (λ p → neq (sym p))
    where
    off : (t : Fin n) (b : Fin _) → ¬ (a ≡ t)
      → ℤFinFunctGenerator κ (ℤFinGenerator a) t b ≡ pos 0
    off t b neq with fst (κ t) ≟ᵗ fst b
    ... | lt _ = refl
    ... | eq _ = delta-off a t neq
    ... | gt _ = refl

  petal-degree : (d : ℕ) {m : ℕ} (a b : Fin m)
    → degree d (λ s → pickPetal b (PO.inr (a , s))) ≡ ℤFinGenerator a b
  petal-degree d a b =
    isGeneratorℤFinGenerator' (λ t → degree d (λ s → pickPetal b (PO.inr (t , s)))) a
    ∙ cong (λ h → fst h (ℤFinGenerator a) b) (bouquetDegreeId {n = d})

  relabel-generator : {d n m : ℕ} (κ : Fin n → Fin m) (a : Fin n)
    → fst (bouquetDegree (relabel {d = d} κ)) (ℤFinGenerator a)
     ≡ ℤFinGenerator (κ a)
  relabel-generator {d} κ a = funExt λ b →
    sym (isGeneratorℤFinGenerator'
      (λ t → degree d (λ s → pickPetal b (PO.inr (κ t , s)))) a)
    ∙ petal-degree d (κ a) b

  relabel-degree : {d n m : ℕ} (κ : Fin n → Fin m)
    → bouquetDegree (relabel {d = d} κ) ≡ ℤFinFunct κ
  relabel-degree κ = agreeOnℤFinGenerator→≡ λ a →
    relabel-generator κ a ∙ sym (label-generator κ a)

  label-id : (n : ℕ) → ℤFinFunct (idfun (Fin n)) ≡ idGroupHom
  label-id n = agreeOnℤFinGenerator→≡ (label-generator (idfun (Fin n)))

  label-comp : {n m k : ℕ} (κ : Fin n → Fin m) (λ' : Fin m → Fin k)
    → compGroupHom (ℤFinFunct κ) (ℤFinFunct λ') ≡ ℤFinFunct (λ' ∘ κ)
  label-comp κ λ' = agreeOnℤFinGenerator→≡ λ a →
    cong (fst (ℤFinFunct λ')) (label-generator κ a)
    ∙ label-generator λ' (κ a) ∙ sym (label-generator (λ' ∘ κ) a)

-- The finite-label maps are exactly the coordinate inclusions of the
-- unsigned splittings (including the library's ((B+A)+C) order).
open import Cubical.Relation.Nullary using (yes ; no)

private
  abstract
    coordinate-self : {n : ℕ} (x : Fin n) → ℤFinGenerator x x ≡ pos 1
    coordinate-self x with fst x ≟ᵗ fst x
    ... | lt p = Empty.rec (<ᵗ-irrefl p)
    ... | eq _ = refl
    ... | gt p = Empty.rec (<ᵗ-irrefl p)

    coordinate-off : {n : ℕ} (x y : Fin n) → ¬ (x ≡ y) → ℤFinGenerator x y ≡ pos 0
    coordinate-off x y neq with fst x ≟ᵗ fst y
    ... | lt _ = refl
    ... | eq p = Empty.rec (neq (Σ≡Prop (λ _ → isProp<ᵗ) p))
    ... | gt _ = refl

abstract
  generator-injective : {n m : ℕ} (κ : Fin n → Fin m)
    (injective : (x y : Fin n) → κ x ≡ κ y → x ≡ y) (x y : Fin n)
    → ℤFinGenerator (κ x) (κ y) ≡ ℤFinGenerator x y
  generator-injective κ injective x y with discreteFin x y
  ... | yes p = cong (ℤFinGenerator (κ x) ∘ κ) (sym p)
    ∙ coordinate-self (κ x) ∙ sym (coordinate-self x) ∙ cong (ℤFinGenerator x) p
  ... | no neq = coordinate-off (κ x) (κ y) (neq ∘ injective x y)
    ∙ sym (coordinate-off x y neq)

module SplitInclusions {N b c : ℕ} (e : Iso (Fin N) (Fin b ⊎ Fin c)) where
  module S = Split e

  left-label : Fin b → Fin N
  left-label x = Iso.inv e (inl x)

  right-label : Fin c → Fin N
  right-label x = Iso.inv e (inr x)

  leftHom : AbGroupHom ℤ[Fin b ] ℤ[Fin N ]
  leftHom = ℤFinFunct left-label

  rightHom : AbGroupHom ℤ[Fin c ] ℤ[Fin N ]
  rightHom = ℤFinFunct right-label

  jB : AbGroupHom ℤ[Fin b ] (dirProdAb ℤ[Fin b ] ℤ[Fin c ])
  jB = pairHom idGroupHom trivGroupHom

  jC : AbGroupHom ℤ[Fin c ] (dirProdAb ℤ[Fin b ] ℤ[Fin c ])
  jC = pairHom trivGroupHom idGroupHom

  private
    abstract
      left-injective : (x y : Fin b) → left-label x ≡ left-label y → x ≡ y
      left-injective x y p = cong (Sum.rec (idfun (Fin b)) (λ _ → x))
        (sym (Iso.sec e (inl x)) ∙ cong (Iso.fun e) p ∙ Iso.sec e (inl y))

      right-injective : (x y : Fin c) → right-label x ≡ right-label y → x ≡ y
      right-injective x y p = cong (Sum.rec (λ _ → x) (idfun (Fin c)))
        (sym (Iso.sec e (inr x)) ∙ cong (Iso.fun e) p ∙ Iso.sec e (inr y))

      separate : (x : Fin b) (y : Fin c) → ¬ (left-label x ≡ right-label y)
      separate x y p = ⊎Path.inl≢inr x y
        (sym (Iso.sec e (inl x)) ∙ cong (Iso.fun e) p ∙ Iso.sec e (inr y))

  abstract
    split-left : compGroupHom leftHom S.splitHom ≡ jB
    split-left = agreeOnℤFinGenerator→≡ λ x → cong S.split (label-generator left-label x)
      ∙ ΣPathP (funExt (generator-injective left-label left-injective x)
        , funExt (λ y → coordinate-off (left-label x) (right-label y) (separate x y)))

    split-right : compGroupHom rightHom S.splitHom ≡ jC
    split-right = agreeOnℤFinGenerator→≡ λ x → cong S.split (label-generator right-label x)
      ∙ ΣPathP (funExt (λ y → coordinate-off (right-label x) (left-label y) (separate y x ∘ sym))
        , funExt (generator-injective right-label right-injective x))

module Split₂Inclusions (b c : ℕ) = SplitInclusions (invIso (Iso-Fin⊎Fin-Fin+ {b} {c}))

module Split₃Inclusions (b a c : ℕ) where
  private
    module BA = Split₂Inclusions b a
    module BAC = Split₂Inclusions (b + a) c
    module T = Split₃ b a c

  κB : Fin b → Fin ((b + a) + c)
  κB = BAC.left-label ∘ BA.left-label

  κC : Fin c → Fin ((b + a) + c)
  κC = BAC.right-label

  κA : Fin a → Fin ((b + a) + c)
  κA = BAC.left-label ∘ BA.right-label

  jB : AbGroupHom ℤ[Fin b ] T.triple
  jB = pairHom idGroupHom (pairHom trivGroupHom trivGroupHom)

  jC : AbGroupHom ℤ[Fin c ] T.triple
  jC = pairHom trivGroupHom (pairHom idGroupHom trivGroupHom)

  jA : AbGroupHom ℤ[Fin a ] T.triple
  jA = pairHom trivGroupHom (pairHom trivGroupHom idGroupHom)

  private
    shuffle : fst (dirProdAb ℤ[Fin (b + a) ] ℤ[Fin c ]) → fst T.triple
    shuffle y = fst (BA.S.split (fst y)) , snd y , snd (BA.S.split (fst y))

  abstract
    split-B : compGroupHom (ℤFinFunct κB) T.splitHom ≡ jB
    split-B = GroupHom≡ (funExt λ x →
      cong T.split (sym (funExt⁻ (cong fst (label-comp BA.left-label BAC.left-label)) x))
      ∙ cong shuffle (funExt⁻ (cong fst BAC.split-left) (fst BA.leftHom x))
      ∙ cong (λ y → fst y , (λ _ → pos 0) , snd y)
          (funExt⁻ (cong fst BA.split-left) x))

    split-C : compGroupHom (ℤFinFunct κC) T.splitHom ≡ jC
    split-C = GroupHom≡ (funExt λ x → cong shuffle (funExt⁻ (cong fst BAC.split-right) x))

    split-A : compGroupHom (ℤFinFunct κA) T.splitHom ≡ jA
    split-A = GroupHom≡ (funExt λ x →
      cong T.split (sym (funExt⁻ (cong fst (label-comp BA.right-label BAC.left-label)) x))
      ∙ cong shuffle (funExt⁻ (cong fst BAC.split-left) (fst BA.rightHom x))
      ∙ cong (λ y → fst y , (λ _ → pos 0) , snd y)
          (funExt⁻ (cong fst BA.split-right) x))
