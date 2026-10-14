{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.Vertices where

-- Actual vertex maps into CWPushout, conjugated by its specified
-- realization equivalence, with their cellular coefficients and beta laws.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Fin.Base using (Fin)
open import Cubical.Data.Sigma
open import Cubical.Data.Empty as Empty using ()
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.HITs.Pushout as PO using (inl ; inr)
open import Cubical.HITs.SequentialColimit as SC
open import Cubical.Algebra.Group.Morphisms
open import Cubical.CW.Base
open import Cubical.CW.Map
open import Cubical.CW.ChainComplex
open import Cubical.CW.Approximation
open import Cubical.CW.Homology.Base
open import Cubical.CW.Strictification using (strictCWskel)
open import Cubical.CW.Instances.Pushout using (module CWPushout)
open import DeloopS3.Bridge.CellularPushout.Cellular

module Vertices (A B C : CWskel ℓ-zero)
  (f : cellMap (strictCWskel A) (strictCWskel B))
  (g : cellMap (strictCWskel A) (strictCWskel C)) where
  private
    module P = CWPushout ℓ-zero A B C f g

  vertexB-cell : cellMap P.C P.pushoutSkel
  SequenceMap.map vertexB-cell zero x = Empty.rec (snd P.C .snd .snd .fst x)
  SequenceMap.map vertexB-cell (suc n) x = inl x
  SequenceMap.comm vertexB-cell zero x = Empty.rec (snd P.C .snd .snd .fst x)
  SequenceMap.comm vertexB-cell (suc n) x = refl

  vertexC-cell : cellMap P.D P.pushoutSkel
  SequenceMap.map vertexC-cell zero x = Empty.rec (snd P.D .snd .snd .fst x)
  SequenceMap.map vertexC-cell (suc n) x = inr x
  SequenceMap.comm vertexC-cell zero x = Empty.rec (snd P.D .snd .snd .fst x)
  SequenceMap.comm vertexC-cell (suc n) x = refl

  vertexB : realise P.C → realise P.pushoutSkel
  vertexB = Iso.inv P.realisePushoutSkel ∘ inl

  vertexC : realise P.D → realise P.pushoutSkel
  vertexC = Iso.inv P.realisePushoutSkel ∘ inr

  abstract
    vertexB-stage : (n : ℕ) (x : fst P.C (suc n))
      → Iso.fun P.realisePushoutSkel (SC.incl {n = suc n} (inl x))
       ≡ inl (SC.incl {n = suc n} x)
    vertexB-stage n x = refl

    vertexC-stage : (n : ℕ) (x : fst P.D (suc n))
      → Iso.fun P.realisePushoutSkel (SC.incl {n = suc n} (inr x))
       ≡ inr (SC.incl {n = suc n} x)
    vertexC-stage n x = refl

    vertexB-over : Iso.fun P.realisePushoutSkel ∘ vertexB ≡ inl
    vertexB-over = funExt λ x → Iso.sec P.realisePushoutSkel (inl x)

    vertexC-over : Iso.fun P.realisePushoutSkel ∘ vertexC ≡ inr
    vertexC-over = funExt λ x → Iso.sec P.realisePushoutSkel (inr x)

  vertexB-approx : (m : ℕ) → finCellApprox P.C P.pushoutSkel vertexB (suc m)
  fst (vertexB-approx m) = restrictCell vertexB-cell (suc m)
  snd (vertexB-approx m) = →FinSeqColimHomotopy _ _ λ x
    → sym (Iso.ret P.realisePushoutSkel (SC.incl {n = suc m} (inl x)))
      ∙ cong (Iso.inv P.realisePushoutSkel) (vertexB-stage m x)

  vertexC-approx : (m : ℕ) → finCellApprox P.D P.pushoutSkel vertexC (suc m)
  fst (vertexC-approx m) = restrictCell vertexC-cell (suc m)
  snd (vertexC-approx m) = →FinSeqColimHomotopy _ _ λ x
    → sym (Iso.ret P.realisePushoutSkel (SC.incl {n = suc m} (inr x)))
      ∙ cong (Iso.inv P.realisePushoutSkel) (vertexC-stage m x)

  abstract
    vertexB-homology-β : (n : Fin 6)
      → H̃ˢᵏᵉˡ→ {C = P.C} {D = P.pushoutSkel} (fst n) vertexB
       ≡ finCellMap→HomologyMap (fst n)
          (restrictCell vertexB-cell (suc (suc (suc (fst n)))))
    vertexB-homology-β n = H̃ˢᵏᵉˡ→β P.C P.pushoutSkel (fst n)
      (vertexB-approx (suc (suc (fst n))))

    vertexC-homology-β : (n : Fin 6)
      → H̃ˢᵏᵉˡ→ {C = P.D} {D = P.pushoutSkel} (fst n) vertexC
       ≡ finCellMap→HomologyMap (fst n)
          (restrictCell vertexC-cell (suc (suc (suc (fst n)))))
    vertexC-homology-β n = H̃ˢᵏᵉˡ→β P.D P.pushoutSkel (fst n)
      (vertexC-approx (suc (suc (fst n))))

  -- The library orders positive cells ((B+A)+C).
  open import Cubical.Data.Sum as Sum using ()
  open import Cubical.Data.Fin.Properties using (Iso-Fin⊎Fin-Fin+)
  open import Cubical.CW.Instances.Pushout using (module pushoutCWLemmas)
  open import Cubical.Algebra.AbGroup using (AbGroupHom)
  open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤ[Fin_] ; ℤFinFunct)
  open import DeloopS3.Bridge.CellularPushout.CellGroups using (relabel ; relabel-degree)

  κB : (n : ℕ) → Fin (snd P.C .fst n) → Fin (P.pushoutCells n)
  κB zero b = Iso.fun Iso-Fin⊎Fin-Fin+ (Sum.inl b)
  κB (suc n) b = Iso.inv (pushoutCWLemmas.IsoFinSplit3
    (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n))) (Sum.inl (Sum.inl b))

  κC : (n : ℕ) → Fin (snd P.D .fst n) → Fin (P.pushoutCells n)
  κC zero c = Iso.fun Iso-Fin⊎Fin-Fin+ (Sum.inr c)
  κC (suc n) c = Iso.inv (pushoutCWLemmas.IsoFinSplit3
    (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n))) (Sum.inr c)

  κA : (n : ℕ) → Fin (snd P.B .fst n) → Fin (P.pushoutCells (suc n))
  κA n a = Iso.inv (pushoutCWLemmas.IsoFinSplit3
    (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n))) (Sum.inl (Sum.inr a))

  JB : (n : ℕ) → AbGroupHom ℤ[Fin (snd P.C .fst n) ] ℤ[Fin (P.pushoutCells n) ]
  JB n = ℤFinFunct (κB n)

  JC : (n : ℕ) → AbGroupHom ℤ[Fin (snd P.D .fst n) ] ℤ[Fin (P.pushoutCells n) ]
  JC n = ℤFinFunct (κC n)

  JA : (n : ℕ) → AbGroupHom ℤ[Fin (snd P.B .fst n) ] ℤ[Fin (P.pushoutCells (suc n)) ]
  JA n = ℤFinFunct (κA n)

  open import Cubical.Foundations.Equiv using (secEq)
  open import Cubical.Foundations.GroupoidLaws using (cong-∙∙ ; cong-∙ ; rUnit ; compPathRefl)
  open import Cubical.HITs.Pushout using (push)
  open import Cubical.HITs.Sn using (S₊ ; ptSn ; σSn ; IsoSphereSusp ; EquivSphereSusp)
  open import Cubical.HITs.SphereBouquet using (SphereBouquet ; BouquetIso-gen ; Pushout→Bouquet)
  open import Cubical.HITs.SphereBouquet.Degree using (bouquetDegree)
  open import Cubical.Data.Nat.Order.Inductive using (<ᵗsuc)

  -- Inverse vertex characteristic clauses avoid assumptions about the
  -- section paths of pushoutIso. The sphere-coordinate homotopies and
  -- the unit in the actual cellular cofibre map are retained explicitly.
  open import Cubical.HITs.Pushout using (Pushout)
  open import Cubical.HITs.SphereBouquet using (preBTC)
  open import DeloopS3.Bridge.CellularPushout.CellLabels using
    (cellSphere ; cellSphere-map ; preBTC-cellSphere ; petalwise-degree)

  private
    labelChart : (n : ℕ) → Iso (Fin (P.pushoutCells (suc n)))
      ((Fin (snd P.C .fst (suc n)) Sum.⊎ Fin (snd P.B .fst n)) Sum.⊎ Fin (snd P.D .fst (suc n)))
    labelChart n = pushoutCWLemmas.IsoFinSplit3
      (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n))

    H : (n : ℕ) → Pushout (P.pushoutMapₛ n) fst → P.pushoutA (suc (suc n))
    H n = P.modifiedPushout→Pushout n ∘ P.pushoutIsoₛ-inv n

    qB : (n : ℕ) → cofibCW (suc n) P.C → cofibCW (suc n) P.pushoutSkel
    qB n (inl _) = inl _
    qB n (inr x) = inr (inl x)
    qB n (push x i) = push (inl x) i

    qC : (n : ℕ) → cofibCW (suc n) P.D → cofibCW (suc n) P.pushoutSkel
    qC n (inl _) = inl _
    qC n (inr x) = inr (inr x)
    qC n (push x i) = push (inr x) i

    qB-actual : (n : ℕ)
      → prefunctoriality.fn+1/fn (suc (suc n))
          (restrictCell vertexB-cell (suc (suc n))) (suc n , <ᵗsuc) ≡ qB n
    qB-actual n = funExt
      λ { (inl _) → refl ; (inr _) → refl ; (push x i) j → rUnit (push (inl x)) (~ j) i }

    qC-actual : (n : ℕ)
      → prefunctoriality.fn+1/fn (suc (suc n))
          (restrictCell vertexC-cell (suc (suc n))) (suc n , <ᵗsuc) ≡ qC n
    qC-actual n = funExt
      λ { (inl _) → refl ; (inr _) → refl ; (push x i) j → rUnit (push (inr x)) (~ j) i }

    pointY : (n : ℕ) → P.pushoutA (suc (suc n)) → cofibCW (suc n) P.pushoutSkel
    pointY n = inr

    pointB : (n : ℕ) → fst P.C (suc (suc n)) → cofibCW (suc n) P.pushoutSkel
    pointB n x = inr (inl x)

    pointC : (n : ℕ) → fst P.D (suc (suc n)) → cofibCW (suc n) P.pushoutSkel
    pointC n x = inr (inr x)

    raw-spoke : (n : ℕ) (a : Fin (P.pushoutCells (suc n))) (s : S₊ n)
      → cong (pointY n ∘ Iso.inv (P.pushoutIsoₜ (suc n))) (push (a , s))
       ≡ cong {B = λ _ → cofibCW (suc n) P.pushoutSkel} (pointY n ∘ H n)
           (push (Iso.fun (labelChart n) a , Iso.fun (IsoSphereSusp n) s))
    raw-spoke n a s =
      cong-∙∙ (pointY n ∘ H n) refl
        (push (Iso.fun (labelChart n) a , Iso.fun (IsoSphereSusp n) s)) refl
      ∙ (λ i → doubleCompPath-filler refl
          (cong (pointY n ∘ H n) (push (Iso.fun (labelChart n) a , Iso.fun (IsoSphereSusp n) s))) refl (~ i))

    sourceB-sphere : (n : ℕ) (a : Fin (snd P.C .fst (suc n)))
      → S₊ (suc n) → cofibCW (suc n) P.pushoutSkel
    sourceB-sphere n a = cellSphere n {Q = cofibCW (suc n) P.pushoutSkel} (inl _)
      (λ s → inr (inl (inl (snd P.C .snd .fst (suc n) (a , s)))))
      (inr (inl (inr a)))
      (λ s → push (inl (snd P.C .snd .fst (suc n) (a , s))))
      (λ s → cong (pointB n) (push (a , s)))

    targetB-sphere : (n : ℕ) (a : Fin (snd P.C .fst (suc n)))
      → fst (preBTC (suc n) (P.pushoutCells (suc n)) (P.pushoutMap (suc n))
          (snd P.pushoutSkel .snd .snd .snd (suc n)) (κB (suc n) a))
       ≡ sourceB-sphere n a
    targetB-sphere n a =
      preBTC-cellSphere n (P.pushoutCells (suc n)) (P.pushoutMap (suc n))
        (snd P.pushoutSkel .snd .snd .snd (suc n)) (κB (suc n) a)
      ∙ (λ i → cellSphere n {Q = cofibCW (suc n) P.pushoutSkel} (inl _)
          (λ s → inr (H n (inl (P.pushoutMap (suc n) (κB (suc n) a , s)))))
          (inr (H n (inr (Iso.fun (labelChart n) (κB (suc n) a)))))
          (λ s → push (P.pushoutMap (suc n) (κB (suc n) a , s)))
          (λ s → raw-spoke n (κB (suc n) a) s i))
      ∙ (λ i → cellSphere n {Q = cofibCW (suc n) P.pushoutSkel} (inl _)
          (λ s → inr (H n (inl (P.pushoutMapₛ n
            (Iso.sec (labelChart n) (Sum.inl (Sum.inl a)) i , Iso.fun (IsoSphereSusp n) s)))))
          (inr (H n (inr (Iso.sec (labelChart n) (Sum.inl (Sum.inl a)) i))))
          (λ s → push (P.pushoutMapₛ n
            (Iso.sec (labelChart n) (Sum.inl (Sum.inl a)) i , Iso.fun (IsoSphereSusp n) s)))
          (λ s → cong (pointY n ∘ H n) (push
            (Iso.sec (labelChart n) (Sum.inl (Sum.inl a)) i , Iso.fun (IsoSphereSusp n) s))))
      ∙ (λ i → cellSphere n {Q = cofibCW (suc n) P.pushoutSkel} (inl _)
          (λ s → inr (inl (inl (snd P.C .snd .fst (suc n) (a , Iso.ret (IsoSphereSusp n) s i)))))
          (inr (inl (inr a)))
          (λ s → push (inl (snd P.C .snd .fst (suc n) (a , Iso.ret (IsoSphereSusp n) s i))))
          (λ s → cong (pointB n) (push (a , Iso.ret (IsoSphereSusp n) s i))))

    sourceC-sphere : (n : ℕ) (a : Fin (snd P.D .fst (suc n)))
      → S₊ (suc n) → cofibCW (suc n) P.pushoutSkel
    sourceC-sphere n a = cellSphere n {Q = cofibCW (suc n) P.pushoutSkel} (inl _)
      (λ s → inr (inr (inl (snd P.D .snd .fst (suc n) (a , s)))))
      (inr (inr (inr a)))
      (λ s → push (inr (snd P.D .snd .fst (suc n) (a , s))))
      (λ s → cong (pointC n) (push (a , s)))

    targetC-sphere : (n : ℕ) (a : Fin (snd P.D .fst (suc n)))
      → fst (preBTC (suc n) (P.pushoutCells (suc n)) (P.pushoutMap (suc n))
          (snd P.pushoutSkel .snd .snd .snd (suc n)) (κC (suc n) a))
       ≡ sourceC-sphere n a
    targetC-sphere n a =
      preBTC-cellSphere n (P.pushoutCells (suc n)) (P.pushoutMap (suc n))
        (snd P.pushoutSkel .snd .snd .snd (suc n)) (κC (suc n) a)
      ∙ (λ i → cellSphere n {Q = cofibCW (suc n) P.pushoutSkel} (inl _)
          (λ s → inr (H n (inl (P.pushoutMap (suc n) (κC (suc n) a , s)))))
          (inr (H n (inr (Iso.fun (labelChart n) (κC (suc n) a)))))
          (λ s → push (P.pushoutMap (suc n) (κC (suc n) a , s)))
          (λ s → raw-spoke n (κC (suc n) a) s i))
      ∙ (λ i → cellSphere n {Q = cofibCW (suc n) P.pushoutSkel} (inl _)
          (λ s → inr (H n (inl (P.pushoutMapₛ n
            (Iso.sec (labelChart n) (Sum.inr a) i , Iso.fun (IsoSphereSusp n) s)))))
          (inr (H n (inr (Iso.sec (labelChart n) (Sum.inr a) i))))
          (λ s → push (P.pushoutMapₛ n
            (Iso.sec (labelChart n) (Sum.inr a) i , Iso.fun (IsoSphereSusp n) s)))
          (λ s → cong (pointY n ∘ H n) (push
            (Iso.sec (labelChart n) (Sum.inr a) i , Iso.fun (IsoSphereSusp n) s))))
      ∙ (λ i → cellSphere n {Q = cofibCW (suc n) P.pushoutSkel} (inl _)
          (λ s → inr (inr (inl (snd P.D .snd .fst (suc n) (a , Iso.ret (IsoSphereSusp n) s i)))))
          (inr (inr (inr a)))
          (λ s → push (inr (snd P.D .snd .fst (suc n) (a , Iso.ret (IsoSphereSusp n) s i))))
          (λ s → cong (pointC n) (push (a , Iso.ret (IsoSphereSusp n) s i))))

    sourceB-preBTC : (n : ℕ) (a : Fin (snd P.C .fst (suc n)))
      → qB n ∘ fst (preBTC (suc n) (snd P.C .fst (suc n))
          (snd P.C .snd .fst (suc n)) (snd P.C .snd .snd .snd (suc n)) a)
       ≡ sourceB-sphere n a
    sourceB-preBTC n a = cong (qB n ∘_)
      (preBTC-cellSphere n (snd P.C .fst (suc n))
        (snd P.C .snd .fst (suc n)) (snd P.C .snd .snd .snd (suc n)) a)
      ∙ cellSphere-map n (qB n) (inl _)
          (λ s → inr (inl (snd P.C .snd .fst (suc n) (a , s)))) (inr (inr a))
          (λ s → push (snd P.C .snd .fst (suc n) (a , s)))
          (λ s i → inr (push (a , s) i))

    sourceC-preBTC : (n : ℕ) (a : Fin (snd P.D .fst (suc n)))
      → qC n ∘ fst (preBTC (suc n) (snd P.D .fst (suc n))
          (snd P.D .snd .fst (suc n)) (snd P.D .snd .snd .snd (suc n)) a)
       ≡ sourceC-sphere n a
    sourceC-preBTC n a = cong (qC n ∘_)
      (preBTC-cellSphere n (snd P.D .fst (suc n))
        (snd P.D .snd .fst (suc n)) (snd P.D .snd .snd .snd (suc n)) a)
      ∙ cellSphere-map n (qC n) (inl _)
          (λ s → inr (inl (snd P.D .snd .fst (suc n) (a , s)))) (inr (inr a))
          (λ s → push (snd P.D .snd .fst (suc n) (a , s)))
          (λ s i → inr (push (a , s) i))

    coefficientBQ : (T : CWskel ℓ-zero) (n : ℕ)
      → Iso (cofibCW n T) (SphereBouquet n (Fin (snd T .fst n)))
    coefficientBQ T n = BouquetIso-gen n (snd T .fst n)
      (snd T .snd .fst n) (snd T .snd .snd .snd n)

  abstract
    vertexB-petal : (n : ℕ) (a : Fin (snd P.C .fst (suc n)))
      → (λ (s : S₊ (suc n)) → prefunctoriality.bouquetFunct (suc (suc n))
          (restrictCell vertexB-cell (suc (suc n))) (suc n , <ᵗsuc) (inr (a , s)))
       ≡ (λ s → inr (κB (suc n) a , s))
    vertexB-petal n a =
      cong (λ q → Iso.fun (coefficientBQ P.pushoutSkel (suc n)) ∘ q
        ∘ fst (preBTC (suc n) (snd P.C .fst (suc n))
          (snd P.C .snd .fst (suc n)) (snd P.C .snd .snd .snd (suc n)) a)) (qB-actual n)
      ∙ cong (Iso.fun (coefficientBQ P.pushoutSkel (suc n)) ∘_)
          (sourceB-preBTC n a ∙ sym (targetB-sphere n a))
      ∙ funExt (λ s → Iso.sec (coefficientBQ P.pushoutSkel (suc n)) (inr (κB (suc n) a , s)))

    vertexC-petal : (n : ℕ) (a : Fin (snd P.D .fst (suc n)))
      → (λ (s : S₊ (suc n)) → prefunctoriality.bouquetFunct (suc (suc n))
          (restrictCell vertexC-cell (suc (suc n))) (suc n , <ᵗsuc) (inr (a , s)))
       ≡ (λ s → inr (κC (suc n) a , s))
    vertexC-petal n a =
      cong (λ q → Iso.fun (coefficientBQ P.pushoutSkel (suc n)) ∘ q
        ∘ fst (preBTC (suc n) (snd P.D .fst (suc n))
          (snd P.D .snd .fst (suc n)) (snd P.D .snd .snd .snd (suc n)) a)) (qC-actual n)
      ∙ cong (Iso.fun (coefficientBQ P.pushoutSkel (suc n)) ∘_)
          (sourceC-preBTC n a ∙ sym (targetC-sphere n a))
      ∙ funExt (λ s → Iso.sec (coefficientBQ P.pushoutSkel (suc n)) (inr (κC (suc n) a , s)))

  open import Cubical.Foundations.Equiv using (secEq)
  open import Cubical.Data.Unit using (tt)
  open import Cubical.CW.Properties using (CW₁-discrete)
  open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using (ℤFinFunct)

  abstract
    vertexB-coefficients : (n : ℕ) → cellular-coefficients vertexB-cell n ≡ JB n
    vertexB-coefficients zero =
      sym (cellular-coefficients-window vertexB-cell 2 0 tt)
      ∙ sym (chainFunct₀ 0 (restrictCell vertexB-cell 3))
      ∙ cong ℤFinFunct (funExt λ a → cong (κB zero) (secEq (CW₁-discrete P.C) a))
    vertexB-coefficients (suc n) = petalwise-degree (κB (suc n))
      (prefunctoriality.bouquetFunct (suc (suc n))
        (restrictCell vertexB-cell (suc (suc n))) (suc n , <ᵗsuc)) (vertexB-petal n)

    vertexC-coefficients : (n : ℕ) → cellular-coefficients vertexC-cell n ≡ JC n
    vertexC-coefficients zero =
      sym (cellular-coefficients-window vertexC-cell 2 0 tt)
      ∙ sym (chainFunct₀ 0 (restrictCell vertexC-cell 3))
      ∙ cong ℤFinFunct (funExt λ a → cong (κC zero) (secEq (CW₁-discrete P.D) a))
    vertexC-coefficients (suc n) = petalwise-degree (κC (suc n))
      (prefunctoriality.bouquetFunct (suc (suc n))
        (restrictCell vertexC-cell (suc (suc n))) (suc n , <ᵗsuc)) (vertexC-petal n)

  -- Actual vertex coefficients in the unsigned coordinates.
  -- Together with Cellular.cellular-boundary these supply the vertex
  -- columns; no differential equation or prism computation is added here.
  open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom)
  open import DeloopS3.Bridge.CellularPushout.CellGroups using
    (module Split₂ ; module Split₃ ; module Split₂Inclusions ; module Split₃Inclusions)

  private
    module U₀ = Split₂Inclusions (snd P.C .fst 0) (snd P.D .fst 0)
    module U₊ (n : ℕ) = Split₃Inclusions
      (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n))

  abstract
    vertexB-coordinates₀ :
      compGroupHom (cellular-coefficients vertexB-cell 0)
        (Split₂.splitHom (snd P.C .fst 0) (snd P.D .fst 0)) ≡ U₀.jB
    vertexB-coordinates₀ = cong
      (λ h → compGroupHom h (Split₂.splitHom (snd P.C .fst 0) (snd P.D .fst 0)))
      (vertexB-coefficients 0) ∙ U₀.split-left

    vertexC-coordinates₀ :
      compGroupHom (cellular-coefficients vertexC-cell 0)
        (Split₂.splitHom (snd P.C .fst 0) (snd P.D .fst 0)) ≡ U₀.jC
    vertexC-coordinates₀ = cong
      (λ h → compGroupHom h (Split₂.splitHom (snd P.C .fst 0) (snd P.D .fst 0)))
      (vertexC-coefficients 0) ∙ U₀.split-right

    vertexB-coordinates₊ : (n : ℕ)
      → compGroupHom (cellular-coefficients vertexB-cell (suc n))
          (Split₃.splitHom (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n)))
       ≡ U₊.jB n
    vertexB-coordinates₊ n = cong
      (λ h → compGroupHom h
        (Split₃.splitHom (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n))))
      (vertexB-coefficients (suc n)) ∙ U₊.split-B n

    vertexC-coordinates₊ : (n : ℕ)
      → compGroupHom (cellular-coefficients vertexC-cell (suc n))
          (Split₃.splitHom (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n)))
       ≡ U₊.jC n
    vertexC-coordinates₊ n = cong
      (λ h → compGroupHom h
        (Split₃.splitHom (snd P.C .fst (suc n)) (snd P.B .fst n) (snd P.D .fst (suc n))))
      (vertexC-coefficients (suc n)) ∙ U₊.split-C n
