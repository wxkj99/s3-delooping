{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.HurewiczChartProof.EdgeCircle where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using
  (cong-∙ ; cong-∙∙ ; assoc ; lCancel ; rUnit)
open import Cubical.Data.Int using (ℤ ; pos ; isSetℤ)
open import Cubical.Data.Sigma using (Σ≡Prop)
open import Cubical.Foundations.HLevels using (isSetΠ)
import Cubical.HITs.SetQuotients as SQ
open import Cubical.CW.Homology.Groups.Sn using (genHₙSⁿ)
open import Cubical.CW.Homology.Groups.CofibFinSphereBouquetMap using
  (genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ)
open import Cubical.Data.Bool using (false ; true)
open import Cubical.HITs.S1 using (S¹ ; base ; loop ; ΩS¹ ; comm-ΩS¹)
open import Cubical.HITs.Sn.Degree using (degree)
open import Cubical.HITs.SphereBouquet.Degree using (pickPetal ; bouquetDegreeId)
open import Cubical.HITs.SphereBouquet.Properties using
  (module BouquetFuns ; preBTC ; Pushout→Bouquet)
open import Cubical.Algebra.AbGroup.Instances.FreeAbGroup using
  (ℤFinGenerator ; isGeneratorℤFinGenerator')
open import Cubical.Foundations.Equiv using (invEq)
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Fin using (Fin ; fzero ; fsuc)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sequence using (SequenceMap)
open import Cubical.Data.FinSequence using (FinSequenceMap)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr ; push)
open import Cubical.HITs.SphereBouquet using (SphereBouquet ; FinSphereBouquetMap)
open import Cubical.HITs.SequentialColimit using (→FinSeqColimHomotopy)
open import Cubical.CW.Base using (CW↪ ; realise ; module CWskel-fields)
open import Cubical.CW.Map using (cellMap ; finCellMap ; realiseCellMap ; module prefunctoriality)
open import Cubical.CW.Approximation using (finCellApprox)
open import Cubical.CW.Instances.Sn using (Sˢᵏᵉˡ)
open import Cubical.CW.Instances.SphereBouquetMap using
  (SphereBouquet/ˢᵏᵉˡ ; SphereBouquet/EqBottomMainGen ; SphereBouquet/EqBottomMainGenLem)
open import Cubical.CW.Homology.Base using (H̃ˢᵏᵉˡ→ ; H̃ˢᵏᵉˡ→-pre ; H̃ˢᵏᵉˡ→β)

-- One generic literal edge inclusion, rather than five product-specific
-- cellular approximations. No homology-coordinate conclusion is assumed.
module Edge {m n : ℕ} (α : FinSphereBouquetMap m n 0) (k : Fin n) where
  private
    S = Sˢᵏᵉˡ 1
    T = SphereBouquet/ˢᵏᵉˡ α

  cellular : cellMap S T
  SequenceMap.map cellular zero ()
  SequenceMap.map cellular (suc zero) tt = tt
  SequenceMap.map cellular (suc (suc zero)) x = inr (k , x)
  SequenceMap.map cellular (suc (suc (suc r))) x = CW↪ T 2 (inr (k , x))
  SequenceMap.comm cellular zero ()
  SequenceMap.comm cellular (suc zero) tt = push k
  SequenceMap.comm cellular (suc (suc zero)) x = refl
  SequenceMap.comm cellular (suc (suc (suc r))) x = refl

  finite : finCellMap 4 S T
  FinSequenceMap.fmap finite (r , _) = SequenceMap.map cellular r
  FinSequenceMap.fcomm finite (r , _) = SequenceMap.comm cellular r

  realization : realise S → realise T
  realization = realiseCellMap cellular

  approximation : finCellApprox S T realization 4
  fst approximation = finite
  snd approximation = →FinSeqColimHomotopy _ _ λ x → refl

  abstract
    homology-beta : H̃ˢᵏᵉˡ→ {C = S} {D = T} 1 realization
      ≡ H̃ˢᵏᵉˡ→-pre S T 1 finite
    homology-beta = H̃ˢᵏᵉˡ→β S T 1 approximation

  private
    module SS = CWskel-fields S
    module TT = CWskel-fields T
    module Q = prefunctoriality 4 finite (fsuc fzero)
    module Target = BouquetFuns 1 n (TT.α 1) (TT.e 1)

    source-petal : S¹ → cofib (CW↪ S 1)
    source-petal = fst (preBTC 1 1 (SS.α 1) (SS.e 1) fzero)

    projected-quotient : Fin n → cofib (CW↪ S 1) → S¹
    projected-quotient q = pickPetal q ∘ Target.CTB ∘ Q.fn+1/fn

    abstract
      target-collapse : (x : SphereBouquet 1 (Fin n)) → Target.CTB (inr x) ≡ x
      target-collapse x =
        cong (Pushout→Bouquet 1 n (TT.α 1) (TT.e 1))
          (transportRefl (fst (SphereBouquet/EqBottomMainGen m n α) x))
        ∙ SphereBouquet/EqBottomMainGenLem 0 α {e = TT.e 1} x

      source-petal-loop : cong source-petal loop
        ≡ push tt ∙∙ (λ i → inr (loop i)) ∙∙ sym (push tt)
      source-petal-loop = cong (λ p → push tt ∙∙ p ∙∙ sym (push tt))
        ((λ j i → inr (cong-∙ (invEq (SS.e 1))
          (push (fzero , false)) (sym (push (fzero , true))) j i))
        ∙ λ j i → inr (rUnit loop (~ j) i))

      circle-conjugation : (p q : ΩS¹) → p ∙∙ q ∙∙ sym p ≡ q
      circle-conjugation p q = doubleCompPath≡compPath p q (sym p)
        ∙ comm-ΩS¹ p _ ∙ sym (assoc _ _ _)
        ∙ cong (q ∙_) (lCancel p) ∙ sym (rUnit q)

      forget-source-cone : (q : Fin n)
        → (projected-quotient q ∘ source-petal) ≡ (projected-quotient q ∘ inr)
      forget-source-cone q = funExt λ
        { base → refl
        ; (loop i) j →
          (cong (cong (projected-quotient q)) source-petal-loop
          ∙ cong-∙∙ (projected-quotient q) (push tt) (λ i → inr (loop i)) (sym (push tt))
          ∙ circle-conjugation (cong (projected-quotient q) (push tt))
              (cong (projected-quotient q ∘ inr) loop)) j i }

      petal-degree : (q : Fin n)
        → degree 1 (λ x → pickPetal q (inr (k , x))) ≡ ℤFinGenerator k q
      petal-degree q =
        isGeneratorℤFinGenerator' (λ w → degree 1 (λ x → pickPetal q (inr (w , x)))) k
        ∙ funExt⁻ (funExt⁻ (cong fst (bouquetDegreeId {n = 1} {m = n})) (ℤFinGenerator k)) q

  abstract
    quotient-degree : (q : Fin n)
      → degree 1 (λ x → pickPetal q (Q.bouquetFunct (inr (fzero , x))))
        ≡ ℤFinGenerator k q
    quotient-degree q = cong (degree 1)
      (forget-source-cone q ∙ funExt (λ x → cong (pickPetal q) (target-collapse (inr (k , x)))))
      ∙ petal-degree q

    edge-chain-generator : fst Q.chainFunct (ℤFinGenerator fzero) ≡ ℤFinGenerator k
    edge-chain-generator = funExt λ q →
      sym (isGeneratorℤFinGenerator'
        (λ w → degree 1 (λ x → pickPetal q (Q.bouquetFunct (inr (w , x))))) fzero)
      ∙ quotient-degree q

    homology-generator : fst (H̃ˢᵏᵉˡ→ {C = S} {D = T} 1 realization) (genHₙSⁿ 0)
      ≡ genH̃ˢᵏᵉˡSphereBouquet/ˢᵏᵉˡ α k
    homology-generator = cong (λ h → fst h (genHₙSⁿ 0)) homology-beta
      ∙ cong SQ.[_] (Σ≡Prop (λ _ → isSetΠ (λ _ → isSetℤ) _ _)
        (cong {A = Fin 1 → ℤ} {B = λ _ → Fin n → ℤ}
          (fst Q.chainFunct) one-is-generator
        ∙ edge-chain-generator))
      where
      one-is-generator : (λ (_ : Fin 1) → pos 1) ≡ ℤFinGenerator fzero
      one-is-generator = funExt λ { (zero , tt) → refl }
