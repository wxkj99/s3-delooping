{-# OPTIONS --safe --cubical #-}
module DeloopS3.Cert.Interpret.Terminal where

-- Terminal basis, shear, and gauge moves on Realization's untruncated diagrams.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; zero; suc; _≡ᵇ_)
open import Cubical.Data.Bool using (Bool; true; false; not; _and_; if_then_else_; false≢true)
open import Cubical.Data.List.Base using (List; []; _∷_)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc)
import Cubical.Data.Empty as Empty
import Cubical.Data.Int as Z
open import Cubical.Relation.Nullary using (yes; no)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup; ℤHom)
open import Cubical.HITs.EilenbergMacLane1.Base using (emsquash; emloop-1g)
open import Cubical.HITs.EilenbergMacLane1.Properties using (elimSet)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (assocₖ; commₖ; rUnitₖ; addIso)
open import Cubical.HITs.Pushout.Base using (inl; inr; push)
import Cubical.HITs.Pushout.Properties as PO
open import Cubical.HITs.S1.Base using (S¹; base; loop)
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
open import DeloopS3.Cert.Interpret.Syntax
open import DeloopS3.Cert.Interpret.Realization
open import DeloopS3.Cert.Interpret.Realized public
open import DeloopS3.Move.CancelLoopCell using (module PushoutUP)
open import DeloopS3.Move.CancelGeneral using (module CircleCoordinates)
open CircleCoordinates using (mulC-add; mulC-compose)
open import DeloopS3.Move.ShearFormula using (TκEquiv; module ClassifyingAddition)
open import DeloopS3.Move.PrimitiveTotal using (unshear-fibre)
import DeloopS3.Cover.Orientation.CircleModel as Circle

private variable
  A B : Type
  ℓ : Level

abstract
  -- The cocone is prescribed by the span squares, not extracted from an
  -- arbitrary equivalence. The seam is precisely the pushout map's filler.
  span-step : (n : ℕ) (S S′ : Ch.State) → WellFormed n S′
    → SpanEquiv (diagram S′) (diagram S) → RealizedStep n S S′
  span-step n S S′ wf e = record
    { next-wf = wf
    ; total = invEquiv back
    ; backLeft = λ x → inl (equivFun (SpanEquiv.leftVertex e) x)
    ; backRight = λ x → inr (equivFun (SpanEquiv.rightVertex e) x)
    ; backSeam = λ a → cong inl (SpanEquiv.leftSquare e a)
        ∙∙ push (equivFun (SpanEquiv.overlapEquiv e) a)
        ∙∙ sym (cong inr (SpanEquiv.rightSquare e a))
    ; back-rec = funExt λ { (inl x) → refl ; (inr x) → refl ; (push a i) → refl } }
    where
    back : T S′ ≃ T S
    back = PO.pushoutEquiv (left S′) (right S′) (left S) (right S)
      (SpanEquiv.overlapEquiv e) (SpanEquiv.leftVertex e) (SpanEquiv.rightVertex e)
      (funExt (SpanEquiv.leftSquare e)) (funExt (SpanEquiv.rightSquare e))

  -- Public coordinate equation, including the seam, across the abstract
  -- total-equivalence boundary. Its endpoints are the prescribed cocones.
  span-step-cocone : (n : ℕ) (S S′ : Ch.State) (wf : WellFormed n S′)
    (e : SpanEquiv (diagram S′) (diagram S))
    → Path (PushoutUP.Cocone (left S′) (right S′) (T S))
      (RealizedStep.backLeft (span-step n S S′ wf e) ,
       RealizedStep.backRight (span-step n S S′ wf e) ,
       RealizedStep.backSeam (span-step n S S′ wf e))
      ((λ x → inl (equivFun (SpanEquiv.leftVertex e) x)) ,
       (λ x → inr (equivFun (SpanEquiv.rightVertex e) x)) ,
       (λ a → cong inl (SpanEquiv.leftSquare e a)
         ∙∙ push (equivFun (SpanEquiv.overlapEquiv e) a)
         ∙∙ sym (cong inr (SpanEquiv.rightSquare e a))))
  span-step-cocone n S S′ wf e = refl

  -- Reindex a mapped list by positions; names are never topological points.
  map-index : (f : A → B) (xs : List A)
    → Fin (P.length xs) → Fin (P.length (P.map f xs))
  map-index f [] ()
  map-index f (x ∷ xs) fzero = fzero
  map-index f (x ∷ xs) (fsuc i) = fsuc (map-index f xs i)

  back-index : (f : A → B) (xs : List A)
    → Fin (P.length (P.map f xs)) → Fin (P.length xs)
  back-index f [] ()
  back-index f (x ∷ xs) fzero = fzero
  back-index f (x ∷ xs) (fsuc i) = fsuc (back-index f xs i)

  map-index-sec : (f : A → B) (xs : List A) (i : Fin (P.length (P.map f xs)))
    → map-index f xs (back-index f xs i) ≡ i
  map-index-sec f [] ()
  map-index-sec f (x ∷ xs) fzero = refl
  map-index-sec f (x ∷ xs) (fsuc i) = cong fsuc (map-index-sec f xs i)

  map-index-ret : (f : A → B) (xs : List A) (i : Fin (P.length xs))
    → back-index f xs (map-index f xs i) ≡ i
  map-index-ret f [] ()
  map-index-ret f (x ∷ xs) fzero = refl
  map-index-ret f (x ∷ xs) (fsuc i) = cong fsuc (map-index-ret f xs i)

  map-index-equiv : (f : A → B) (xs : List A)
    → Fin (P.length (P.map f xs)) ≃ Fin (P.length xs)
  map-index-equiv f xs = isoToEquiv (iso (back-index f xs) (map-index f xs)
    (map-index-ret f xs) (map-index-sec f xs))

  map-index-equiv-map : (f : A → B) (xs : List A) (i : Fin (P.length (P.map f xs)))
    → equivFun (map-index-equiv f xs) i ≡ back-index f xs i
  map-index-equiv-map f xs i = refl

  at-back-index : (f : A → B) (xs : List A) (i : Fin (P.length (P.map f xs)))
    → at (P.map f xs) i ≡ f (at xs (back-index f xs i))
  at-back-index f [] ()
  at-back-index f (x ∷ xs) fzero = refl
  at-back-index f (x ∷ xs) (fsuc i) = at-back-index f xs i

  mul-pres+ : (d : Z.ℤ) (u v : C) → mulC d (u +C v) ≡ mulC d u +C mulC d v
  mul-pres+ d = ClassifyingAddition.B-pres+ {G = ℤAbGroup} {H = ℤAbGroup} (ℤHom d)

  swap-last : (a b c : C) → (a +C b) +C c ≡ (a +C c) +C b
  swap-last a b c = sym (assocₖ {G = ℤAbGroup} 1 a b c)
    ∙ cong (a +C_) (commₖ {G = ℤAbGroup} 1 b c)
    ∙ assocₖ {G = ℤAbGroup} 1 a c b

  row-shear : (s d q : Z.ℤ) (u t : C)
    → mulC s u +C mulC d (t +C mulC q u)
      ≡ mulC (s Z.+ (d Z.· q)) u +C mulC d t
  row-shear s d q u t = cong (mulC s u +C_) (mul-pres+ d t (mulC q u))
    ∙ cong (λ z → mulC s u +C (mulC d t +C z)) (mulC-compose d q u)
    ∙ assocₖ {G = ℤAbGroup} 1 (mulC s u) (mulC d t) (mulC (d Z.· q) u)
    ∙ swap-last (mulC s u) (mulC d t) (mulC (d Z.· q) u)
    ∙ cong (_+C mulC d t) (sym (mulC-add s (d Z.· q) u))

  effective-int : (f : Ch.Face)
    → int (Ch.effective f) ≡ int (Ch.faceWeight f) Z.+ (Z.pos (Ch.faceOrder f) Z.· (Z.- int (Ch.faceH f)))
  effective-int f = int-subtract (Ch.faceWeight f) (P.scale (Ch.faceOrder f) (Ch.faceH f))
    ∙ cong (λ z → int (Ch.faceWeight f) Z.- z) (int-scale (Ch.faceOrder f) (Ch.faceH f))
    ∙ cong (int (Ch.faceWeight f) Z.+_) (Z.-DistR· (Z.pos (Ch.faceOrder f)) (int (Ch.faceH f)))

  mul-zero : (u : C) → mulC (Z.pos 0) u ≡ 0C
  mul-zero = elimSet ℤGroup (λ _ → emsquash _ _) refl
    (λ g i j → emloop-1g ℤGroup j i)

  module MappedFaces (gs : List ℕ) (fs : List Ch.Face) (f : Ch.Face → Ch.Face) where
    old new : Ch.State
    old = Ch.state gs fs
    new = Ch.state gs (P.map f fs)

    indices : FaceIx new ≃ FaceIx old
    indices = map-index-equiv f fs

    back : FaceIx new → FaceIx old
    back = equivFun indices

    face : (i : FaceIx new) → faceAt new i ≡ f (faceAt old (back i))
    face i = at-back-index f fs i
      ∙ cong (λ j → f (at fs j)) (sym (map-index-equiv-map f fs i))

    left-normal : (i : FaceIx new) (u t : C)
      → left new (i , u , t) ≡
        (wordCircle gs (Ch.faceWord (f (faceAt old (back i)))) u ,
         t +C mulC (int (Ch.faceH (f (faceAt old (back i))))) u)
    left-normal i u t = cong (λ a → wordCircle gs (Ch.faceWord a) u , t +C mulC (int (Ch.faceH a)) u) (face i)

    right-normal : (i : FaceIx new) (u t : C)
      → right new (i , u , t) ≡
        (i , mulC (int (Ch.faceWeight (f (faceAt old (back i))))) u
          +C mulC (Z.pos (Ch.faceOrder (f (faceAt old (back i))))) t)
    right-normal i u t = cong (λ a → i , mulC (int (Ch.faceWeight a)) u
      +C mulC (Z.pos (Ch.faceOrder a)) t) (face i)

  module Unshear (S : Ch.State) where
    module M = MappedFaces (Ch.alive S) (Ch.faces S) unshearFace

    overlap-back : O (unshearState S) ≃ O S
    overlap-back = compEquiv (Σ-cong-equiv-fst M.indices)
      (Σ-cong-equiv-snd λ i → TκEquiv (Z.- int (Ch.faceH (faceAt S i))))

    core-back : R (unshearState S) ≃ R S
    core-back = Σ-cong-equiv-fst M.indices

    left-square : (a : O (unshearState S))
      → left (unshearState S) a ≡ left S (equivFun overlap-back a)
    left-square (i , u , t) = M.left-normal i u t
      ∙ ΣPathP (refl , (cong (t +C_) (mul-zero u)
        ∙ rUnitₖ {G = ℤAbGroup} 1 t
        ∙ sym (unshear-fibre (int (Ch.faceH (faceAt S (M.back i)))) u t)))

    right-square : (a : O (unshearState S))
      → equivFun core-back (right (unshearState S) a) ≡ right S (equivFun overlap-back a)
    right-square (i , u , t) = cong (equivFun core-back) (M.right-normal i u t)
      ∙ cong (M.back i ,_) (cong (λ z → mulC z u +C mulC (Z.pos (Ch.faceOrder f)) t) (effective-int f)
        ∙ sym (row-shear (int (Ch.faceWeight f)) (Z.pos (Ch.faceOrder f)) (Z.- int (Ch.faceH f)) u t))
      where
      f : Ch.Face
      f = faceAt S (M.back i)

    span : SpanEquiv (diagram (unshearState S)) (diagram S)
    span = record { overlapEquiv = overlap-back ; leftVertex = idEquiv (L S)
      ; rightVertex = core-back ; leftSquare = left-square ; rightSquare = right-square }

    -- The sign and direction of this coordinate change are explicit.
    overlap-formula : (i : FaceIx (unshearState S)) (u t : C)
      → equivFun overlap-back (i , u , t) ≡
        (M.back i , u , t +C mulC (Z.- int (Ch.faceH (faceAt S (M.back i)))) u)
    overlap-formula i u t = refl

  unshear-sound : (ct : Ch.Certificate) (S S′ : Ch.State)
    → WellFormed (suc (Ch.index ct)) S
    → checkMove ct S unshear S′ ≡ true
    → RealizedStep (suc (Ch.index ct)) S S′
  unshear-sound ct S S′ wf ok = subst (RealizedStep n S) snapshot
    (span-step n S (unshearState S)
      (subst (WellFormed n) (sym snapshot) (checkMove-target {ct = ct} {S = S} {S′ = S′} {m = unshear} ok))
      (Unshear.span S))
    where
    n : ℕ
    n = suc (Ch.index ct)
    snapshot : unshearState S ≡ S′
    snapshot = stateEq-sound (unshearState S) S′ (checkMove-clause {ct = ct} {S = S} {S′ = S′} {m = unshear} ok)

  module Gauge (S : Ch.State) (zs : List P.Z) where
    module M = MappedFaces (Ch.alive S) (Ch.faces S) (gaugeFace (Ch.alive S) zs)

    winding : Rose (Ch.alive S) → C
    winding = graphWind (Ch.alive S) zs

    graph-back : L S ≃ L S
    graph-back = Σ-cong-equiv-snd λ x → isoToEquiv (addIso {G = ℤAbGroup} 1 (winding x))

    q : FaceIx S → P.Z
    q i = wind (Ch.alive S) zs (Ch.faceWord (faceAt S i))

    overlap-back : O (gaugeState S zs) ≃ O S
    overlap-back = compEquiv (Σ-cong-equiv-fst M.indices)
      (Σ-cong-equiv-snd λ i → TκEquiv (int (q i)))

    core-back : R (gaugeState S zs) ≃ R S
    core-back = Σ-cong-equiv-fst M.indices

    left-square : (a : O (gaugeState S zs))
      → equivFun graph-back (left (gaugeState S zs) a) ≡ left S (equivFun overlap-back a)
    left-square (i , u , t) = cong (equivFun graph-back) (M.left-normal i u t)
      ∙ ΣPathP (refl , (cong ((t +C mulC (int (Ch.faceH f)) u) +C_)
          (wind-sound (Ch.alive S) zs (Ch.faceWord f) u)
        ∙ swap-last t (mulC (int (Ch.faceH f)) u) (mulC (int (q (M.back i))) u)))
      where
      f : Ch.Face
      f = faceAt S (M.back i)

    right-square : (a : O (gaugeState S zs))
      → equivFun core-back (right (gaugeState S zs) a) ≡ right S (equivFun overlap-back a)
    right-square (i , u , t) = cong (equivFun core-back) (M.right-normal i u t)
      ∙ cong (M.back i ,_) (cong (λ z → mulC z u +C mulC (Z.pos (Ch.faceOrder f)) t)
          (int-add (Ch.faceWeight f) (P.scale (Ch.faceOrder f) (q (M.back i)))
            ∙ cong (int (Ch.faceWeight f) Z.+_) (int-scale (Ch.faceOrder f) (q (M.back i))))
        ∙ sym (row-shear (int (Ch.faceWeight f)) (Z.pos (Ch.faceOrder f)) (int (q (M.back i))) u t))
      where
      f : Ch.Face
      f = faceAt S (M.back i)

    span : SpanEquiv (diagram (gaugeState S zs)) (diagram S)
    span = record { overlapEquiv = overlap-back ; leftVertex = graph-back
      ; rightVertex = core-back ; leftSquare = left-square ; rightSquare = right-square }

    graph-formula : (x : Rose (Ch.alive S)) (t : C)
      → equivFun graph-back (x , t) ≡ (x , t +C graphWind (Ch.alive S) zs x)
    graph-formula x t = refl

    overlap-formula : (i : FaceIx (gaugeState S zs)) (u t : C)
      → equivFun overlap-back (i , u , t) ≡ (M.back i , u , t +C mulC (int (q (M.back i))) u)
    overlap-formula i u t = refl

  gauge-sound : (ct : Ch.Certificate) (S S′ : Ch.State) (zs : List P.Z)
    → WellFormed (suc (Ch.index ct)) S
    → checkMove ct S (gauge zs) S′ ≡ true
    → RealizedStep (suc (Ch.index ct)) S S′
  gauge-sound ct S S′ zs wf ok = subst (RealizedStep n S) snapshot
    (span-step n S (gaugeState S zs)
      (subst (WellFormed n) (sym snapshot) (checkMove-target {ct = ct} {S = S} {S′ = S′} {m = gauge zs} ok))
      (Gauge.span S zs))
    where
    n : ℕ
    n = suc (Ch.index ct)
    snapshot : gaugeState S zs ≡ S′
    snapshot = stateEq-sound (gaugeState S zs) S′
      (and-right {a = P.length zs ≡ᵇ P.length (Ch.alive S)}
        (checkMove-clause {ct = ct} {S = S} {S′ = S′} {m = gauge zs} ok))

-- A specified substitution, not a search for a Nielsen transformation.
subRose : (gs hs : List ℕ) → List P.Word → Rose gs → Rose hs
subRose gs hs ws = roseRec root (λ i → roseWord hs (image gs ws (at gs i)))

abstract
  image-scope : (n : ℕ) (hs gs : List ℕ) (ws : List P.Word) (g : ℕ)
    → P.all (scopedWord n hs) ws ≡ true → inScope hs (image gs ws g) ≡ true
  image-scope n hs [] ws g h = refl
  image-scope n hs (a ∷ gs) [] g h = refl
  image-scope n hs (a ∷ gs) (w ∷ ws) g h with g ≡ᵇ a
  ... | true = and-right {a = P.wordValid n w} (and-left h)
  ... | false = image-scope n hs gs ws g (and-right {a = scopedWord n hs w} h)

  subRose-loop : (gs hs : List ℕ) (ws : List P.Word)
    → P.unique _≡ᵇ_ gs ≡ true → (g : ℕ) → g ∈ gs
    → cong (subRose gs hs ws) (loopAt gs g) ≡ roseWord hs (image gs ws g)
  subRose-loop gs hs ws unique g m = lookup-cong (subRose gs hs ws) gs petal g
    ∙ lookupLoop-member gs (λ i → roseWord hs (image gs ws (at gs i))) unique g m
    ∙ cong (λ h → roseWord hs (image gs ws h)) (member-index m .snd)

  eval-scoped-agree : {X : Type ℓ} {x : X} (gs : List ℕ)
    (p q : ℕ → x ≡ x) → ((g : ℕ) → g ∈ gs → p g ≡ q g)
    → (w : P.Word) → inScope gs w ≡ true → evalWord p w ≡ evalWord q w
  eval-scoped-agree gs p q h [] scope = refl
  eval-scoped-agree gs p q h (P.fwd g ∷ w) scope = cong₂ _∙_
    (h g (member-sound _≡ᵇ_ natEq-sound g gs (and-left scope)))
    (eval-scoped-agree gs p q h w (and-right {a = P.member _≡ᵇ_ g gs} scope))
  eval-scoped-agree gs p q h (P.bwd g ∷ w) scope = cong₂ _∙_
    (cong sym (h g (member-sound _≡ᵇ_ natEq-sound g gs (and-left scope))))
    (eval-scoped-agree gs p q h w (and-right {a = P.member _≡ᵇ_ g gs} scope))

  subRose-word : (gs hs : List ℕ) (ws : List P.Word)
    → P.unique _≡ᵇ_ gs ≡ true → (w : P.Word) → inScope gs w ≡ true
    → cong (subRose gs hs ws) (roseWord gs w) ≡ roseWord hs (substAll gs ws w)
  subRose-word gs hs ws unique w scope = eval-cong (subRose gs hs ws) (loopAt gs) w
    ∙ eval-scoped-agree gs (λ g → cong (subRose gs hs ws) (loopAt gs g))
        (λ g → roseWord hs (image gs ws g)) (subRose-loop gs hs ws unique) w scope
    ∙ sym (eval-substAll (loopAt hs) gs ws w)

  subRose-circle : (gs hs : List ℕ) (ws : List P.Word)
    (unique : P.unique _≡ᵇ_ gs ≡ true) (w : P.Word) (scope : inScope gs w ≡ true) (u : C)
    → subRose gs hs ws (wordCircle gs w u) ≡ wordCircle hs (substAll gs ws w) u
  subRose-circle gs hs ws unique w scope u = on-circle (Circle.CToCircle u)
    where
    on-circle : (v : S¹) → subRose gs hs ws (circleRec root (roseWord gs w) v)
      ≡ circleRec root (roseWord hs (substAll gs ws w)) v
    on-circle base = refl
    on-circle (loop i) j = subRose-word gs hs ws unique w scope j i

module BasisGraph (n : ℕ) (S : Ch.State) (b : Basis2)
  (wf : WellFormed n S) (ok : checkBasis n S b ≡ true) where
  gs hs : List ℕ
  gs = Ch.alive S
  hs = twoGenerators

  forward : Rose gs → Rose hs
  forward = subRose gs hs (oldInNew b)

  backward : Rose hs → Rose gs
  backward = subRose hs gs (newInOld b)

  abstract
    forward-scope : (g : ℕ) → inScope hs (image gs (oldInNew b) g) ≡ true
    forward-scope g = image-scope 2 hs gs (oldInNew b) g (test-true (basisTests n S b) 4 ok)

    backward-scope : (g : ℕ) → inScope gs (image hs (newInOld b) g) ≡ true
    backward-scope g = image-scope n gs hs (newInOld b) g (test-true (basisTests n S b) 5 ok)

    old-composite : (g : ℕ) → g ∈ gs
      → substAll hs (newInOld b) (image gs (oldInNew b) g) ≡ (P.fwd g ∷ [])
    old-composite g m = wordEq-sound _ _
      (all-sound (λ g → P.wordEq (substAll hs (newInOld b) (image gs (oldInNew b) g)) (P.fwd g ∷ []))
        (test-true (basisTests n S b) 6 ok) m)

    new-composite : (g : ℕ) → g ∈ hs
      → substAll gs (oldInNew b) (image hs (newInOld b) g) ≡ (P.fwd g ∷ [])
    new-composite g m = wordEq-sound _ _
      (all-sound (λ g → P.wordEq (substAll gs (oldInNew b) (image hs (newInOld b) g)) (P.fwd g ∷ []))
        (test-true (basisTests n S b) 7 ok) m)

    backward-forward : (x : Rose gs) → backward (forward x) ≡ x
    backward-forward root = refl
    backward-forward (petal i j) k =
      (subRose-word hs gs (newInOld b) refl (image gs (oldInNew b) (at gs i)) (forward-scope (at gs i))
        ∙ cong (roseWord gs) (old-composite (at gs i) (at-member gs i))
        ∙ sym (rUnit (loopAt gs (at gs i)))
        ∙ loopAt-index gs (alive-distinct wf) i) k j

    forward-backward : (x : Rose hs) → forward (backward x) ≡ x
    forward-backward root = refl
    forward-backward (petal i j) k =
      (subRose-word gs hs (oldInNew b) (alive-distinct wf)
          (image hs (newInOld b) (at hs i)) (backward-scope (at hs i))
        ∙ cong (roseWord hs) (new-composite (at hs i) (at-member hs i))
        ∙ sym (rUnit (loopAt hs (at hs i))) ∙ loopAt-index hs refl i) k j

    graph-equiv : Rose gs ≃ Rose hs
    graph-equiv = isoToEquiv (iso forward backward forward-backward backward-forward)

    graph-forward : equivFun graph-equiv ≡ forward
    graph-forward = refl

    graph-backward : invEq graph-equiv ≡ backward
    graph-backward = refl

    -- The entire circle homotopy, not only equality in the free group.
    backward-boundary : (w : P.Word) → inScope gs w ≡ true → (u : C)
      → backward (wordCircle hs (substAll gs (oldInNew b) w) u) ≡ wordCircle gs w u
    backward-boundary w scope u =
      sym (cong backward (subRose-circle gs hs (oldInNew b) (alive-distinct wf) w scope u))
      ∙ backward-forward (wordCircle gs w u)

-- Selection/relabeling is a finite index equivalence, independent of graph
-- homotopy. Successful lookup and exhaustive distinct IDs are all retained.
open import DeloopS3.Groups.TablePermutation using (unique-injective)

record Selected (ids : List ℕ) (fs : List Ch.Face) : Type where
  field
    chosen : List Ch.Face
    lookup-ok : Ch.getFaces ids fs ≡ P.just chosen
    names : P.map Ch.faceId chosen ≡ ids
    included : (f : Ch.Face) → f ∈ chosen → f ∈ fs
open Selected

abstract
  at-map-index : (f : A → B) (xs : List A) (i : Fin (P.length xs))
    → at (P.map f xs) (map-index f xs i) ≡ f (at xs i)
  at-map-index f [] ()
  at-map-index f (x ∷ xs) fzero = refl
  at-map-index f (x ∷ xs) (fsuc i) = at-map-index f xs i

  face-index-injective : (fs : List Ch.Face) → P.unique _≡ᵇ_ (P.map Ch.faceId fs) ≡ true
    → (i j : Fin (P.length fs)) → Ch.faceId (at fs i) ≡ Ch.faceId (at fs j) → i ≡ j
  face-index-injective fs unique i j p = sym (map-index-ret Ch.faceId fs i)
    ∙ cong (back-index Ch.faceId fs)
        (unique-injective _≡ᵇ_ natEq-refl (P.map Ch.faceId fs) unique
          (map-index Ch.faceId fs i) (map-index Ch.faceId fs j)
          (at-map-index Ch.faceId fs i ∙ p ∙ sym (at-map-index Ch.faceId fs j)))
    ∙ map-index-ret Ch.faceId fs j

  face-id-injective : (fs : List Ch.Face) → P.unique _≡ᵇ_ (P.map Ch.faceId fs) ≡ true
    → (f g : Ch.Face) → f ∈ fs → g ∈ fs → Ch.faceId f ≡ Ch.faceId g → f ≡ g
  face-id-injective fs unique f g mf mg p = sym (member-index mf .snd)
    ∙ cong (at fs) (face-index-injective fs unique (member-index mf .fst) (member-index mg .fst)
        (cong Ch.faceId (member-index mf .snd) ∙ p ∙ sym (cong Ch.faceId (member-index mg .snd))))
    ∙ member-index mg .snd

  other-tail : {k h : ℕ} {hs : List ℕ} → k ∈ (h ∷ hs)
    → ((h ≡ᵇ k) ≡ true → Empty.⊥) → k ∈ hs
  other-tail {k = k} here ne = Empty.rec (ne (natEq-refl k))
  other-tail (there m) ne = m

  getFace-present : (k : ℕ) (fs : List Ch.Face) → k ∈ P.map Ch.faceId fs
    → Σ[ f ∈ Ch.Face ] ((Ch.getFace k fs ≡ P.just f) × (f ∈ fs) × (Ch.faceId f ≡ k))
  getFace-present k [] ()
  getFace-present k (f ∷ fs) member with bool-dec (Ch.faceId f ≡ᵇ k)
  ... | yes e = f , cong (λ b → if b then P.just f else Ch.getFace k fs) e , here , natEq-sound _ _ e
  ... | no ne = result .fst ,
      (cong (λ b → if b then P.just f else Ch.getFace k fs) (test-false (Ch.faceId f ≡ᵇ k) ne)
        ∙ result .snd .fst) , there (result .snd .snd .fst) , result .snd .snd .snd
    where
    result : Σ[ g ∈ Ch.Face ] ((Ch.getFace k fs ≡ P.just g) × (g ∈ fs) × (Ch.faceId g ≡ k))
    result = getFace-present k fs (other-tail member ne)

join-selected : P.Maybe Ch.Face → P.Maybe (List Ch.Face) → P.Maybe (List Ch.Face)
join-selected (P.just f) (P.just fs) = P.just (f ∷ fs)
join-selected _ _ = P.nothing

abstract
  getFaces-cons : (k : ℕ) (ks : List ℕ) (fs : List Ch.Face)
    → Ch.getFaces (k ∷ ks) fs ≡ join-selected (Ch.getFace k fs) (Ch.getFaces ks fs)
  getFaces-cons k ks fs with Ch.getFace k fs | Ch.getFaces ks fs
  ... | P.just f | P.just rest = refl
  ... | P.just f | P.nothing = refl
  ... | P.nothing | r = refl

  select-faces : (ids : List ℕ) (fs : List Ch.Face)
    → ((k : ℕ) → k ∈ ids → k ∈ P.map Ch.faceId fs) → Selected ids fs
  select-faces [] fs member = record
    { chosen = [] ; lookup-ok = refl ; names = refl ; included = λ f () }
  select-faces (k ∷ ks) fs member = record
    { chosen = hit .fst ∷ chosen rest
    ; lookup-ok = getFaces-cons k ks fs ∙ cong₂ join-selected (hit .snd .fst) (lookup-ok rest)
    ; names = cong₂ _∷_ (hit .snd .snd .snd) (names rest)
    ; included = inclusion }
    where
    hit : Σ[ f ∈ Ch.Face ] ((Ch.getFace k fs ≡ P.just f) × (f ∈ fs) × (Ch.faceId f ≡ k))
    hit = getFace-present k fs (member k here)
    rest : Selected ks fs
    rest = select-faces ks fs (λ j m → member j (there m))
    inclusion : (f : Ch.Face) → f ∈ (hit .fst ∷ chosen rest) → f ∈ fs
    inclusion f here = hit .snd .snd .fst
    inclusion f (there m) = included rest f m

module SelectedFaces (n : ℕ) (S : Ch.State) (b : Basis2)
  (wf : WellFormed n S) (ok : checkBasis n S b ≡ true) where
  ids : List ℕ
  ids = faceOrder b
  fs : List Ch.Face
  fs = Ch.faces S

  abstract
    exhaustive : P.setEq _≡ᵇ_ ids (P.map Ch.faceId fs) ≡ true
    exhaustive = test-true (basisTests n S b) 10 ok

    select-member : (k : ℕ) → k ∈ ids → k ∈ P.map Ch.faceId fs
    select-member k m = member-sound _≡ᵇ_ natEq-sound k (P.map Ch.faceId fs)
      (all-sound (λ k → P.member _≡ᵇ_ k (P.map Ch.faceId fs)) (and-left exhaustive) m)

    selection : Selected ids fs
    selection = select-faces ids fs select-member

  selected : List Ch.Face
  selected = chosen selection

  abstract
    selected-unique : P.unique _≡ᵇ_ (P.map Ch.faceId selected) ≡ true
    selected-unique = cong (P.unique _≡ᵇ_) (names selection) ∙ test-true (basisTests n S b) 9 ok

    old-in-selected : (f : Ch.Face) → f ∈ fs → f ∈ selected
    old-in-selected f m = subst (λ g → g ∈ selected)
      (face-id-injective fs (ids-distinct wf) (hit .fst) f
        (included selection (hit .fst) (hit .snd .fst)) m (hit .snd .snd))
      (hit .snd .fst)
      where
      name-in-ids : Ch.faceId f ∈ ids
      name-in-ids = member-sound _≡ᵇ_ natEq-sound (Ch.faceId f) ids
        (all-sound (λ k → P.member _≡ᵇ_ k ids)
          (and-right {a = P.all (λ k → P.member _≡ᵇ_ k (P.map Ch.faceId fs)) ids} exhaustive)
          (map-member Ch.faceId m))
      hit : Σ[ g ∈ Ch.Face ] ((g ∈ selected) × (Ch.faceId g ≡ Ch.faceId f))
      hit = map-member⁻ Ch.faceId selected
        (subst (λ ks → Ch.faceId f ∈ ks) (sym (names selection)) name-in-ids)

  to-old : Fin (P.length selected) → Fin (P.length fs)
  to-old i = member-index (included selection (at selected i) (at-member selected i)) .fst

  from-old : Fin (P.length fs) → Fin (P.length selected)
  from-old i = member-index (old-in-selected (at fs i) (at-member fs i)) .fst

  abstract
    to-face : (i : Fin (P.length selected)) → at fs (to-old i) ≡ at selected i
    to-face i = member-index (included selection (at selected i) (at-member selected i)) .snd

    from-face : (i : Fin (P.length fs)) → at selected (from-old i) ≡ at fs i
    from-face i = member-index (old-in-selected (at fs i) (at-member fs i)) .snd

    indices : Fin (P.length selected) ≃ FaceIx S
    indices = isoToEquiv (iso to-old from-old
      (λ i → face-index-injective fs (ids-distinct wf) (to-old (from-old i)) i
        (cong Ch.faceId (to-face (from-old i) ∙ from-face i)))
      (λ i → face-index-injective selected selected-unique (from-old (to-old i)) i
        (cong Ch.faceId (from-face (to-old i) ∙ to-face i))))

    indices-face : (i : Fin (P.length selected)) → faceAt S (equivFun indices i) ≡ at selected i
    indices-face = to-face

FaceShape : Type
FaceShape = ℕ × P.Z × P.Word × P.Z

shape : Ch.Face → FaceShape
shape f = Ch.faceOrder f , Ch.faceWeight f , Ch.faceWord f , Ch.faceH f

-- IDs are deliberately absent: they name lookup entries, not attaching maps.
module Rebased (gs : List ℕ) (ws : List P.Word) where
  transformed : Ch.Face → FaceShape
  transformed f = Ch.faceOrder f , Ch.faceWeight f , substAll gs ws (Ch.faceWord f) , Ch.faceH f

  down : (k : ℕ) (fs : List Ch.Face) → Fin (P.length (rebaseFaces gs ws k fs)) → Fin (P.length fs)
  down k [] ()
  down k (f ∷ fs) fzero = fzero
  down k (f ∷ fs) (fsuc i) = fsuc (down (suc k) fs i)

  up : (k : ℕ) (fs : List Ch.Face) → Fin (P.length fs) → Fin (P.length (rebaseFaces gs ws k fs))
  up k [] ()
  up k (f ∷ fs) fzero = fzero
  up k (f ∷ fs) (fsuc i) = fsuc (up (suc k) fs i)

  abstract
    down-up : (k : ℕ) (fs : List Ch.Face) (i : Fin (P.length fs)) → down k fs (up k fs i) ≡ i
    down-up k [] ()
    down-up k (f ∷ fs) fzero = refl
    down-up k (f ∷ fs) (fsuc i) = cong fsuc (down-up (suc k) fs i)

    up-down : (k : ℕ) (fs : List Ch.Face) (i : Fin (P.length (rebaseFaces gs ws k fs)))
      → up k fs (down k fs i) ≡ i
    up-down k [] ()
    up-down k (f ∷ fs) fzero = refl
    up-down k (f ∷ fs) (fsuc i) = cong fsuc (up-down (suc k) fs i)

    indices : (k : ℕ) (fs : List Ch.Face)
      → Fin (P.length (rebaseFaces gs ws k fs)) ≃ Fin (P.length fs)
    indices k fs = isoToEquiv (iso (down k fs) (up k fs) (down-up k fs) (up-down k fs))

    down-shape : (k : ℕ) (fs : List Ch.Face) (i : Fin (P.length (rebaseFaces gs ws k fs)))
      → shape (at (rebaseFaces gs ws k fs) i) ≡ transformed (at fs (down k fs i))
    down-shape k [] ()
    down-shape k (f ∷ fs) fzero = refl
    down-shape k (f ∷ fs) (fsuc i) = down-shape (suc k) fs i

    indices-shape : (k : ℕ) (fs : List Ch.Face) (i : Fin (P.length (rebaseFaces gs ws k fs)))
      → shape (at (rebaseFaces gs ws k fs) i) ≡ transformed (at fs (equivFun (indices k fs) i))
    indices-shape = down-shape

basisSelectedState : (S : Ch.State) (b : Basis2) → P.Maybe (List Ch.Face) → Ch.State
basisSelectedState S b P.nothing = Ch.state twoGenerators []
basisSelectedState S b (P.just fs) = Ch.state twoGenerators (rebaseFaces (Ch.alive S) (oldInNew b) 0 fs)

abstract
  basisState-view : (S : Ch.State) (b : Basis2)
    → basisState S b ≡ basisSelectedState S b (Ch.getFaces (faceOrder b) (Ch.faces S))
  basisState-view S b with Ch.getFaces (faceOrder b) (Ch.faces S)
  ... | P.nothing = refl
  ... | P.just fs = refl

module BasisSpan (n : ℕ) (S : Ch.State) (b : Basis2)
  (wf : WellFormed n S) (ok : checkBasis n S b ≡ true) where
  module G = BasisGraph n S b wf ok
  module F = SelectedFaces n S b wf ok
  module B = Rebased (Ch.alive S) (oldInNew b)

  new : Ch.State
  new = Ch.state twoGenerators (rebaseFaces (Ch.alive S) (oldInNew b) 0 F.selected)

  abstract
    computed : basisState S b ≡ new
    computed = basisState-view S b ∙ cong (basisSelectedState S b) (lookup-ok F.selection)

    indices : FaceIx new ≃ FaceIx S
    indices = compEquiv (B.indices 0 F.selected) F.indices

    face-shape : (i : FaceIx new) → shape (faceAt new i) ≡ B.transformed (faceAt S (equivFun indices i))
    face-shape i = B.indices-shape 0 F.selected i
      ∙ cong B.transformed (sym (F.indices-face (equivFun (B.indices 0 F.selected) i)))

    graph-back : L new ≃ L S
    graph-back = Σ-cong-equiv-fst (invEquiv G.graph-equiv)

    overlap-back : O new ≃ O S
    overlap-back = Σ-cong-equiv-fst indices

    core-back : R new ≃ R S
    core-back = Σ-cong-equiv-fst indices

    left-normal : (i : FaceIx new) (u t : C)
      → left new (i , u , t) ≡
        (wordCircle twoGenerators (substAll (Ch.alive S) (oldInNew b) (Ch.faceWord (faceAt S (equivFun indices i)))) u ,
         t +C mulC (int (Ch.faceH (faceAt S (equivFun indices i)))) u)
    left-normal i u t = cong (λ (a : FaceShape) → wordCircle twoGenerators (a .snd .snd .fst) u ,
      t +C mulC (int (a .snd .snd .snd)) u) (face-shape i)

    right-normal : (i : FaceIx new) (u t : C)
      → right new (i , u , t) ≡
        (i , mulC (int (Ch.faceWeight (faceAt S (equivFun indices i)))) u
          +C mulC (Z.pos (Ch.faceOrder (faceAt S (equivFun indices i)))) t)
    right-normal i u t = cong (λ (a : FaceShape) → i , mulC (int (a .snd .fst)) u
      +C mulC (Z.pos (a .fst)) t) (face-shape i)

    left-square : (a : O new) → equivFun graph-back (left new a) ≡ left S (equivFun overlap-back a)
    left-square (i , u , t) = cong (equivFun graph-back) (left-normal i u t)
      ∙ ΣPathP ((funExt⁻ G.graph-backward
          (wordCircle twoGenerators (substAll (Ch.alive S) (oldInNew b) (Ch.faceWord f)) u)
        ∙ G.backward-boundary (Ch.faceWord f) scope u) , refl)
      where
      j : FaceIx S
      j = equivFun indices i
      f : Ch.Face
      f = faceAt S j
      scope : inScope (Ch.alive S) (Ch.faceWord f) ≡ true
      scope = and-right {a = P.wordValid n (Ch.faceWord f)}
        (all-sound (λ f → scopedWord n (Ch.alive S) (Ch.faceWord f)) (words-in-scope wf) (at-member (Ch.faces S) j))

    right-square : (a : O new) → equivFun core-back (right new a) ≡ right S (equivFun overlap-back a)
    right-square (i , u , t) = cong (equivFun core-back) (right-normal i u t)

    span : SpanEquiv (diagram new) (diagram S)
    span = record { overlapEquiv = overlap-back ; leftVertex = graph-back
      ; rightVertex = core-back ; leftSquare = left-square ; rightSquare = right-square }

    graph-formula : (x : Rose twoGenerators) (t : C)
      → equivFun graph-back (x , t) ≡ (subRose twoGenerators (Ch.alive S) (newInOld b) x , t)
    graph-formula x t = ΣPathP (funExt⁻ G.graph-backward x , refl)

    overlap-formula : (i : FaceIx new) (u t : C)
      → equivFun overlap-back (i , u , t) ≡ (equivFun indices i , u , t)
    overlap-formula i u t = refl

abstract
  basis₂-sound : (ct : Ch.Certificate) (S S′ : Ch.State) (b : Basis2)
    → WellFormed (suc (Ch.index ct)) S
    → checkMove ct S (basis₂ b) S′ ≡ true
    → RealizedStep (suc (Ch.index ct)) S S′
  basis₂-sound ct S S′ b wf ok = subst (RealizedStep n S) snapshot
    (span-step n S B.new
      (subst (WellFormed n) (sym snapshot) (checkMove-target {ct = ct} {S = S} {S′ = S′} {m = basis₂ b} ok)) B.span)
    where
    n : ℕ
    n = suc (Ch.index ct)
    clause : checkBasis n S b and Ch.stateEq (basisState S b) S′ ≡ true
    clause = checkMove-clause {ct = ct} {S = S} {S′ = S′} {m = basis₂ b} ok
    module B = BasisSpan n S b wf (and-left clause)
    snapshot : B.new ≡ S′
    snapshot = sym B.computed ∙ stateEq-sound (basisState S b) S′
      (and-right {a = checkBasis n S b} clause)
