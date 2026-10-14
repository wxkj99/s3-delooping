{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.Telescope where

-- Sequential-colimit flattening, identity codes, and stationary loop
-- comparison, together with finite loop powers and localization uniqueness.
-- The power-telescope equivalences take locality and the universal property
-- as explicit parameters; the final delooping uses the finite Route B proof.

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; idfun)
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (compPath→Square)
open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _·_)
open import Cubical.Data.Sequence
open import Cubical.Data.Sigma using (ΣPathP)
open import Cubical.HITs.SequentialColimit.Base
open import Cubical.Homotopy.Loopspace using (Ω ; Ω→)
open import Cubical.Homotopy.Connected using (isConnected)
open import Cubical.HITs.S1.Base using (S¹)
import Cubical.HITs.Localization as Localization
open import DeloopS3.Local.Base using (powLoop ; deg₁)
open import DeloopS3.Local.Unique using (module Unique)

-- Port of Loc.SeqFlattenEquiv (no mathematical changes).
module EquivFlatten where

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.Univalence
  open import Cubical.Data.Nat.Base using (ℕ ; suc)
  open import Cubical.Data.Sequence.Base
  open import Cubical.HITs.SequentialColimit.Base

  module Flatten {ℓx ℓy} (X : Sequence ℓx)
    (Y : (n : ℕ) → Sequence.obj X n → Type ℓy)
    (e : {n : ℕ} (x : Sequence.obj X n) → Y n x ≃ Y (suc n) (Sequence.map X x)) where

    Total : Sequence (ℓ-max ℓx ℓy)
    Sequence.obj Total n = Σ (Sequence.obj X n) (Y n)
    Sequence.map Total (x , y) = Sequence.map X x , equivFun (e x) y

    Family : SeqColim X → Type ℓy
    Family (incl {n} x) = Y n x
    Family (push x i) = ua (e x) i

    total : SeqColim Total → Σ (SeqColim X) Family
    total (incl (x , y)) = incl x , y
    total (push (x , y) i) = push x i , ua-gluePt (e x) i y

    flatten : Σ (SeqColim X) Family → SeqColim Total
    flatten (incl (x) , y) = incl (x , y)
    flatten (push x i , y) = hcomp
      (λ j → λ { (i = i0) → push (x , y) (~ j)
                 ; (i = i1) → incl (Sequence.map X x , y) })
      (incl (Sequence.map X x , ua-unglue (e x) i y))

    flatten-total : (z : SeqColim Total) → flatten (total z) ≡ z
    flatten-total (incl (x , y)) = refl
    flatten-total (push (x , y) i) j = hcomp
      (λ k → λ { (i = i0) → push (x , ua-gluePt (e x) i0 y) (~ k)
                 ; (i = i1) → incl (Sequence.map X x , ua-gluePt (e x) i1 y)
                 ; (j = i1) → push (x , y) (i ∨ ~ k) })
      (incl (Sequence.map X x , ua-unglue (e x) i (ua-gluePt (e x) i y)))

    private
      glue-square : ∀ {ℓ} {A B : Type ℓ} (d : A ≃ B)
        → SquareP (λ i k → ua d i → ua d (i ∨ ~ k))
          (λ k x → ua-gluePt d (~ k) x) (λ k x → x)
          (λ i x → ua-unglue d i x) (λ i x → x)
      glue-square d i k x = ua-glue d (i ∨ ~ k)
        (λ { ((i ∨ ~ k) = i0) → x }) (inS (ua-unglue d i x))

    total-flatten : (z : Σ (SeqColim X) Family) → total (flatten z) ≡ z
    total-flatten (incl x , y) = refl
    total-flatten (push x i , y) j = comp (λ _ → Σ (SeqColim X) Family)
      (λ k → λ { (i = i0) → push x (~ k) , ua-gluePt (e x) (~ k) y
                 ; (i = i1) → incl (Sequence.map X x) , y
                 ; (j = i1) → push x (i ∨ ~ k) , glue-square (e x) i k y })
      (incl (Sequence.map X x) , ua-unglue (e x) i y)

    flattenIso : Iso (Σ (SeqColim X) Family) (SeqColim Total)
    flattenIso = iso flatten total flatten-total total-flatten

    flattenEquiv : Σ (SeqColim X) Family ≃ SeqColim Total
    flattenEquiv = isoToEquiv flattenIso

    total-incl : {n : ℕ} (x : Sequence.obj X n) (y : Y n x)
      → total (incl (x , y)) ≡ (incl x , y)
    total-incl x y = refl

    total-push : {n : ℕ} (x : Sequence.obj X n) (y : Y n x)
      → cong total (push (x , y)) ≡ (λ i → push x i , ua-gluePt (e x) i y)
    total-push x y = refl

    family-push : {n : ℕ} (x : Sequence.obj X n)
      → cong Family (push x) ≡ ua (e x)
    family-push x = refl

    transport-push : {n : ℕ} (x : Sequence.obj X n) (y : Y n x)
      → subst Family (push x) y ≡ equivFun (e x) y
    transport-push x y = uaβ (e x) y

-- Port of Loc.SeqFlatten (no mathematical changes).
module SF where

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.Univalence
  open import Cubical.Data.Nat.Base using (ℕ ; zero ; suc)
  open import Cubical.Data.Sequence.Base
  open import Cubical.HITs.SequentialColimit.Base
  open import Cubical.HITs.SequentialColimit.Properties
    using (ShiftSeq ; Iso-SeqColim→SeqColimSuc)


  module Flatten {ℓx ℓp} (X : Sequence ℓx)
    (P : (n : ℕ) → Sequence.obj X n → Type ℓp)
    (g : {n : ℕ} (a : Sequence.obj X n) → P n a → P (suc n) (Sequence.map X a)) where

    private
      A = Sequence.obj X
      f = Sequence.map X
      ℓ = ℓ-max ℓx ℓp

    TailObj : (k : ℕ) {n : ℕ} → A n → Type ℓp
    TailObj zero {n} a = P n a
    TailObj (suc k) a = TailObj k (f a)

    tail-map : (k : ℕ) {n : ℕ} (a : A n) → TailObj k a → TailObj (suc k) a
    tail-map zero a = g a
    tail-map (suc k) a = tail-map k (f a)

    Tail : {n : ℕ} → A n → Sequence ℓp
    Sequence.obj (Tail a) k = TailObj k a
    Sequence.map (Tail a) {n = k} = tail-map k a

    stepEquiv : {n : ℕ} (a : A n) → SeqColim (Tail a) ≃ SeqColim (Tail (f a))
    stepEquiv a = isoToEquiv (Iso-SeqColim→SeqColimSuc (Tail a))

    step : {n : ℕ} (a : A n) → SeqColim (Tail a) → SeqColim (Tail (f a))
    step a = equivFun (stepEquiv a)

    Total : Sequence ℓ
    Sequence.obj Total n = Σ (A n) (P n)
    Sequence.map Total (a , p) = f a , g a p

    module EF = EquivFlatten.Flatten X (λ n a → SeqColim (Tail a)) stepEquiv

    Family : SeqColim X → Type ℓp
    Family = EF.Family

    private
      B = SeqColim Total
      D = SeqColim EF.Total

      ti : {n : ℕ} (a : A n) {k : ℕ} → TailObj k a → SeqColim (Tail a)
      ti a {k} p = incl {n = k} p

      tp : {n : ℕ} (a : A n) {k : ℕ} (p : TailObj k a)
        → ti a p ≡ ti a (tail-map k a p)
      tp a {k} p = push {n = k} p

      di : {n : ℕ} (a : A n) → SeqColim (Tail a) → D
      di {n} a z = incl {n = n} (a , z)

      dp : {n : ℕ} (a : A n) (z : SeqColim (Tail a))
        → di a z ≡ di (f a) (step a z)
      dp {n} a z = push {n = n} (a , z)

    lift-point : (k : ℕ) {n : ℕ} (a : A n) → TailObj k a → B
    lift-point zero {n} a p = incl {n = n} (a , p)
    lift-point (suc k) a p = lift-point k (f a) p

    lift-push : (k : ℕ) {n : ℕ} (a : A n) (p : TailObj k a)
      → lift-point k a p ≡ lift-point (suc k) a (tail-map k a p)
    lift-push zero {n} a p = push {n = n} (a , p)
    lift-push (suc k) a p = lift-push k (f a) p

    collapse-fibre : {n : ℕ} (a : A n) → SeqColim (Tail a) → B
    collapse-fibre a (incl {n = k} p) = lift-point k a p
    collapse-fibre a (push {n = k} p i) = lift-push k a p i

    collapse-step : {n : ℕ} (a : A n) (z : SeqColim (Tail a))
      → collapse-fibre a z ≡ collapse-fibre (f a) (step a z)
    collapse-step {n} a (incl {n = zero} p) = push {n = n} (a , p)
    collapse-step a (incl {n = suc k} p) = refl
    collapse-step {n} a (push {n = zero} p j) i = push {n = n} (a , p) (j ∨ i)
    collapse-step a (push {n = suc k} p j) = refl

    collapse : D → B
    collapse (incl (a , z)) = collapse-fibre a z
    collapse (push (a , z) i) = collapse-step a z i

    expand : B → D
    expand (incl (a , p)) = di a (ti a {zero} p)
    expand (push (a , p) i) = dp a (ti a {zero} p) i

    collapse-expand : (b : B) → collapse (expand b) ≡ b
    collapse-expand (incl (a , p)) = refl
    collapse-expand (push (a , p) i) = refl

    private
      E : D → Type ℓ
      E d = expand (collapse d) ≡ d

      point-return : (k : ℕ) {n : ℕ} (a : A n) (p : TailObj k a) → E (di a (ti a {k} p))
      point-return zero a p = refl
      point-return (suc k) a p = subst E (sym (dp a (ti a {suc k} p)))
        (point-return k (f a) p)

      next-return : (k : ℕ) {n : ℕ} (a : A n) (p : TailObj k a)
        → E (di (f a) (step a (ti a {k} p)))
      next-return zero a p = point-return zero (f a) (g a p)
      next-return (suc k) a p = point-return k (f a) p

      point-path : (k : ℕ) {n : ℕ} (a : A n) (p : TailObj k a)
        → PathP (λ i → E (dp a (ti a {k} p) i))
            (point-return k a p) (next-return k a p)
      point-path zero a p i = refl
      point-path (suc k) a p i =
        transport-filler (λ j → E (dp a (ti a {suc k} p) (~ j)))
          (point-return k (f a) p) (~ i)

      box-base : (k : ℕ) {n : ℕ} (a : A n) (p : TailObj k a) → I → I → D
      box-base k a p i j = dp a (tp a {k} p j) i

      Right : (k : ℕ) {n : ℕ} (a : A n) (p : TailObj k a) → Type ℓ
      Right k a p = PathP (λ j → E (box-base k a p i1 j))
        (next-return k a p) (next-return (suc k) a (tail-map k a p))

      box : (k : ℕ) {n : ℕ} (a : A n) (p : TailObj k a)
        → Right k a p → (i j : I) → E (box-base k a p i j)
      box k a p r i j = fill (λ h → E (box-base k a p (~ h) j))
        (λ h → λ { (j = i0) → point-path k a p (~ h)
                   ; (j = i1) → point-path (suc k) a (tail-map k a p) (~ h) })
        (inS (r j)) (~ i)

      inner-return : (k : ℕ) {n : ℕ} (a : A n) (p : TailObj k a)
        → PathP (λ j → E (di a (tp a {k} p j)))
            (point-return k a p) (point-return (suc k) a (tail-map k a p))
      inner-return zero a p j = box zero a p refl i0 j
      inner-return (suc k) a p j = box (suc k) a p (inner-return k (f a) p) i0 j

      fibre-return : {n : ℕ} (a : A n) (z : SeqColim (Tail a)) → E (di a z)
      fibre-return a (incl {n = k} p) = point-return k a p
      fibre-return a (push {n = k} p j) = inner-return k a p j

      outer-return : {n : ℕ} (a : A n) (z : SeqColim (Tail a))
        → PathP (λ i → E (dp a z i)) (fibre-return a z) (fibre-return (f a) (step a z))
      outer-return a (incl {n = zero} p) = point-path zero a p
      outer-return a (incl {n = suc k} p) = point-path (suc k) a p
      outer-return a (push {n = zero} p j) i = box zero a p refl i j
      outer-return a (push {n = suc k} p j) i = box (suc k) a p (inner-return k (f a) p) i j

    expand-collapse : (d : D) → expand (collapse d) ≡ d
    expand-collapse (incl (a , z)) = fibre-return a z
    expand-collapse (push (a , z) i) = outer-return a z i

    diagonalIso : Iso D B
    diagonalIso = iso collapse expand collapse-expand expand-collapse

    flattenIso : Iso (Σ (SeqColim X) Family) (SeqColim Total)
    flattenIso = compIso EF.flattenIso diagonalIso

    flattenEquiv : Σ (SeqColim X) Family ≃ SeqColim Total
    flattenEquiv = isoToEquiv flattenIso

    inclusion : {n : ℕ} (a : A n) → P n a → Family (incl a)
    inclusion a p = ti a {zero} p

    total : SeqColim Total → Σ (SeqColim X) Family
    total = Iso.inv flattenIso

    total-incl : {n : ℕ} (a : A n) (p : P n a)
      → total (incl (a , p)) ≡ (incl a , inclusion a p)
    total-incl a p = refl

    total-push : {n : ℕ} (a : A n) (p : P n a)
      → cong total (push (a , p))
        ≡ (λ i → push a i , ua-gluePt (stepEquiv a) i (inclusion a p))
    total-push a p = refl

    transport-inclusion : {n : ℕ} (a : A n) (p : P n a)
      → subst Family (push a) (inclusion a p) ≡ inclusion (f a) (g a p)
    transport-inclusion a p = uaβ (stepEquiv a) (inclusion a p)

    family-incl : {n : ℕ} (a : A n) → Family (incl a) ≡ SeqColim (Tail a)
    family-incl a = refl

    family-push : {n : ℕ} (a : A n) → cong Family (push a) ≡ ua (stepEquiv a)
    family-push a = refl

    transport-step : {n : ℕ} (a : A n) (z : SeqColim (Tail a))
      → subst Family (push a) z ≡ step a z
    transport-step a z = uaβ (stepEquiv a) z

    projection : SeqColim Total → SeqColim X
    projection (incl (a , p)) = incl a
    projection (push (a , p) i) = push a i

    total-projection : (z : SeqColim Total) → fst (total z) ≡ projection z
    total-projection (incl (a , p)) = refl
    total-projection (push (a , p) i) = refl

    flatten-incl : {n : ℕ} (a : A n) (p : P n a)
      → Iso.fun flattenIso (incl a , inclusion a p) ≡ incl (a , p)
    flatten-incl a p = refl

-- Port of Loc.ContinueTelescope (no mathematical changes).
module CT where

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.GroupoidLaws
  open import Cubical.Foundations.Path using (compPath→Square)
  open import Cubical.Data.Nat using (ℕ ; zero ; suc)
  open import Cubical.Data.Sequence
  open import Cubical.HITs.SequentialColimit.Base

  private
    slide : ∀ {ℓ} {A : Type ℓ} {x y z : A}
      (p : x ≡ y) (q : y ≡ z) → Square (sym p) (sym q) q p
    slide p q = compPath→Square (rCancel q ∙ sym (lCancel p))

  module Stationary {ℓ} (A : Type ℓ) (f : A → A) where
    diagram : Sequence ℓ
    Sequence.obj diagram _ = A
    Sequence.map diagram = f

    Telescope : Type ℓ
    Telescope = SeqColim diagram

    at : ℕ → A → Telescope
    at n a = incl {n = n} a

    transition : Telescope → Telescope
    transition (incl {n = n} a) = incl {n = n} (f a)
    transition (push {n = n} a i) = push {n = n} (f a) i

    shift : Telescope → Telescope
    shift (incl {n = n} a) = incl {n = suc n} a
    shift (push {n = n} a i) = push {n = suc n} a i

    transition-shift : (x : Telescope) → transition (shift x) ≡ x
    transition-shift (incl {n = n} a) = sym (push {n = n} a)
    transition-shift (push {n = n} a i) j =
      slide (push {n = n} a) (push {n = suc n} (f a)) i j

    shift-transition : (x : Telescope) → shift (transition x) ≡ x
    shift-transition (incl {n = n} a) = sym (push {n = n} a)
    shift-transition (push {n = n} a i) j =
      slide (push {n = n} a) (push {n = suc n} (f a)) i j

    transitionEquiv : Telescope ≃ Telescope
    transitionEquiv = isoToEquiv
      (iso transition shift transition-shift shift-transition)

    stage-zero : A → Telescope
    stage-zero = at zero

-- Port of Loc.ContinueLoopDiagram (no mathematical changes).
module LD where

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Pointed
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.GroupoidLaws
  open import Cubical.Data.Nat using (ℕ ; zero ; suc)
  open import Cubical.Data.Sequence
  open import Cubical.Data.Sigma using (ΣPathP)
  open import Cubical.Homotopy.Loopspace using (Ω ; Ω→ ; Ω→∘ ; isEquivΩ→)
  open import Cubical.HITs.SequentialColimit.Base
  open import Cubical.HITs.SequentialColimit.Properties using (sequenceEquiv→ColimIso)
  open CT using (module Stationary)

  module PointedDiagram {ℓ} (A : Pointed ℓ) (F : A →∙ A) where
    private
      f = fst F
      e = pt A
      u = snd F

    point : ℕ → typ A
    point zero = e
    point (suc n) = f (point n)

    to-base : (n : ℕ) → point n ≡ e
    to-base zero = refl
    to-base (suc n) = cong f (to-base n) ∙ u

    movingLoops : Sequence ℓ
    Sequence.obj movingLoops n = point n ≡ point n
    Sequence.map movingLoops = cong f

    module Target = Stationary (typ (Ω A)) (fst (Ω→ F))

    rebase∙ : (n : ℕ) → (typ A , point n) →∙ A
    rebase∙ n = (λ a → a) , to-base n

    step∙ : (n : ℕ) → (typ A , point n) →∙ (typ A , point (suc n))
    step∙ n = f , refl

    composition : (n : ℕ) → F ∘∙ rebase∙ n ≡ rebase∙ (suc n) ∘∙ step∙ n
    composition n = ΣPathP (refl , lUnit (to-base (suc n)))

    rebase-map : SequenceMap movingLoops Target.diagram
    SequenceMap.map rebase-map n = fst (Ω→ (rebase∙ n))
    SequenceMap.comm rebase-map n p =
      sym (Ω→∘ F (rebase∙ n) p)
      ∙ cong (λ h → fst (Ω→ h) p) (composition n)
      ∙ Ω→∘ (rebase∙ (suc n)) (step∙ n) p
      ∙ cong (fst (Ω→ (rebase∙ (suc n)))) (sym (rUnit (cong f p)))

    rebase-equiv : SequenceEquiv movingLoops Target.diagram
    fst rebase-equiv = rebase-map
    snd rebase-equiv n = isEquivΩ→ (rebase∙ n) (idIsEquiv (typ A))

    movingLoopIso : Iso (SeqColim movingLoops) Target.Telescope
    movingLoopIso = sequenceEquiv→ColimIso rebase-equiv

    at-zero : (p : e ≡ e)
      → Iso.fun movingLoopIso (incl {n = zero} p) ≡ Target.stage-zero p
    at-zero p = cong (incl {n = zero}) (sym (rUnit p))

-- Port of Loc.ContinueLoopColimit (no mathematical changes).
module LC where

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Pointed
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Equiv.Properties using (isEquivFromIsContr)
  open import Cubical.Foundations.Equiv.Fiberwise using (recognizeId)
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.HLevels using (isOfHLevelRetractFromIso)
  open import Cubical.Foundations.GroupoidLaws
  open import Cubical.Data.Nat using (ℕ ; zero ; suc ; _+_)
  open import Cubical.Data.Sequence
  open import Cubical.Homotopy.Loopspace using (Ω ; Ω→ ; isEquivΩ→)
  open import Cubical.HITs.SequentialColimit.Base
  open import Cubical.HITs.SequentialColimit.Properties
    using (converges→ColimIso ; sequenceEquiv→ColimIso)

  open CT using (module Stationary)
  open LD using (module PointedDiagram)

  module LoopColimit {ℓ} (A : Pointed ℓ) (F : A →∙ A) where
    private
      f = fst F
      e = pt A

    module Source = Stationary (typ A) f
    module Moving = PointedDiagram A F
    module Target = Moving.Target

    P : (n : ℕ) → typ A → Type ℓ
    P n a = Moving.point n ≡ a

    fibre-step : {n : ℕ} (a : typ A) → P n a → P (suc n) (f a)
    fibre-step a p = cong f p

    module Flat = SF.Flatten Source.diagram P (λ {n} a p → fibre-step {n} a p)

    private
      total-map-equiv : (n : ℕ) → isEquiv (Sequence.map Flat.Total {n = n})
      total-map-equiv n = isEquivFromIsContr (Sequence.map Flat.Total {n = n})
        (isContrSingl (Moving.point n)) (isContrSingl (Moving.point (suc n)))

      total-sequence-contr : isContr (SeqColim Flat.Total)
      total-sequence-contr = isOfHLevelRetractFromIso 0
        (invIso (converges→ColimIso {seq = Flat.Total} zero
          (λ k → total-map-equiv (k + zero))))
        (isContrSingl e)

      code-total-contr : isContr (Σ Source.Telescope Flat.Family)
      code-total-contr = isOfHLevelRetractFromIso 0
        (equivToIso Flat.flattenEquiv) total-sequence-contr

    path-code : (x : Source.Telescope)
      → (Source.stage-zero e ≡ x) ≃ Flat.Family x
    path-code = recognizeId Flat.Family (Flat.inclusion {n = zero} e refl) code-total-contr

    encode-inclusion : {a : typ A} (p : e ≡ a)
      → fst (path-code (Source.stage-zero a)) (cong Source.stage-zero p)
        ≡ Flat.inclusion {n = zero} a p
    encode-inclusion = J
      (λ a p → fst (path-code (Source.stage-zero a)) (cong Source.stage-zero p)
        ≡ Flat.inclusion {n = zero} a p)
      (JRefl {x = Source.stage-zero e}
        (λ x p → Flat.Family x) (Flat.inclusion {n = zero} e refl))

    tail-rebase : (k n : ℕ)
      → Flat.TailObj k {n} (Moving.point n) ≃ typ (Ω A)
    tail-rebase zero n = fst (Ω→ (Moving.rebase∙ n)) ,
      isEquivΩ→ (Moving.rebase∙ n) (idIsEquiv (typ A))
    tail-rebase (suc k) n = tail-rebase k (suc n)

    tail-comm : (k n : ℕ) (p : Flat.TailObj k {n} (Moving.point n))
      → fst (Ω→ F) (fst (tail-rebase k n) p)
        ≡ fst (tail-rebase (suc k) n) (Flat.tail-map k (Moving.point n) p)
    tail-comm zero n p = SequenceMap.comm Moving.rebase-map n p
    tail-comm (suc k) n p = tail-comm k (suc n) p

    tail-map : SequenceMap (Flat.Tail {zero} e) Target.diagram
    SequenceMap.map tail-map k = fst (tail-rebase k zero)
    SequenceMap.comm tail-map k = tail-comm k zero

    tail-equiv : SequenceEquiv (Flat.Tail {zero} e) Target.diagram
    fst tail-equiv = tail-map
    snd tail-equiv k = snd (tail-rebase k zero)

    tailIso : Iso (Flat.Family (Source.stage-zero e)) Target.Telescope
    tailIso = sequenceEquiv→ColimIso tail-equiv

    tail-at-zero : (p : e ≡ e)
      → Iso.fun tailIso (Flat.inclusion {n = zero} e p) ≡ Target.stage-zero p
    tail-at-zero p = cong (incl {n = zero}) (sym (rUnit p))

    loop-colimit : (Source.stage-zero e ≡ Source.stage-zero e) ≃ Target.Telescope
    loop-colimit = compEquiv (path-code (Source.stage-zero e)) (isoToEquiv tailIso)

    loop-colimit-base : fst loop-colimit refl ≡ Target.stage-zero refl
    loop-colimit-base = cong (Iso.fun tailIso) (encode-inclusion refl) ∙ tail-at-zero refl

    loop-colimit∙ : Ω (Source.Telescope , Source.stage-zero e)
      ≃∙ (Target.Telescope , Target.stage-zero refl)
    loop-colimit∙ = loop-colimit , loop-colimit-base

    stage-zero∙ : A →∙ (Source.Telescope , Source.stage-zero e)
    stage-zero∙ = Source.stage-zero , refl

    canonical-stage-zero : (p : e ≡ e)
      → fst loop-colimit (fst (Ω→ stage-zero∙) p) ≡ Target.stage-zero p
    canonical-stage-zero p = cong (fst loop-colimit)
        (sym (rUnit (cong Source.stage-zero p)))
      ∙ cong (Iso.fun tailIso) (encode-inclusion p)
      ∙ tail-at-zero p

-- Port of Loc.LoopColimitStageCode (no mathematical changes).
module Code where

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Pointed
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.Isomorphism
  open import Cubical.Foundations.GroupoidLaws
  open import Cubical.Foundations.Transport using (substComposite ; subst⁻Subst)
  open import Cubical.Data.Nat.Base using (ℕ ; zero ; suc)
  open import Cubical.HITs.SequentialColimit.Base using (incl ; push)


  private
    undo-transport : ∀ {ℓ ℓp} {A : Type ℓ} (P : A → Type ℓp)
      {a b : A} (p : a ≡ b) {x : P a} {y : P b}
      → subst P p x ≡ y → subst P (sym p) y ≡ x
    undo-transport P p {x} h = cong (subst P (sym p)) (sym h)
      ∙ subst⁻Subst P p x

  module Stages {ℓ} (A : Pointed ℓ) (F : A →∙ A) where
    module L = LC.LoopColimit A F
    module S = L.Source
    module M = L.Moving
    module Flat = L.Flat
    module T = L.Target

    private
      f = fst F
      e = pt A
      start = S.stage-zero e
      seed = Flat.inclusion {n = zero} e refl

    advance : (n : ℕ) → start ≡ S.at n (M.point n)
    advance zero = refl
    advance (suc n) = advance n ∙ push {n = n} (M.point n)

    advance-code : (n : ℕ)
      → subst Flat.Family (advance n) seed
        ≡ Flat.inclusion {n = n} (M.point n) refl
    advance-code zero = transportRefl seed
    advance-code (suc n) = substComposite Flat.Family (advance n)
        (push {n = n} (M.point n)) seed
      ∙ cong (subst Flat.Family (push {n = n} (M.point n))) (advance-code n)
      ∙ Flat.transport-inclusion {n = n} (M.point n) refl

    at-code : (n : ℕ) {a : typ A} (p : M.point n ≡ a)
      → fst (L.path-code (S.at n a)) (advance n ∙ cong (S.at n) p)
        ≡ Flat.inclusion {n = n} a p
    at-code n p = substComposite Flat.Family (advance n) (cong (S.at n) p) seed
      ∙ cong (subst Flat.Family (cong (S.at n) p)) (advance-code n)
      ∙ fromPathP (λ i → Flat.inclusion {n = n} (p i) (λ j → p (i ∧ j)))

    decode-word : (k : ℕ) {n : ℕ} (a : typ A)
      → Flat.TailObj k {n} a → start ≡ S.at n a
    decode-word zero {n} a p = advance n ∙ cong (S.at n) p
    decode-word (suc k) {n} a p = decode-word k {suc n} (f a) p
      ∙ sym (push {n = n} a)

    encode-word : (k : ℕ) {n : ℕ} (a : typ A) (p : Flat.TailObj k {n} a)
      → fst (L.path-code (S.at n a)) (decode-word k {n} a p)
        ≡ incl {n = k} p
    encode-word zero {n} a p = at-code n p
    encode-word (suc k) {n} a p = substComposite Flat.Family
        (decode-word k {suc n} (f a) p) (sym (push {n = n} a)) seed
      ∙ cong (subst Flat.Family (sym (push {n = n} a)))
          (encode-word k {suc n} (f a) p)
      ∙ undo-transport Flat.Family (push {n = n} a)
          (Flat.transport-step {n = n} a (incl {n = suc k} p))

    loop-word : (k : ℕ) → Flat.TailObj k {zero} e → start ≡ start
    loop-word k = decode-word k {zero} e

    loop-code : (k : ℕ) (p : Flat.TailObj k {zero} e)
      → fst L.loop-colimit (loop-word k p)
        ≡ T.at k (fst (L.tail-rebase k zero) p)
    loop-code k p = cong (Iso.fun L.tailIso) (encode-word k {zero} e p)

    decode-generator : (k : ℕ) (p : Flat.TailObj k {zero} e)
      → invEq L.loop-colimit (T.at k (fst (L.tail-rebase k zero) p))
        ≡ loop-word k p
    decode-generator k p = cong (invEq L.loop-colimit) (sym (loop-code k p))
      ∙ retEq L.loop-colimit (loop-word k p)

-- Port of Loc.LoopColimitStages (no mathematical changes).
module Stages where

  open import Cubical.Foundations.Prelude
  open import Cubical.Foundations.Pointed
  open import Cubical.Foundations.Equiv
  open import Cubical.Foundations.GroupoidLaws
  open import Cubical.Foundations.Function using (idfun)
  open import Cubical.Data.Sigma using (ΣPathP)
  open import Cubical.Data.Nat.Base using (ℕ ; zero ; suc ; _+_)
  open import Cubical.Data.Nat.Properties using (+-zero ; +-suc)
  open import Cubical.Homotopy.Loopspace using (Ω ; Ω→ ; Ω→∘)
  open import Cubical.HITs.SequentialColimit.Base using (push)


  private
    cancel-pointing : ∀ {ℓ} {X : Type ℓ} {a b c : X}
      (p : a ≡ b) (q : b ≡ c) → q ∙ sym (p ∙ q) ≡ sym p
    cancel-pointing p q = cong (q ∙_) (symDistr p q)
      ∙ assoc q (sym q) (sym p)
      ∙ cong (_∙ sym p) (rCancel q) ∙ sym (lUnit (sym p))

    rebase-word : ∀ {ℓ ℓ'} {A : Type ℓ} {B : Type ℓ'}
      {a e : A} {b : B} (f : A → B) (v : b ≡ f a) (u : a ≡ e) (p : a ≡ a)
      → (v ∙ cong f p) ∙ sym v
        ≡ fst (Ω→ {A = A , e} {B = B , b} (f , sym (v ∙ cong f u)))
            (fst (Ω→ {A = A , a} {B = A , e} (idfun A , u)) p)
    rebase-word {A = A} {B = B} {a} {e} {b} f v u p =
        sym (assoc v (cong f p) (sym v))
      ∙ sym (doubleCompPath≡compPath v (cong f p) (sym v))
      ∙ sym (cong (λ h → fst (Ω→ h) p) normalize)
      ∙ Ω→∘ outer inner p
      where
      outer : (A , e) →∙ (B , b)
      outer = f , sym (v ∙ cong f u)
      inner : (A , a) →∙ (A , e)
      inner = idfun A , u
      direct : (A , a) →∙ (B , b)
      direct = f , sym v
      normalize : outer ∘∙ inner ≡ direct
      normalize = ΣPathP (refl , cancel-pointing v (cong f u))

  module AllStages {ℓ} (A : Pointed ℓ) (F : A →∙ A) where
    module C = Code.Stages A F
    module L = C.L
    module S = C.S
    module M = C.M
    module Flat = C.Flat
    module T = C.T

    private
      e = pt A
      start = S.stage-zero e
      Tel∙ : Pointed ℓ
      Tel∙ = S.Telescope , start

    stage-at : (k n : ℕ) → A →∙ Tel∙
    stage-at zero n = S.at n , sym (C.advance n ∙ cong (S.at n) (M.to-base n))
    stage-at (suc k) n = stage-at k (suc n)

    stage : (k : ℕ) → A →∙ Tel∙
    stage k = stage-at k zero

    closed-word : (k n : ℕ) → Flat.TailObj k {n} (M.point n) → start ≡ start
    closed-word k n p = C.decode-word k {n} (M.point n) p ∙ sym (C.advance n)

    private
      close-step : (k n : ℕ) (p : Flat.TailObj (suc k) {n} (M.point n))
        → closed-word (suc k) n p ≡ closed-word k (suc n) p
      close-step k n p = sym (assoc d (sym s) (sym (C.advance n)))
        ∙ cong (d ∙_) (sym (symDistr (C.advance n) s))
        where
        d = C.decode-word k {suc n} (M.point (suc n)) p
        s = push {n = n} (M.point n)

    closed-as-stage : (k n : ℕ) (p : Flat.TailObj k {n} (M.point n))
      → closed-word k n p
        ≡ fst (Ω→ (stage-at k n)) (fst (L.tail-rebase k n) p)
    closed-as-stage zero n p = rebase-word (S.at n) (C.advance n) (M.to-base n) p
    closed-as-stage (suc k) n p = close-step k n p ∙ closed-as-stage k (suc n) p

    private
      from-tail : (k : ℕ) (p : Flat.TailObj k {zero} e)
        → invEq L.loop-colimit (T.at k (fst (L.tail-rebase k zero) p))
          ≡ fst (Ω→ (stage k)) (fst (L.tail-rebase k zero) p)
      from-tail k p = C.decode-generator k p ∙ rUnit (C.loop-word k p)
        ∙ closed-as-stage k zero p

    decoded-stage : (k : ℕ) (p : typ (Ω A))
      → invEq L.loop-colimit (T.at k p) ≡ fst (Ω→ (stage k)) p
    decoded-stage k p = cong (λ q → invEq L.loop-colimit (T.at k q)) (sym beta)
      ∙ from-tail k q ∙ cong (fst (Ω→ (stage k))) beta
      where
      q : Flat.TailObj k {zero} e
      q = invEq (L.tail-rebase k zero) p
      beta : fst (L.tail-rebase k zero) q ≡ p
      beta = secEq (L.tail-rebase k zero) p

    canonical-stage : (k : ℕ) (p : typ (Ω A))
      → fst L.loop-colimit (fst (Ω→ (stage k)) p) ≡ T.at k p
    canonical-stage k p = cong (fst L.loop-colimit) (sym (decoded-stage k p))
      ∙ secEq L.loop-colimit (T.at k p)

    stage-at-function : (k n : ℕ) → fst (stage-at k n) ≡ S.at (k + n)
    stage-at-function zero n = refl
    stage-at-function (suc k) n = stage-at-function k (suc n)
      ∙ cong S.at (+-suc k n)

    stage-function : (k : ℕ) → fst (stage k) ≡ S.at k
    stage-function k = stage-at-function k zero ∙ cong S.at (+-zero k)

-- The actual pullback sequence, including both transition squares.
PB : ∀ {ℓa ℓb ℓc} {A : Type ℓa} {B : Type ℓb} {C : Type ℓc}
  → (A → C) → (B → C) → Type (ℓ-max ℓa (ℓ-max ℓb ℓc))
PB {A = A} {B = B} f g = Σ[ a ∈ A ] Σ[ b ∈ B ] f a ≡ g b

module PullbackSequence {ℓa ℓb ℓc}
  {A : Sequence ℓa} {B : Sequence ℓb} {C : Sequence ℓc}
  (f : SequenceMap A C) (g : SequenceMap B C) where

  private
    fa = SequenceMap.map f
    gb = SequenceMap.map g
    cf = SequenceMap.comm f
    cg = SequenceMap.comm g

  PBSequence : Sequence (ℓ-max ℓa (ℓ-max ℓb ℓc))
  Sequence.obj PBSequence n = PB (fa n) (gb n)
  Sequence.map PBSequence {n} (a , b , p) =
    Sequence.map A a , Sequence.map B b ,
    (sym (cf n a) ∙∙ cong (Sequence.map C) p ∙∙ cg n b)

  -- The square is the horizontal pasting of the naturality square for push
  -- and the filler of the double composition in the stagewise pullback.
  comparison-square : (n : ℕ) (a : Sequence.obj A n)
    (b : Sequence.obj B n) (p : fa n a ≡ gb n b)
    → PathP (λ i → realiseSequenceMap f (push a i)
                   ≡ realiseSequenceMap g (push b i))
        (cong (incl {n = n}) p)
        (cong (incl {n = suc n})
          (sym (cf n a) ∙∙ cong (Sequence.map C) p ∙∙ cg n b))
  comparison-square n a b p i j =
    (push (p j) ∙ (λ k → incl
      (doubleCompPath-filler (sym (cf n a))
        (cong (Sequence.map C) p) (cg n b) k j))) i

  seq-pullback-comparison : SeqColim PBSequence
    → PB (realiseSequenceMap f) (realiseSequenceMap g)
  seq-pullback-comparison (incl (a , b , p)) = incl a , incl b , cong incl p
  seq-pullback-comparison (push {n} (a , b , p) i) =
    push a i , push b i , comparison-square n a b p i

  seq-pullback-stage : (n : ℕ) (a : Sequence.obj A n)
    (b : Sequence.obj B n) (p : fa n a ≡ gb n b)
    → seq-pullback-comparison (incl {n = n} (a , b , p))
      ≡ (incl a , incl b , cong incl p)
  seq-pullback-stage n a b p = refl

open PullbackSequence public
  using (PBSequence ; seq-pullback-comparison ; seq-pullback-stage)

-- A pointed sequence has genuinely pointed transition maps.
record PointedSequence (ℓ : Level) : Type (ℓ-suc ℓ) where
  field
    obj∙ : ℕ → Pointed ℓ
    map∙ : (n : ℕ) → obj∙ n →∙ obj∙ (suc n)

underlyingSequence : ∀ {ℓ} → PointedSequence ℓ → Sequence ℓ
Sequence.obj (underlyingSequence D) n = typ (PointedSequence.obj∙ D n)
Sequence.map (underlyingSequence D) {n} = fst (PointedSequence.map∙ D n)

SeqColim∙ : ∀ {ℓ} → PointedSequence ℓ → Pointed ℓ
SeqColim∙ D = SeqColim (underlyingSequence D) ,
  incl {n = zero} (pt (PointedSequence.obj∙ D zero))

loopSequence : ∀ {ℓ} → PointedSequence ℓ → PointedSequence ℓ
PointedSequence.obj∙ (loopSequence D) n = Ω (PointedSequence.obj∙ D n)
PointedSequence.map∙ (loopSequence D) n = Ω→ (PointedSequence.map∙ D n)

module PointedStages {ℓ} (D : PointedSequence ℓ) where
  private
    A = PointedSequence.obj∙ D
    F = PointedSequence.map∙ D

  -- The moving point follows the maps strictly; to-base accounts for every
  -- transition's pointing.  This is the convention of the stationary port.
  point : (n : ℕ) → typ (A n)
  point zero = pt (A zero)
  point (suc n) = fst (F n) (point n)

  to-base : (n : ℕ) → point n ≡ pt (A n)
  to-base zero = refl
  to-base (suc n) = cong (fst (F n)) (to-base n) ∙ snd (F n)

  advance : (n : ℕ) → pt (SeqColim∙ D) ≡ incl {n = n} (point n)
  advance zero = refl
  advance (suc n) = advance n ∙ push {n = n} (point n)

  stage∙ : (n : ℕ) → A n →∙ SeqColim∙ D
  stage∙ n = incl {n = n} , sym (advance n ∙ cong incl (to-base n))

open PointedStages public using (stage∙)

Stationary∙ : ∀ {ℓ} (A : Pointed ℓ) → (A →∙ A) → PointedSequence ℓ
PointedSequence.obj∙ (Stationary∙ A F) _ = A
PointedSequence.map∙ (Stationary∙ A F) _ = F

-- The cumulative product includes R k.  No positivity is imposed.
Conn : ∀ {ℓ} → Type ℓ → Type ℓ
Conn = isConnected 2

SC : ∀ {ℓ} → Type ℓ → Type ℓ
SC = isConnected 3

DegreeFamily : (ℕ → ℕ) → ℕ → S¹ → S¹
DegreeFamily R i = deg₁ (R i)

L : ∀ {ℓ} → (ℕ → ℕ) → Type ℓ → Type ℓ
L R X = Localization.Localize (DegreeFamily R) X

η : ∀ {ℓ} (R : ℕ → ℕ) {X : Type ℓ} → X → L R X
η R = Localization.∣_∣

pow : ∀ {ℓ} → ℕ → (X : Pointed ℓ) → typ (Ω X) → typ (Ω X)
pow m X = powLoop m

pow-refl : ∀ {ℓ} (m : ℕ) (X : Pointed ℓ) → pow m X refl ≡ refl
pow-refl zero X = refl
pow-refl (suc m) X = cong (refl ∙_) (pow-refl m X) ∙ sym (lUnit refl)

pow∙ : ∀ {ℓ} → ℕ → (X : Pointed ℓ) → Ω X →∙ Ω X
pow∙ m X = pow m X , pow-refl m X

cumulative-product : (ℕ → ℕ) → ℕ → ℕ
cumulative-product R zero = R zero
cumulative-product R (suc k) = cumulative-product R k · R (suc k)

PowerSeq∙ : ∀ {ℓ} → (ℕ → ℕ) → Pointed ℓ → PointedSequence ℓ
PointedSequence.obj∙ (PowerSeq∙ R X) _ = Ω X
PointedSequence.map∙ (PowerSeq∙ R X) k = pow∙ (cumulative-product R k) X

PowerSeq : ∀ {ℓ} → (ℕ → ℕ) → Pointed ℓ → Sequence ℓ
PowerSeq R X = underlyingSequence (PowerSeq∙ R X)

i₀ : ∀ {ℓ} (R : ℕ → ℕ) (X : Pointed ℓ)
  → typ (Ω X) → SeqColim (PowerSeq R X)
i₀ R X = incl {n = zero}

StationaryPowerSeq : ∀ {ℓ} → ℕ → Pointed ℓ → Sequence ℓ
StationaryPowerSeq m X = CT.Stationary.diagram (typ (Ω X)) (pow m X)

stationary-i₀ : ∀ {ℓ} (m : ℕ) (X : Pointed ℓ)
  → typ (Ω X) → SeqColim (StationaryPowerSeq m X)
stationary-i₀ m X = incl {n = zero}

-- This inverts the induced transition on the telescope, not the power map
-- on its loop spaces; it does not assert locality of the telescope.
stationary-power-transition-equiv : ∀ {ℓ} (m : ℕ) (X : Pointed ℓ)
  → SeqColim (StationaryPowerSeq m X) ≃ SeqColim (StationaryPowerSeq m X)
stationary-power-transition-equiv m X =
  CT.Stationary.transitionEquiv (typ (Ω X)) (pow m X)

-- Generic pointed path algebra for the all-stage comparison.  Keeping this
-- separate avoids normalizing the flattened identity-code proof inside it.
module PointStage {ℓ} {X Y Z : Pointed ℓ} (e : Y ≃∙ Z)
  (f : X →∙ Y) (g : typ X → typ Z)
  (h : (x : typ X) → fst (≃∙map e ∘∙ f) x ≡ g x) where

  stage : X →∙ Z
  stage = g , sym (h (pt X)) ∙ snd (≃∙map e ∘∙ f)

  stage-path : ≃∙map e ∘∙ f ≡ stage
  stage-path = ΣPathP (funExt h ,
    compPath-filler' (sym (h (pt X))) (snd (≃∙map e ∘∙ f)))

  inverse-stage : ≃∙map (invEquiv∙ e) ∘∙ stage ≡ f
  inverse-stage =
    cong (≃∙map (invEquiv∙ e) ∘∙_) (sym stage-path)
    ∙ sym (∘∙-assoc (≃∙map (invEquiv∙ e)) (≃∙map e) f)
    ∙ cong (_∘∙ f) (fst (≃∙→ret/sec∙ e))
    ∙ ∘∙-idʳ f

-- Stationary loop comparison. The loop-stage pointing is induced by the
-- all-stage homotopy.
module StationaryLoops {ℓ} (A : Pointed ℓ) (F : A →∙ A) where
  module St = Stages.AllStages A F
  module Loops = St.L

  source∙ : Pointed ℓ
  source∙ = SeqColim∙ (Stationary∙ A F)

  target∙ : Pointed ℓ
  target∙ = SeqColim∙ (loopSequence (Stationary∙ A F))

  stage-stationary∙ : (k : ℕ) → A →∙ source∙
  stage-stationary∙ = St.stage

  stage-stationary-is-inclusion : (k : ℕ)
    → fst (stage-stationary∙ k) ≡ incl {n = k}
  stage-stationary-is-inclusion = St.stage-function

  -- This abstraction is only a conversion boundary, not an assumption.
  abstract
    forwardEquiv : Ω source∙ ≃∙ target∙
    forwardEquiv = Loops.loop-colimit∙

    canonical-stage : (k : ℕ) (p : typ (Ω A))
      → fst (≃∙map forwardEquiv ∘∙ Ω→ (stage-stationary∙ k)) p
        ≡ Loops.Target.at k p
    canonical-stage = St.canonical-stage

  seq-loops-stationary : target∙ ≃∙ Ω source∙
  seq-loops-stationary = invEquiv∙ forwardEquiv

  module At (k : ℕ) = PointStage forwardEquiv
    (Ω→ (stage-stationary∙ k)) (Loops.Target.at k) (canonical-stage k)

  loopStage : (k : ℕ) → Ω A →∙ target∙
  loopStage k = At.stage k

  loopStage-is-inclusion : (k : ℕ)
    → fst (loopStage k) ≡ incl {n = k}
  loopStage-is-inclusion k = refl

  seq-loops-stage-stationary : (k : ℕ)
    → ≃∙map seq-loops-stationary ∘∙ loopStage k
      ≡ Ω→ (stage-stationary∙ k)
  seq-loops-stage-stationary k = At.inverse-stage k

open StationaryLoops public
  using (seq-loops-stationary ; stage-stationary∙ ;
         stage-stationary-is-inclusion ; seq-loops-stage-stationary)

-- Uniqueness WITH the actual unit.  Generators are small;
-- X, Y, and test objects may lie in any one common universe.
module LocalizationUnit {ℓ} {I : Type} {S T : I → Type}
  {F : (i : I) → S i → T i} {X Y : Type ℓ}
  (u : X → Y) (localY : Localization.isLocal F Y)
  (UP : (Z : Type ℓ) → Localization.isLocal F Z
    → isEquiv (λ (h : Y → Z) → h ∘ u)) where

  open import Cubical.Foundations.Equiv.Properties using (isEquivCong)

  LX : Type ℓ
  LX = Localization.Localize F X

  localLX : Localization.isLocal F LX
  localLX = Localization.isLocal-Localize F X

  comparison : LX → Y
  comparison = Localization.rec localY u

  restriction : (Z : Type ℓ) → Localization.isLocal F Z
    → (Y → Z) ≃ (X → Z)
  restriction Z lZ = (λ h → h ∘ u) , UP Z lZ

  inverse : Y → LX
  inverse = invEq (restriction LX localLX) Localization.∣_∣

  inverse-unit : inverse ∘ u ≡ Localization.∣_∣
  inverse-unit = secEq (restriction LX localLX) Localization.∣_∣

  comparison-inverse : comparison ∘ inverse ≡ idfun Y
  comparison-inverse = invEq
    (_ , isEquivCong (restriction Y localY))
    (cong (comparison ∘_) inverse-unit)

  inverse-comparison : inverse ∘ comparison ≡ idfun LX
  inverse-comparison = Unique.unique localLX
    (inverse ∘ comparison) (idfun LX) (funExt⁻ inverse-unit)

  equivalence : LX ≃ Y
  equivalence = isoToEquiv (iso comparison inverse
    (funExt⁻ comparison-inverse) (funExt⁻ inverse-comparison))

  unit-β : equivFun equivalence ∘ Localization.∣_∣ ≡ u
  unit-β = refl

localization-unique : ∀ {ℓ} {I : Type} {S T : I → Type}
  {F : (i : I) → S i → T i} {X Y : Type ℓ}
  (u : X → Y) → Localization.isLocal F Y
  → ((Z : Type ℓ) → Localization.isLocal F Z
      → isEquiv (λ (h : Y → Z) → h ∘ u))
  → Σ[ e ∈ Localization.Localize F X ≃ Y ]
      (equivFun e ∘ Localization.∣_∣ ≡ u)
localization-unique u lY UP = LocalizationUnit.equivalence u lY UP , refl

-- Locality and the universal property of the initial inclusion determine
-- the comparison equivalence and its unit law.
module PowerUnit {ℓ} (R : ℕ → ℕ) (X : Pointed ℓ)
  (localTel : Localization.isLocal (DegreeFamily R) (SeqColim (PowerSeq R X)))
  (telescopeUP : (Y : Type ℓ) → Localization.isLocal (DegreeFamily R) Y
    → isEquiv (λ (h : SeqColim (PowerSeq R X) → Y) → h ∘ i₀ R X)) where

  module UnitProof = LocalizationUnit (i₀ R X) localTel telescopeUP

  power-telescope-equiv-from-UP : L R (typ (Ω X)) ≃ SeqColim (PowerSeq R X)
  power-telescope-equiv-from-UP = UnitProof.equivalence

  power-telescope-β-from-UP :
    equivFun power-telescope-equiv-from-UP ∘ η R ≡ i₀ R X
  power-telescope-β-from-UP = refl

open PowerUnit public
  using (power-telescope-equiv-from-UP ; power-telescope-β-from-UP)

-- The identity-code portion of the same flattening proof works for
-- an arbitrary pointed sequence.  No stationary or equivalence hypothesis
-- is made on its transition maps.  Tail indices remain recursive.
module SequencePathCode {ℓ} (D : PointedSequence ℓ) where
  open import Cubical.Foundations.Equiv.Properties using (isEquivFromIsContr)
  open import Cubical.Foundations.Equiv.Fiberwise using (recognizeId)
  open import Cubical.Foundations.HLevels using (isOfHLevelRetractFromIso)
  open import Cubical.Foundations.Transport using (substComposite ; subst⁻Subst)
  open import Cubical.HITs.SequentialColimit.Properties using (converges→ColimIso)
  open import Cubical.Data.Nat using (_+_)

  module Moving = PointedStages D

  private
    A = PointedSequence.obj∙ D
    F = PointedSequence.map∙ D
    basepoint = pt (SeqColim∙ D)

  P : (n : ℕ) → typ (A n) → Type ℓ
  P n a = Moving.point n ≡ a

  fibre-step : {n : ℕ} (a : typ (A n)) → P n a
    → P (suc n) (fst (F n) a)
  fibre-step {n} a = cong (fst (F n))

  module Flat = SF.Flatten (underlyingSequence D) P fibre-step

  private
    total-map-equiv : (n : ℕ) → isEquiv (Sequence.map Flat.Total {n = n})
    total-map-equiv n = isEquivFromIsContr (Sequence.map Flat.Total {n = n})
      (isContrSingl (Moving.point n)) (isContrSingl (Moving.point (suc n)))

    total-sequence-contr : isContr (SeqColim Flat.Total)
    total-sequence-contr = isOfHLevelRetractFromIso 0
      (invIso (converges→ColimIso {seq = Flat.Total} zero
        (λ k → total-map-equiv (k + zero))))
      (isContrSingl (pt (A zero)))

    code-total-contr : isContr (Σ (typ (SeqColim∙ D)) Flat.Family)
    code-total-contr = isOfHLevelRetractFromIso 0
      (equivToIso Flat.flattenEquiv) total-sequence-contr

    seed : Flat.Family basepoint
    seed = Flat.inclusion {n = zero} (pt (A zero)) refl

  seq-path-code : (x : typ (SeqColim∙ D)) → (basepoint ≡ x) ≃ Flat.Family x
  seq-path-code = recognizeId Flat.Family seed code-total-contr

  advance-code : (n : ℕ)
    → subst Flat.Family (Moving.advance n) seed
      ≡ Flat.inclusion {n = n} (Moving.point n) refl
  advance-code zero = transportRefl seed
  advance-code (suc n) = substComposite Flat.Family (Moving.advance n)
      (push {n = n} (Moving.point n)) seed
    ∙ cong (subst Flat.Family (push {n = n} (Moving.point n))) (advance-code n)
    ∙ Flat.transport-inclusion {n = n} (Moving.point n) refl

  seq-path-code-stage : (n : ℕ) {a : typ (A n)} (p : Moving.point n ≡ a)
    → fst (seq-path-code (incl {n = n} a))
        (Moving.advance n ∙ cong (incl {n = n}) p)
      ≡ Flat.inclusion {n = n} a p
  seq-path-code-stage n p =
    substComposite Flat.Family (Moving.advance n) (cong (incl {n = n}) p) seed
    ∙ cong (subst Flat.Family (cong (incl {n = n}) p)) (advance-code n)
    ∙ fromPathP (λ i → Flat.inclusion {n = n} (p i) (λ j → p (i ∧ j)))

  decode-word : (k : ℕ) {n : ℕ} (a : typ (A n))
    → Flat.TailObj k {n} a → basepoint ≡ incl {n = n} a
  decode-word zero {n} a p = Moving.advance n ∙ cong (incl {n = n}) p
  decode-word (suc k) {n} a p = decode-word k {suc n} (fst (F n) a) p
    ∙ sym (push {n = n} a)

  encode-word : (k : ℕ) {n : ℕ} (a : typ (A n)) (p : Flat.TailObj k {n} a)
    → fst (seq-path-code (incl {n = n} a)) (decode-word k {n} a p)
      ≡ incl {n = k} p
  encode-word zero {n} a p = seq-path-code-stage n p
  encode-word (suc k) {n} a p = substComposite Flat.Family
      (decode-word k {suc n} (fst (F n) a) p) (sym (push {n = n} a)) seed
    ∙ cong (subst Flat.Family (sym (push {n = n} a)))
        (encode-word k {suc n} (fst (F n) a) p)
    ∙ cong (subst Flat.Family (sym (push {n = n} a)))
        (sym (Flat.transport-step {n = n} a (incl {n = suc k} p)))
    ∙ subst⁻Subst Flat.Family (push {n = n} a) (incl {n = suc k} p)

  decode-generator : (k : ℕ) {n : ℕ} (a : typ (A n)) (p : Flat.TailObj k {n} a)
    → invEq (seq-path-code (incl {n = n} a)) (incl {n = k} p)
      ≡ decode-word k {n} a p
  decode-generator k {n} a p =
    cong (invEq (seq-path-code (incl {n = n} a))) (sym (encode-word k {n} a p))
    ∙ retEq (seq-path-code (incl {n = n} a)) (decode-word k {n} a p)

-- Compare the constant ℕ-indexed family with the existing Unit-indexed
-- single-map convention, rather than silently identifying the two HITs.
module ConstantFamily where
  open import Cubical.Data.Unit using (Unit ; tt)
  open import Cubical.Foundations.Equiv.PathSplit using (isPropIsPathSplitEquiv)
  import DeloopS3.Local.Base as Single

  constant-family-locality : ∀ {ℓ} (m : ℕ) (X : Type ℓ)
    → Localization.isLocal (Single.F m) X
      ≃ Localization.isLocal (DegreeFamily (λ _ → m)) X
  constant-family-locality m X = isoToEquiv
    (iso (λ h _ → h tt) (λ h _ → h zero)
      (λ h → funExt λ n → isPropIsPathSplitEquiv
        (λ (g : S¹ → X) → g ∘ deg₁ m) (h zero) (h n))
      (λ h → funExt λ n → isPropIsPathSplitEquiv
        (λ (g : S¹ → X) → g ∘ deg₁ m) (h tt) (h n)))

  Lm : ∀ {ℓ} → ℕ → Type ℓ → Type ℓ
  Lm m X = L (λ _ → m) X

  module _ {ℓ} (m : ℕ) (X : Type ℓ) where
    private
      localTarget : Localization.isLocal (Single.F m) (Lm m X)
      localTarget = invEq (constant-family-locality m (Lm m X))
        (Localization.isLocal-Localize (DegreeFamily (λ _ → m)) X)

      module Identification = LocalizationUnit (η (λ _ → m) {X = X})
        localTarget (λ Z lZ → Unique.isEquiv-preη
          (equivFun (constant-family-locality m Z) lZ))

    constant-family-localization-equiv :
      Localization.Localize (Single.F m) X ≃ Lm m X
    constant-family-localization-equiv = Identification.equivalence

    constant-family-localization-β :
      equivFun constant-family-localization-equiv ∘ Localization.∣_∣
        ≡ η (λ _ → m)
    constant-family-localization-β = refl

open ConstantFamily public
  using (Lm ; constant-family-locality ; constant-family-localization-equiv ;
         constant-family-localization-β)

-- The stationary route has its own actual unit; no comparison with
-- the cumulative-product telescope is assumed or needed here.
module StationaryPowerUnit {ℓ} (m : ℕ) (X : Pointed ℓ)
  (localTel : Localization.isLocal (DegreeFamily (λ _ → m))
    (SeqColim (StationaryPowerSeq m X)))
  (telescopeUP : (Y : Type ℓ)
    → Localization.isLocal (DegreeFamily (λ _ → m)) Y
    → isEquiv (λ (h : SeqColim (StationaryPowerSeq m X) → Y)
      → h ∘ stationary-i₀ m X)) where

  module UnitProof = LocalizationUnit (stationary-i₀ m X) localTel telescopeUP

  stationary-power-telescope-equiv-from-UP :
    Lm m (typ (Ω X)) ≃ SeqColim (StationaryPowerSeq m X)
  stationary-power-telescope-equiv-from-UP = UnitProof.equivalence

  stationary-power-telescope-β-from-UP :
    equivFun stationary-power-telescope-equiv-from-UP ∘ η (λ _ → m)
      ≡ stationary-i₀ m X
  stationary-power-telescope-β-from-UP = refl

open StationaryPowerUnit public
  using (stationary-power-telescope-equiv-from-UP ;
         stationary-power-telescope-β-from-UP)

-- The pullback comparison includes its stage rule; the pointed loop
-- equivalence here is stationary. SequencePathCode gives identity codes
-- for arbitrary pointed sequences, without a general loop-colimit equivalence.
