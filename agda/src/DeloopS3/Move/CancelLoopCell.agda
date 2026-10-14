{-# OPTIONS --safe --cubical #-}

-- Untruncated loop--cell cancellation, retaining the relation comparison.
-- No other attachments, graph presentation, or truncation assumption.
module DeloopS3.Move.CancelLoopCell where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path
open import Cubical.Data.Sigma
open import Cubical.Data.Unit
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.S1.Base using (S¹; base; loop)
open import DeloopS3.Move.CancelMinimalCore using (EquivOver)

private
  variable
    ℓ ℓ' ℓ'' ℓ''' : Level

-- The complete fibre, including its relation comparison, is
-- contractible.  That second component supplies the cell cube.
data Sign : Type₀ where
  plus minus : Sign

power : {X : Type ℓ} {a : X} → Sign → a ≡ a → a ≡ a
power plus p = p
power minus p = sym p

powerEquiv : {X : Type ℓ} (a : X) (ε : Sign) → (a ≡ a) ≃ (a ≡ a)
powerEquiv a ε .fst = power ε
powerEquiv a plus .snd = idEquiv _ .snd
powerEquiv a minus .snd = isoToIsEquiv (iso sym sym (λ _ → refl) (λ _ → refl))

ΦEquiv : {X : Type ℓ} (a : X) (u v : a ≡ a) (ε : Sign)
  → (a ≡ a) ≃ (a ≡ a)
ΦEquiv a u v ε = compEquiv (powerEquiv a ε)
  (compEquiv (compPathlEquiv u) (compPathrEquiv v))

solve-loop : {X : Type ℓ} (a : X) (u v : a ≡ a) (ε : Sign)
  → isContr (Σ[ y ∈ (a ≡ a) ] (((u ∙ power ε y) ∙ v) ≡ refl))
solve-loop a u v ε = ΦEquiv a u v ε .snd .equiv-proof refl

-- The two chosen solutions and the exact associativity/cancellation
-- composites (the library's assoc points right-to-left).
solve-plus : {X : Type ℓ} {a : X} (u v : a ≡ a)
  → (u ∙ (sym u ∙ sym v)) ∙ v ≡ refl
solve-plus u v = cong (_∙ v)
  (assoc u (sym u) (sym v)
    ∙ cong (_∙ sym v) (rCancel u)
    ∙ sym (lUnit (sym v)))
  ∙ lCancel v

solve-minus : {X : Type ℓ} {a : X} (u v : a ≡ a)
  → (u ∙ sym (v ∙ u)) ∙ v ≡ refl
solve-minus u v = cong (λ y → (u ∙ y) ∙ v) (symDistr v u)
  ∙ solve-plus u v

-- The full mapping-type universal property, not homotopy classes.
module PushoutUP {A : Type ℓ} {L : Type ℓ'} {R : Type ℓ''}
  (f : A → L) (g : A → R) (X : Type ℓ''') where

  Cocone : Type (ℓ-max (ℓ-max (ℓ-max ℓ ℓ') ℓ'') ℓ''')
  Cocone = Σ[ l ∈ (L → X) ] Σ[ r ∈ (R → X) ]
    ((a : A) → l (f a) ≡ r (g a))

  restrict : (Pushout f g → X) → Cocone
  restrict h = (h ∘ inl) , (h ∘ inr) , λ a → cong h (push a)

  extend : Cocone → Pushout f g → X
  extend (l , r , δ) (inl x) = l x
  extend (l , r , δ) (inr x) = r x
  extend (l , r , δ) (push a i) = δ a i

  β : (d : Cocone) → restrict (extend d) ≡ d
  β d = refl

  η : (h : Pushout f g → X) → extend (restrict h) ≡ h
  η h j (inl l) = h (inl l)
  η h j (inr r) = h (inr r)
  η h j (push a i) = h (push a i)

  pushoutUP : (Pushout f g → X) ≃ Cocone
  pushoutUP = isoToEquiv (iso restrict extend β η)

-- The dependent circle recursion equivalence.
module CircleUP (B : S¹ → Type ℓ) where
  Data : Type ℓ
  Data = Σ[ b ∈ B base ] PathP (λ i → B (loop i)) b b

  restrict : ((a : S¹) → B a) → Data
  restrict f = f base , λ i → f (loop i)

  extend : Data → (a : S¹) → B a
  extend (b , p) base = b
  extend (b , p) (loop i) = p i

  β : (d : Data) → restrict (extend d) ≡ d
  β d = refl

  η : (f : (a : S¹) → B a) → extend (restrict f) ≡ f
  η f j base = f base
  η f j (loop i) = f (loop i)

  circleUP : ((a : S¹) → B a) ≃ Data
  circleUP = isoToEquiv (iso restrict extend β η)

circleMap : {P : Type ℓ} {p : P} → p ≡ p → S¹ → P
circleMap {p = p} l base = p
circleMap l (loop i) = l i

CofibLoop : {P : Type ℓ} (p : P) → p ≡ p → Type ℓ
CofibLoop p l = Pushout (circleMap l) (λ _ → tt)

-- Cancellation of the common vertical edge γ.  J packages the
-- generic unit/cancellation squares without expanding any HIT recursor.
-- At γ=refl this is exactly transposition of the constructor square.
square-cancel : {X : Type ℓ} {a z : X} (p : a ≡ a) (γ : a ≡ z)
  → PathP (λ i → p i ≡ z) γ γ ≃ (p ≡ refl)
square-cancel {a = a} p γ = J
  (λ z γ → PathP (λ i → p i ≡ z) γ γ ≃ (p ≡ refl))
  (isoToEquiv (iso (λ s j i → s i j) (λ s i j → s j i)
    (λ _ → refl) (λ _ → refl))) γ

module CofiberUP {P : Type ℓ} (p : P) (l : p ≡ p) (X : Type ℓ') where
  V = CofibLoop p l

  Cocone : Type (ℓ-max ℓ ℓ')
  Cocone = Σ[ f ∈ (P → X) ] Σ[ z ∈ X ]
    ((a : S¹) → f (circleMap l a) ≡ z)

  restrict : (V → X) → Cocone
  restrict h = (h ∘ inl) , h (inr tt) , λ a → cong h (push a)

  extend : Cocone → V → X
  extend (f , z , g) (inl x) = f x
  extend (f , z , g) (inr tt) = z
  extend (f , z , g) (push a i) = g a i

  β : (d : Cocone) → restrict (extend d) ≡ d
  β d = refl

  η : (h : V → X) → extend (restrict h) ≡ h
  η h j (inl x) = h (inl x)
  η h j (inr tt) = h (inr tt)
  η h j (push a i) = h (push a i)

  coconeEquiv : (V → X) ≃ Cocone
  coconeEquiv = isoToEquiv (iso restrict extend β η)

  -- The contractible singleton is eliminated only after retaining the
  -- entire square type, so no two-cell information is truncated away.
  relationEquiv : (f : P → X)
    → (Σ[ z ∈ X ] ((a : S¹) → f (circleMap l a) ≡ z))
      ≃ (cong f l ≡ refl)
  relationEquiv f = compEquiv
    (Σ-cong-equiv-snd (λ z → CircleUP.circleUP (λ a → f (circleMap l a) ≡ z)))
    (compEquiv
      (Σ-cong-equiv-snd (λ z → Σ-cong-equiv-snd (square-cancel (cong f l))))
      (compEquiv (invEquiv Σ-assoc-≃)
        (Σ-contractFst (isContrSingl (f p)))))

  cofiberUP : (V → X) ≃ (Σ[ f ∈ (P → X) ] (cong f l ≡ refl))
  cofiberUP = compEquiv coconeEquiv (Σ-cong-equiv-snd relationEquiv)

-- Free adjoining of precisely one loop, with no truncation.
data AddLoop (Q : Type ℓ) (q : Q) : Type ℓ where
  incQ : Q → AddLoop Q q
  x : incQ q ≡ incQ q

module AddLoopUP {Q : Type ℓ} (q : Q) (X : Type ℓ') where
  Data : Type (ℓ-max ℓ ℓ')
  Data = Σ[ f ∈ (Q → X) ] (f q ≡ f q)

  restrict : (AddLoop Q q → X) → Data
  restrict g = (g ∘ incQ) , cong g x

  extend : Data → AddLoop Q q → X
  extend (f , y) (incQ a) = f a
  extend (f , y) (x i) = y i

  β : (d : Data) → restrict (extend d) ≡ d
  β d = refl

  η : (g : AddLoop Q q → X) → extend (restrict g) ≡ g
  η g j (incQ a) = g (incQ a)
  η g j (x i) = g (x i)

  addLoopUP : (AddLoop Q q → X) ≃ Data
  addLoopUP = isoToEquiv (iso restrict extend β η)

power-cong : {X : Type ℓ} {Y : Type ℓ'} {a : X}
  (ε : Sign) (f : X → Y) (p : a ≡ a)
  → cong f (power ε p) ≡ power ε (cong f p)
power-cong plus f p = refl
power-cong minus f p = refl

module PrimitiveCancellation (Q : Type ℓ) (q : Q)
  (L R : q ≡ q) (ε : Sign) where
  A : Type ℓ
  A = AddLoop Q q

  -- The fixed parenthesization of the attached word.
  w : Path A (incQ q) (incQ q)
  w = (cong incQ L ∙ power ε x) ∙ cong incQ R

  V : Type ℓ
  V = CofibLoop (incQ q) w

  j : Q → V
  j a = inl (incQ a)

  map-word : {X : Type ℓ'} (g : A → X)
    → cong g w ≡
      ((cong (g ∘ incQ) L ∙ power ε (cong g x)) ∙ cong (g ∘ incQ) R)
  map-word g = cong-∙ g (cong incQ L ∙ power ε x) (cong incQ R)
    ∙ cong (_∙ cong (g ∘ incQ) R) (cong-∙ g (cong incQ L) (power ε x))
    ∙ cong (λ y → (cong (g ∘ incQ) L ∙ y) ∙ cong (g ∘ incQ) R)
        (power-cong ε g x)

  -- cofiberUP, AddLoop recursion, cong-∙/cong-sym, and the
  -- contractible loop-equation fibre, in that order.  Its forward map
  -- is definitionally restriction along the original inclusion j.
  restrictionEquiv : (X : Type ℓ') → (V → X) ≃ (Q → X)
  restrictionEquiv X = compEquiv (CofiberUP.cofiberUP (incQ q) w X)
    (compEquiv
      (Σ-cong-equiv (AddLoopUP.addLoopUP q X)
        (λ g → compPathlEquiv (sym (map-word g))))
      (compEquiv Σ-assoc-≃
        (Σ-contractSnd (λ f → solve-loop (f q) (cong f L) (cong f R) ε))))

  restriction-β : {X : Type ℓ'} (f : V → X)
    → restrictionEquiv X .fst f ≡ f ∘ j
  restriction-β f = refl

  -- The cancellation retraction uses no Yoneda theorem or generic cube filler.
  r : V → Q
  r = invEq (restrictionEquiv Q) (idfun Q)

  rj : r ∘ j ≡ idfun Q
  rj = secEq (restrictionEquiv Q) (idfun Q)

  private
    Extension : Type ℓ
    Extension = Σ[ f ∈ (V → V) ] (f ∘ j ≡ j)

    extensions-contractible : isContr Extension
    extensions-contractible = restrictionEquiv V .snd .equiv-proof j

    jr-extension : Extension
    jr-extension = (j ∘ r) , (λ i a → j (rj i a))

    id-extension : Extension
    id-extension = idfun V , refl

  -- The second component of the extension path is the comparison on
  -- Q; cofiberUP and solve-loop retain its entire attached-cell cube.
  extension-path : jr-extension ≡ id-extension
  extension-path = sym (extensions-contractible .snd jr-extension)
    ∙ extensions-contractible .snd id-extension

  H : j ∘ r ≡ idfun V
  H = cong fst extension-path

  H-on-Q : PathP (λ i → (H i ∘ j) ≡ j)
    (λ i a → j (rj i a)) refl
  H-on-Q i = extension-path i .snd

  primitive-cancel : isEquiv j
  primitive-cancel = isoToIsEquiv (iso j r (λ z i → H i z) (λ a i → rj i a))

  jEquiv : Q ≃ V
  jEquiv = j , primitive-cancel

  rEquiv : V ≃ Q
  rEquiv = isoToEquiv (iso r j (λ a i → rj i a) (λ z i → H i z))

  -- The marking is retained as an actual slice homotopy, not forgotten.
  primitive-cancel-over : {B : Type ℓ'} (m : V → B)
    → EquivOver m (m ∘ j)
  primitive-cancel-over m = rEquiv , λ z → cong m (λ i → H (~ i) z)
