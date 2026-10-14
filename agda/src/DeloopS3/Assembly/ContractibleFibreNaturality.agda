{-# OPTIONS --cubical --safe #-}
module DeloopS3.Assembly.ContractibleFibreNaturality where

-- Naturality of fibre-loop equivalences for contractible total spaces.
-- The basepoint square is an explicit hypothesis, not unpointed uniqueness.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_ ; homotopyNatural)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Homotopy.Loopspace using (Ω→)
open import Cubical.Data.Nat using (ℕ ; _·_)
open import DeloopS3.Local.Base using (L ; η)
open import DeloopS3.Local.RouteB2 using (SC ; L-map)
open import DeloopS3.Assembly.LocalizedLoops
import DeloopS3.Assembly.LocalizedFibreNaturality as LF

private
  abstract
    cancel-prefix : {A : Type} {x y z : A} (p : x ≡ y) (q : y ≡ z)
      → sym p ∙ p ∙ q ≡ q
    cancel-prefix p q = assoc (sym p) p q
      ∙ cong (_∙ q) (lCancel p) ∙ sym (lUnit q)

    move-prefix : {A : Type} {w x y : A} (p : w ≡ x)
      (q : x ≡ y) (r : w ≡ y) → p ∙ q ≡ r → q ≡ sym p ∙ r
    move-prefix p q r e = sym (cancel-prefix p q) ∙ cong (sym p ∙_) e

    prefix-rebase : {A : Type} {z u v w b : A}
      (α : z ≡ u) (p : u ≡ b) (h : z ≡ v) (q : v ≡ w) (d : w ≡ b)
      → α ∙ p ≡ h ∙ q ∙ d
      → sym p ∙ sym α ∙ h ≡ sym d ∙ sym q
    prefix-rebase α p h q d e =
      assoc (sym p) (sym α) h
      ∙ cong (_∙ h) (sym (symDistr α p))
      ∙ cong (λ v → sym v ∙ h) e
      ∙ cong (_∙ h) (symDistr h (q ∙ d))
      ∙ sym (assoc (sym (q ∙ d)) (sym h) h)
      ∙ cong (sym (q ∙ d) ∙_) (lCancel h)
      ∙ sym (rUnit (sym (q ∙ d)))
      ∙ symDistr q d

    regroup : {A : Type} {v w x y z u : A}
      (p : v ≡ w) (q : w ≡ x) (r : x ≡ y) (s : y ≡ z) (t : z ≡ u)
      → p ∙ (q ∙ r ∙ s) ∙ t ≡ (p ∙ q ∙ r) ∙ s ∙ t
    regroup p q r s t =
      cong (p ∙_) (sym (assoc q (r ∙ s) t)
        ∙ cong (q ∙_) (sym (assoc r s t)))
      ∙ assoc p q (r ∙ s ∙ t)
      ∙ assoc (p ∙ q) r (s ∙ t)
      ∙ cong (_∙ (s ∙ t)) (sym (assoc p q r))

module ContractibleSquare
  (E P E' P' : Type) (f : E → P) (f' : E' → P')
  (a : E → E') (bmap : P → P')
  (h : (x : E) → f' (a x) ≡ bmap (f x))
  (e₀ : E) (e₀' : E') (b : P) (b' : P')
  (p₀ : f e₀ ≡ b) (p₀' : f' e₀' ≡ b')
  (a₀ : a e₀ ≡ e₀') (d : bmap b ≡ b')
  (basepoint-coherence : cong f' a₀ ∙ p₀' ≡ h e₀ ∙ cong bmap p₀ ∙ d)
  (cE : isContr E) (cE' : isContr E') where

  CG : fiber f b → b ≡ b
  CG = contractible-fiber-coordinate E P f e₀ b p₀ cE

  C* : fiber f' b' → b' ≡ b'
  C* = contractible-fiber-coordinate E' P' f' e₀' b' p₀' cE'

  VG : fiber f b → fiber f' b'
  VG (x , s) = a x , h x ∙ cong bmap s ∙ d

  uG : (P , b) →∙ (P' , b')
  uG = bmap , d

  abstract
    contractible-fibre-natural-G : C* ∘ VG ≡ fst (Ω→ uG) ∘ CG
    contractible-fibre-natural-G = funExt λ (x , s) → calculation x s
      where
      calculation : (x : E) (s : f x ≡ b)
        → C* (VG (x , s)) ≡ fst (Ω→ uG) (CG (x , s))
      calculation x s =
        cong (sym p₀' ∙_) (assoc q (h x) (S ∙ d))
        ∙ cong (λ v → sym p₀' ∙ v ∙ S ∙ d) comm
        ∙ regroup (sym p₀') (sym α) (h e₀) R (S ∙ d)
        ∙ cong (_∙ (R ∙ S ∙ d))
            (prefix-rebase α p₀' (h e₀) B d basepoint-coherence)
        ∙ sym (assoc (sym d) (sym B) (R ∙ S ∙ d))
        ∙ cong (sym d ∙_)
            (cong (sym B ∙_) (assoc R S d) ∙ assoc (sym B) (R ∙ S) d)
        ∙ cong (λ v → sym d ∙ v ∙ d) (sym mapped-coordinate)
        ∙ sym (doubleCompPath-elim' (sym d) (cong bmap (CG (x , s))) d)
        where
        cx : e₀ ≡ x
        cx = isContr→isProp cE e₀ x
        cy : e₀' ≡ a x
        cy = isContr→isProp cE' e₀' (a x)
        α : f' (a e₀) ≡ f' e₀'
        α = cong f' a₀
        q : f' e₀' ≡ f' (a x)
        q = cong f' cy
        B : bmap (f e₀) ≡ bmap b
        B = cong bmap p₀
        R : bmap (f e₀) ≡ bmap (f x)
        R = cong bmap (cong f cx)
        S : bmap (f x) ≡ bmap b
        S = cong bmap s

        contraction-square : a₀ ∙ cy ≡ cong a cx
        contraction-square = isProp→isSet (isContr→isProp cE') _ _ _ _

        comm : q ∙ h x ≡ sym α ∙ h e₀ ∙ R
        comm = move-prefix α (q ∙ h x) (h e₀ ∙ R)
          (assoc α q (h x)
          ∙ cong (_∙ h x) (sym (cong-∙ f' a₀ cy)
            ∙ cong (cong f') contraction-square)
          ∙ sym (homotopyNatural h cx))

        mapped-coordinate : cong bmap (CG (x , s)) ≡ sym B ∙ R ∙ S
        mapped-coordinate = cong-∙ bmap (sym p₀) (cong f cx ∙ s)
          ∙ cong (sym B ∙_) (cong-∙ bmap (cong f cx) s)

-- Instantiation and cancellation for the EXISTING abstract loop equivalences.
-- With (m,n)=(3,10), both legs have target modulus 30.
module LocalizedSquare (m n : ℕ) (leg : LF.Leg)
  (E P E* P* : Type) (t : E → P) (t* : E* → P*)
  (a : E → E*) (bmap : P → P*) (H : t* ∘ a ≡ bmap ∘ t)
  (e₀ : E) (e*₀ : E*) (p₀ : P) (p*₀ : P*)
  (q₀ : t e₀ ≡ p₀) (q*₀ : t* e*₀ ≡ p*₀)
  (a₀ : a e₀ ≡ e*₀) (d : bmap p₀ ≡ p*₀)
  (basepoint-coherence : cong t* a₀ ∙ q*₀
    ≡ funExt⁻ H e₀ ∙ cong bmap q₀ ∙ d)
  (sc : SC P) (sc* : SC P*)
  (cE : isContr (L (LF.source-modulus m n leg) E))
  (cE* : isContr (L (m · n) E*)) where

  module S = LF.Square m n leg E P E* P* t t* a bmap H p₀ p*₀ d
  open S public

  ℓG : (η {r} {P} p₀ ≡ η {r} {P} p₀) ≃ L r (fiber t p₀)
  ℓG = loop-of-localization r E P t e₀ p₀ q₀ sc cE

  ℓ* : (η {k} {P*} p*₀ ≡ η {k} {P*} p*₀) ≃ L k (fiber t* p*₀)
  ℓ* = loop-of-localization k E* P* t* e*₀ p*₀ q*₀ sc* cE*

  uG : (L r P , η {r} {P} p₀) →∙ (L k P* , η {k} {P*} p*₀)
  uG = bGᴸ , dᴸG

  abstract
    localized-basepoint-coherence :
      cong (L-map k t*) (cong (η {k} {E*}) a₀) ∙ cong (η {k} {P*}) q*₀
      ≡ HᴸG (η {r} {E} e₀) ∙ cong bGᴸ (cong (η {r} {P}) q₀) ∙ dᴸG
    localized-basepoint-coherence =
      sym (cong-∙ (η {k} {P*}) (cong t* a₀) q*₀)
      ∙ cong (cong (η {k} {P*})) basepoint-coherence
      ∙ cong-∙ (η {k} {P*}) (funExt⁻ H e₀) (cong bmap q₀ ∙ d)
      ∙ cong (cong (η {k} {P*}) (funExt⁻ H e₀) ∙_)
          (cong-∙ (η {k} {P*}) (cong bmap q₀) d)
      ∙ cong (λ h → h ∙ cong bGᴸ (cong (η {r} {P}) q₀) ∙ dᴸG)
          (sym (HᴸG-β e₀))

  module C = ContractibleSquare (L r E) (L r P) (L k E*) (L k P*)
    (L-map r t) (L-map k t*) aGᴸ bGᴸ HᴸG
    (η {r} {E} e₀) (η {k} {E*} e*₀) (η {r} {P} p₀) (η {k} {P*} p*₀)
    (cong (η {r} {P}) q₀) (cong (η {k} {P*}) q*₀)
    (cong (η {k} {E*}) a₀) dᴸG localized-basepoint-coherence cE cE*

  open C public using (CG ; C*)

  abstract
    contractible-fibre-natural-G : C* ∘ VG ≡ fst (Ω→ uG) ∘ CG
    contractible-fibre-natural-G = C.contractible-fibre-natural-G

    localized-loop-inverse-natural : invEq ℓ* ∘ localized-UG ≡ fst (Ω→ uG) ∘ invEq ℓG
    localized-loop-inverse-natural =
      cong (_∘ localized-UG)
        (loop-of-localization-inverse k E* P* t* e*₀ p*₀ q*₀ sc* cE*)
      ∙ cong (C* ∘_) (sym localized-fibre-natural-G)
      ∙ cong (_∘ θG) contractible-fibre-natural-G
      ∙ cong (fst (Ω→ uG) ∘_)
          (sym (loop-of-localization-inverse r E P t e₀ p₀ q₀ sc cE))

    loop-of-localization-natural-G :
      L-map k UG ∘ LF.jG m n leg (fiber t p₀) ∘ equivFun ℓG
      ≡ equivFun ℓ* ∘ fst (Ω→ uG)
    loop-of-localization-natural-G = funExt λ x →
      sym (secEq ℓ* (localized-UG (equivFun ℓG x)))
      ∙ cong (equivFun ℓ*)
          (funExt⁻ localized-loop-inverse-natural (equivFun ℓG x)
          ∙ cong (fst (Ω→ uG)) (retEq ℓG x))

    -- Exact η-point interface requested by Assembly.Final.FibreInput.
    unit-loop-square : (x : fiber t p₀)
      → fst (Ω→ uG) (invEq ℓG (η {r} {fiber t p₀} x))
        ≡ invEq ℓ* (η {k} {fiber t* p*₀} (UG x))
    unit-loop-square x = sym
      (funExt⁻ localized-loop-inverse-natural (η {r} {fiber t p₀} x))

    -- Normalized inclusions may omit the refl factors of UG. The explicit
    -- agreement transports the theorem without altering any equivalence.
    unit-loop-square-for : (U : fiber t p₀ → fiber t* p*₀)
      → ((x : fiber t p₀) → UG x ≡ U x) → (x : fiber t p₀)
      → fst (Ω→ uG) (invEq ℓG (η {r} {fiber t p₀} x))
        ≡ invEq ℓ* (η {k} {fiber t* p*₀} (U x))
    unit-loop-square-for U agrees x = unit-loop-square x
      ∙ cong (invEq ℓ* ∘ η {k} {fiber t* p*₀}) (agrees x)
