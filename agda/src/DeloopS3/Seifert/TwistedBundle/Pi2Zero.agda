{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}

-- π₂(Mₑ) vanishes for e ≠ 0 by a nonzero image in the suspension model.
-- The LES is that of suspensionClass, not a calibrated bundle boundary.
module DeloopS3.Seifert.TwistedBundle.Pi2Zero where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Pointed
open import Cubical.Foundations.Pointed.Homogeneous
  using (→∙Homogeneous≡; isHomogeneousPath)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Foundations.Path using (symIso)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Int as Z using (ℤ; pos; ·IdR; -Involutive)
open import Cubical.Relation.Nullary using (¬_)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
  using (GroupEquiv→GroupHom; compGroupHom; invGroupEquiv; compGroupEquiv;
         makeIsGroupHom; GroupIso→GroupEquiv)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop)
open import Cubical.HITs.Susp.Base using (Susp; north; south; merid)
open import Cubical.HITs.Susp.Properties
  using (toSuspPointed; ΩSuspAdjointIso; fromSusp→toΩ; congSuspEquiv)
open import Cubical.HITs.Sn.Base using (S₊; S₊∙)
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as TR
open import Cubical.Homotopy.Loopspace
open import Cubical.Homotopy.Group.Base using (π; πGr; πHom; πIso; 1π)
open import Cubical.Homotopy.Group.PinSn using (πₙSⁿ≅ℤ)
open import Cubical.Homotopy.Group.LES using (module πLES)
open import Cubical.Homotopy.Connected using (isConnectedPath)
open import Cubical.Homotopy.EilenbergMacLane.Base using (hLevelEM)
open import Cubical.Homotopy.EilenbergMacLane.Properties using (isConnectedEM)
open import DeloopS3.Move.CancelMinimal using (C; 0C; K; 0K; U; ω; ω₀; mulC)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)
open import DeloopS3.Sphere.RP2UnitFiber using (q; q-fibers-are-sets)
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
open import DeloopS3.Seifert.TwistedBundle.Pi2 using (module Homotopy)
open import DeloopS3.Seifert.TwistedBundle.Exactness
  using (integer-hom-nonzero-injective; pi₂-groupoid-zero; twice-nonzero)
import DeloopS3.Seifert.TwistedBundle.TwoCap as TwoCap
import DeloopS3.Seifert.TwistedBundle.Connecting as Connecting

-- No coordinate of the source witness is computed.
abstract
  nonzero-image→mono : ∀ {ℓ ℓ′} {G : Group ℓ} {H : Group ℓ′}
    (a : GroupEquiv G ℤGroup) (b : GroupEquiv H ℤGroup)
    (f : GroupHom G H) (u : G .fst)
    → ¬ b .fst .fst (f .fst u) ≡ pos 0
    → (x y : G .fst) → f .fst x ≡ f .fst y → x ≡ y
  nonzero-image→mono {G = G} a b f u nz x y p = invEq (congEquiv (a .fst))
    (integer-hom-nonzero-injective h (a .fst .fst u)
      (λ z → nz (sym (coordinate u) ∙ z))
      (a .fst .fst x) (a .fst .fst y)
      (coordinate x ∙ cong (b .fst .fst) p ∙ sym (coordinate y)))
    where
    h : GroupHom ℤGroup ℤGroup
    h = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv a))
      (compGroupHom f (GroupEquiv→GroupHom b))

    coordinate : (x : G .fst)
      → h .fst (a .fst .fst x) ≡ b .fst .fst (f .fst x)
    coordinate x = cong (λ v → b .fst .fst (f .fst v)) (retEq (a .fst) x)

-- The two exactness positions needed for a homotopy fibre.
module MapFiber {ℓ ℓ′ : Level} {A : Pointed ℓ} {B : Pointed ℓ′}
  (f : A →∙ B) where
  module L = πLES f

  abstract
    fiber-π₂-zero : isContr (π 3 B)
      → ((x y : π 2 A)
          → πHom 1 f .fst x ≡ πHom 1 f .fst y → x ≡ y)
      → isContr (π 2 L.fib)
    fiber-π₂-zero target-zero injective = 1π 2 , contract
      where
      inclusion-zero : (z : π 2 L.fib) → L.fib→A 1 .fst z ≡ 1π 2
      inclusion-zero z = injective (L.fib→A 1 .fst z) (1π 2)
        (L.Im-fib→A⊂Ker-A→B 1 (L.fib→A 1 .fst z) PT.∣ z , refl ∣₁
          ∙ sym (IsGroupHom.pres1 (L.A→B 1 .snd)))

      contract : (z : π 2 L.fib) → 1π 2 ≡ z
      contract z = PT.rec (ST.squash₂ (1π 2) z)
        (λ { (y , hy) → sym (IsGroupHom.pres1 (L.B→fib 1 .snd))
          ∙ cong (L.B→fib 1 .fst)
              (isContr→isProp target-zero (1π 3) y) ∙ hy })
        (L.Ker-fib→A⊂Im-B→fib 1 z (inclusion-zero z))

-- Functoriality only involves small pointed types.
abstract
  πHom-comp : ∀ {ℓ₁ ℓ₂ ℓ₃}
    {A : Pointed ℓ₁} {B : Pointed ℓ₂} {D : Pointed ℓ₃}
    (n : ℕ) (g : B →∙ D) (f : A →∙ B) (x : π (suc n) A)
    → πHom n (g ∘∙ f) .fst x ≡ πHom n g .fst (πHom n f .fst x)
  πHom-comp n g f = ST.elim (λ _ → isProp→isSet (ST.squash₂ _ _))
    (λ p → cong ST.∣_∣₂ (cong (λ h → h .fst p) (Ω^→∘∙ (suc n) g f)))

module Suspension where
  C∙ K∙ SC∙ : Pointed₀
  C∙ = C , 0C
  K∙ = K , 0K
  SC∙ = Susp C , north

  ω∙ : C∙ →∙ Ω K∙
  ω∙ = ω .fst , ω₀

  mul∙ : ℤ → C∙ →∙ C∙
  mul∙ d = mulC d , refl

  c∙ : ℤ → SC∙ →∙ K∙
  c∙ d = TwoCap.suspensionClass d , refl

  σ∙ : C∙ →∙ Ω SC∙
  σ∙ = toSuspPointed C∙

  abstract
    c-as-adjoint : (d : ℤ)
      → c∙ d ≡ Iso.fun (ΩSuspAdjointIso {A = C∙} {B = K∙}) (ω∙ ∘∙ mul∙ d)
    c-as-adjoint d = ΣPathP
      (funExt (λ { north → refl ; south → refl ; (merid a i) → refl }) , refl)

    suspension-adjoint : (d : ℤ)
      → (Ω→ (c∙ d) ∘∙ σ∙) ≡ (ω∙ ∘∙ mul∙ d)
    suspension-adjoint d =
      →∙Homogeneous≡ {A∙ = C∙} {B∙ = Ω K∙}
        {f∙ = Ω→ (c∙ d) ∘∙ σ∙}
        {g∙ = fromSusp→toΩ {A = C∙} {B = K∙} (c∙ d)}
        (isHomogeneousPath K refl) refl
      ∙ cong (fromSusp→toΩ {A = C∙} {B = K∙}) (c-as-adjoint d)
      ∙ Iso.ret (ΩSuspAdjointIso {A = C∙} {B = K∙}) (ω∙ ∘∙ mul∙ d)

  h₁ : π 1 C∙
  h₁ = ST.∣ emloop (pos 1) ∣₂

  w : π 2 SC∙
  w = πHom 0 σ∙ .fst h₁

  ωπ : GroupEquiv (πGr 0 C∙) (πGr 1 K∙)
  ωπ .fst = πIso {A = C∙} {B = Ω K∙} (ω , ω₀) 0 .fst
  ωπ .snd = makeIsGroupHom λ x y →
    IsGroupHom.pres· (πIso {A = C∙} {B = Ω K∙} (ω , ω₀) 0 .snd) x y

  abstract
    normalize-units : ∀ {ℓ} {X : Type ℓ} {x y : X} (p : x ≡ y)
      → refl ∙∙ p ∙∙ refl ≡ p
    normalize-units p = doubleCompPath-elim refl p refl
      ∙ sym (rUnit (refl ∙ p)) ∙ sym (lUnit p)

    mul-witness : (d : ℤ)
      → πHom 0 (mul∙ d) .fst h₁ ≡ ST.∣ emloop d ∣₂
    mul-witness d = cong ST.∣_∣₂
      (normalize-units (cong (mulC d) (emloop (pos 1)))
        ∙ cong emloop (·IdR d))

    suspension-witness : (d : ℤ)
      → πHom 1 (c∙ d) .fst w ≡ ωπ .fst .fst ST.∣ emloop d ∣₂
    suspension-witness d = sym (πHom-comp 0 (Ω→ (c∙ d)) σ∙ h₁)
      ∙ cong (λ f → πHom {A = C∙} {B = Ω K∙} 0 f .fst h₁)
          (suspension-adjoint d)
      ∙ πHom-comp 0 ω∙ (mul∙ d) h₁
      ∙ cong (πHom 0 ω∙ .fst) (mul-witness d)


  -- The arbitrary sphere chart is never evaluated on w.
  abstract
    χC : GroupEquiv (πGr 0 C∙) ℤGroup
    χC = invGroupEquiv (Homotopy.integerCircleGroup (pos 0))

    circle-chart-emloop : (n : ℤ)
      → χC .fst .fst ST.∣ emloop n ∣₂ ≡ n
    circle-chart-emloop n = retEq
      (Homotopy.integerCircleGroup (pos 0) .fst) n

  abstract
    χK : GroupEquiv (πGr 1 K∙) ℤGroup
    χK = compGroupEquiv (invGroupEquiv ωπ) χC

    χK-ωπ : (x : π 1 C∙)
      → χK .fst .fst (ωπ .fst .fst x) ≡ χC .fst .fst x
    χK-ωπ x = cong (χC .fst .fst) (retEq (ωπ .fst) x)

  abstract
    witness-coordinate : (d : ℤ)
      → χK .fst .fst (πHom 1 (c∙ d) .fst w) ≡ d
    witness-coordinate d = cong (χK .fst .fst) (suspension-witness d)
      ∙ χK-ωπ ST.∣ emloop d ∣₂
      ∙ circle-chart-emloop d

  abstract
    sphereSusp : S₊ 2 ≃ Susp C
    sphereSusp = congSuspEquiv S¹≃C

    sphereSusp-point : sphereSusp .fst north ≡ north
    sphereSusp-point = refl

    χS : GroupEquiv (πGr 1 SC∙) ℤGroup
    χS = compGroupEquiv
      (invGroupEquiv (πIso {A = S₊∙ 2} {B = SC∙}
        (sphereSusp , sphereSusp-point) 1))
      (GroupIso→GroupEquiv (πₙSⁿ≅ℤ 1))

  abstract
    suspension-π₂-injective : (d : ℤ) → ¬ d ≡ pos 0
      → (x y : π 2 SC∙)
      → πHom 1 (c∙ d) .fst x ≡ πHom 1 (c∙ d) .fst y → x ≡ y
    suspension-π₂-injective d nz = nonzero-image→mono χS χK
      (πHom 1 (c∙ d)) w (λ p → nz (sym (witness-coordinate d) ∙ p))

    π₃K-zero : isContr (π 3 K∙)
    π₃K-zero = pi₂-groupoid-zero (hLevelEM ℤAbGroup 2 0K 0K) refl

    suspension-fiber-π₂-zero₀ : (d : ℤ) → ¬ d ≡ pos 0
      → isContr (π 2 (fiber (TwoCap.suspensionClass d) 0K , (north , refl)))
    suspension-fiber-π₂-zero₀ d nz =
      MapFiber.fiber-π₂-zero (c∙ d) π₃K-zero (suspension-π₂-injective d nz)

  -- Eliminate into propositions, rather than point the TwoCap model.
  module AllBasepoints (d : ℤ) (nz : ¬ d ≡ pos 0) where
    F : Type₀
    F = fiber (TwoCap.suspensionClass d) 0K

    P : Susp C → Type₀
    P x = (r : TwoCap.suspensionClass d x ≡ 0K)
      → isContr (π 2 (F , (x , r)))

    abstract
      pn : P north
      pn r = TR.rec isPropIsContr
        (λ p → subst (λ t → isContr (π 2 (F , (north , t)))) p
          (suspension-fiber-π₂-zero₀ d nz))
        (isConnectedPath 1
          (isConnectedPath 2 (isConnectedEM {G' = ℤAbGroup} 2) 0K 0K)
          refl r .fst)

    ps : P south
    ps = subst P (merid 0C) pn

    all : (x : Susp C) → P x
    all north = pn
    all south = ps
    all (merid a i) = isProp→PathP {B = λ j → P (merid a j)}
      (λ j → isPropΠ (λ _ → isPropIsContr)) pn ps i

  abstract
    suspension-fiber-π₂-zero : (d : ℤ) → ¬ d ≡ pos 0
      → (z : fiber (TwoCap.suspensionClass d) 0K)
      → isContr (π 2 (fiber (TwoCap.suspensionClass d) 0K , z))
    suspension-fiber-π₂-zero d nz (x , r) = AllBasepoints.all d nz x r

-- Path decomposition, reversal, and a dependent singleton.
-- Keeping this generic prevents the descended family from being normalized.
module PullbackTotal {ℓX ℓB ℓF : Level} {X : Type ℓX} {B : Type ℓB}
  (q₀ : X → B) (F : B → Type ℓF) where
  E : Type (ℓ-max ℓX ℓF)
  E = Σ X (F ∘ q₀)

  M : Type (ℓ-max ℓB ℓF)
  M = Σ B F

  Q : E → M
  Q (x , u) = q₀ x , u

  private
    Remainder : (m : M) → fiber q₀ (fst m) → Type ℓF
    Remainder (b , v) (x , p) = singlP (λ i → F (p (~ i))) v

    decompose : (m : M) → fiber Q m
      → Σ (fiber q₀ (fst m)) (Remainder m)
    decompose m ((x , u) , r) =
      (x , cong fst r) , (u , λ i → r (~ i) .snd)

    reassemble : (m : M) → Σ (fiber q₀ (fst m)) (Remainder m)
      → fiber Q m
    reassemble m ((x , p) , (u , α)) =
      (x , u) , (λ i → p i , α (~ i))

  abstract
    pullback-total-fiber : (m : M) → fiber Q m ≃ fiber q₀ (fst m)
    pullback-total-fiber m = compEquiv
      (isoToEquiv (iso (decompose m) (reassemble m) (λ _ → refl) (λ _ → refl)))
      (Σ-contractSnd (λ { (x , p) → isContrSinglP (λ i → F (p (~ i))) (snd m) }))

    Q-discrete : ((b : B) → isSet (fiber q₀ b))
      → (m : M) → isSet (fiber Q m)
    Q-discrete discrete m = isOfHLevelRespectEquiv 2
      (invEquiv (pullback-total-fiber m)) (discrete (fst m))

  module AtPoint (discrete : (b : B) → isSet (fiber q₀ b))
    (m : M) (sheet : fiber q₀ (fst m)) where
    abstract
      lift₀ : fiber Q m
      lift₀ = invEq (pullback-total-fiber m) sheet

    v₀ : E
    v₀ = lift₀ .fst

    Q∙ : (E , v₀) →∙ (M , m)
    Q∙ = Q , lift₀ .snd

    abstract
      Qπ₂ : GroupEquiv (πGr 1 (E , v₀)) (πGr 1 (M , m))
      Qπ₂ = Connecting.cover-π₂ {X = E , v₀} {Y = M , m}
        Q∙ (Q-discrete discrete)

      total-cover-π₂-zero : ((v : E) → isContr (π 2 (E , v)))
        → isContr (π 2 (M , m))
      total-cover-π₂-zero source-zero =
        isOfHLevelRespectEquiv 0 (Qπ₂ .fst) (source-zero v₀)

-- An unpointed equivalence is automatically pointed at the image of x.
abstract
  π₂-equiv-zero : ∀ {ℓ ℓ′} {X : Type ℓ} {Y : Type ℓ′}
    (t : X ≃ Y) (x : X) → isContr (π 2 (Y , t .fst x))
    → isContr (π 2 (X , x))
  π₂-equiv-zero {X = X} {Y = Y} t x = isOfHLevelRespectEquiv 0
    (invEquiv (πIso {A = X , x} {B = Y , t .fst x} (t , refl) 1 .fst))

-- Only the exported calibrated equivalences are used here.
-- In particular, neither Chart.H nor the marked cancellation is unfolded
-- to calculate a sphere generator or a total-space basepoint.
module ActualBundle (e : ℤ) where
  module B = Bundle e
  module T = TwoCap.Calibrated e

  E : Type₀
  E = Σ (S₊ 2) (B.Fₑ ∘ q)

  abstract
    total-to-class-fiber : E ≃ fiber T.calibratedClass 0K
    total-to-class-fiber = compEquiv
      {A = E} {B = Σ (S₊ 2) (U ∘ T.calibratedClass)}
      {C = fiber T.calibratedClass 0K}
      T.calibratedTotal
      (Σ-cong-equiv-snd {A = S₊ 2}
        {B = U ∘ T.calibratedClass}
        {B' = λ x → T.calibratedClass x ≡ 0K}
        (λ x → isoToEquiv (symIso {a = 0K} {b = T.calibratedClass x})))

    total-to-class-fiber-over : (v : E)
      → total-to-class-fiber .fst v .fst ≡ v .fst
    total-to-class-fiber-over v = T.calibratedTotal-over v

    class-fiber-to-susp-fiber : fiber T.calibratedClass 0K
      ≃ fiber (TwoCap.suspensionClass T.degree) 0K
    class-fiber-to-susp-fiber = Σ-cong-equiv-fst
      {A = S₊ 2} {A' = Susp C}
      {B = λ y → TwoCap.suspensionClass T.degree y ≡ 0K}
      T.calibratedSphere

    model : E ≃ fiber (TwoCap.suspensionClass T.degree) 0K
    model = compEquiv
      {A = E} {B = fiber T.calibratedClass 0K}
      {C = fiber (TwoCap.suspensionClass T.degree) 0K}
      total-to-class-fiber class-fiber-to-susp-fiber

  abstract
    degree-nonzero : ¬ e ≡ pos 0 → ¬ T.degree ≡ pos 0
    degree-nonzero nz p = twice-nonzero e nz
      (sym (-Involutive (pos 2 Z.· e)) ∙ cong Z.-_ p)

    pullback-π₂-zero : ¬ e ≡ pos 0
      → (v : E) → isContr (π 2 (E , v))
    pullback-π₂-zero nz v = π₂-equiv-zero
      {X = E} {Y = fiber (TwoCap.suspensionClass T.degree) 0K} model v
      (Suspension.suspension-fiber-π₂-zero T.degree (degree-nonzero nz)
        (model .fst v))

  module Pullback = PullbackTotal q B.Fₑ
  module Cover = Pullback.AtPoint q-fibers-are-sets B.m₀ Connecting.capLift

  abstract
    pi₂-zero : ¬ e ≡ pos 0 → isContr (π 2 (B.Mₑ , B.m₀))
    pi₂-zero nz = Cover.total-cover-π₂-zero (pullback-π₂-zero nz)

-- Vanishing at the bundle basepoint, assuming only e ≠ 0.
pi₂-Mₑ-zero : (e : ℤ) → ¬ e ≡ pos 0
  → isContr (π 2 (Bundle.Mₑ e , Bundle.m₀ e))
pi₂-Mₑ-zero e = ActualBundle.pi₂-zero e
