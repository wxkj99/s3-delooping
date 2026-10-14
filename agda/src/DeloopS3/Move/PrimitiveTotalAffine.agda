{-# OPTIONS --safe --cubical #-}

-- Fibre affinity of primitive total-space cancellation.
-- The comparison is proved with abstract functions before the primitive
-- cancellation (and, in particular, its large cell homotopy) is substituted.
module DeloopS3.Move.PrimitiveTotalAffine where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ)
open import Cubical.Algebra.AbGroup.Instances.Int using (ℤAbGroup)
open import Cubical.Homotopy.EilenbergMacLane.GroupStructure using (lUnitₖ)
open import Cubical.HITs.Pushout.Base using (inl)
open import DeloopS3.Move.CancelLoopCell using (Sign; module PrimitiveCancellation)
open import DeloopS3.Move.CancelMinimal using (C; K; 0C; 0K; U; ω; _+C_)
open import DeloopS3.Move.PrimitiveTotal using (omega-transport-affine; module Diagram)

-- No laws for the translation operation are needed: equality at the origin
-- and the two equivariance paths suffice. All pasting endpoints are explicit.
module AffineComparison {ℓA ℓC ℓX : Level}
  {A : Type ℓA} {Fibre : Type ℓC} {X : Type ℓX}
  (zero : Fibre) (translate : Fibre → X → X)
  (f g : A × Fibre → X)
  (at-zero : (a : A) → f (a , zero) ≡ g (a , zero))
  (f-affine : (a : A) (t : Fibre)
    → f (a , t) ≡ translate t (f (a , zero)))
  (g-affine : (a : A) (t : Fibre)
    → g (a , t) ≡ translate t (g (a , zero))) where

  abstract
    comparison : (a : A) (t : Fibre) → f (a , t) ≡ g (a , t)
    comparison a t =
      _∙_ {ℓX} {X} {x = f (a , t)}
        {y = translate t (f (a , zero))} {z = g (a , t)}
        (f-affine a t)
        (_∙_ {ℓX} {X} {x = translate t (f (a , zero))}
          {y = translate t (g (a , zero))} {z = g (a , t)}
          (cong (translate t) (at-zero a)) (sym (g-affine a t)))

-- Hide the transport evaluator before substituting a concrete correction.
-- Otherwise conversion tries to execute transp on the primitive cell cube.
abstract
  evaluate : (k : K) → k ≡ 0K → U k → C
  evaluate k p v = invEq ω (transport (cong U p) v)

  evaluate-formula : (k : K) (p : k ≡ 0K) (v : U k)
    → evaluate k p v ≡ invEq ω (transport (cong U p) v)
  evaluate-formula k p v = refl

  evaluate-affine : (p : Path K 0K 0K) (t : C)
    → evaluate 0K p (ω .fst t) ≡ t +C invEq ω p
  evaluate-affine = omega-transport-affine

-- Repackage the full, dependent formula before restricting to the graph.
module HideTransport {ℓV ℓB : Level} {V : Type ℓV} {B : Type ℓB}
  (m : V → K) (r : V → B) (p : (z : V) → m z ≡ 0K)
  (f : Σ V (λ z → U (m z)) → B × C)
  (formula : (z : V) (v : U (m z))
    → f (z , v) ≡ (r z , invEq ω (transport (cong U (p z)) v))) where

  abstract
    hidden-formula : (z : V) (v : U (m z))
      → f (z , v) ≡ (r z , evaluate (m z) (p z) v)
    hidden-formula z v = formula z v
      ∙ (λ i → r z , evaluate-formula (m z) (p z) v (~ i))

-- The input formula is a hypothesis about an abstract f. Neither the proof
-- nor its type mentions total-cancel or the primitive cell homotopy.
module TransportAffinity {ℓA ℓB : Level} {A : Type ℓA} {B : Type ℓB}
  (r : A → B) (p : A → Path K 0K 0K)
  (f : A × C → B × C)
  (formula : (a : A) (t : C)
    → f (a , t)
      ≡ (r a , evaluate 0K (p a) (ω .fst t))) where

  translate : C → B × C → B × C
  translate t z = z .fst , t +C z .snd

  g : A × C → B × C
  g z = r (z .fst) , z .snd +C invEq ω (p (z .fst))

  abstract
    origin : (a : A) → f (a , 0C) ≡ (r a , invEq ω (p a))
    origin a = formula a 0C ∙
      (λ i → r a ,
        (evaluate-affine (p a) 0C
          ∙ lUnitₖ {G = ℤAbGroup} 1 (invEq ω (p a))) i)

    at-zero : (a : A) → f (a , 0C) ≡ g (a , 0C)
    at-zero a = origin a ∙
      (λ i → r a , lUnitₖ {G = ℤAbGroup} 1 (invEq ω (p a)) (~ i))

    f-affine : (a : A) (t : C)
      → f (a , t) ≡ translate t (f (a , 0C))
    f-affine a t = formula a t
      ∙ (λ i → r a , evaluate-affine (p a) t i)
      ∙ cong (translate t) (sym (origin a))

    g-affine : (a : A) (t : C)
      → g (a , t) ≡ translate t (g (a , 0C))
    g-affine a t i = r a ,
      t +C lUnitₖ {G = ℤAbGroup} 1 (invEq ω (p a)) (~ i)

  module Compare = AffineComparison 0C translate f g at-zero f-affine g-affine

  abstract
    comparison : (a : A) (t : C)
      → f (a , t) ≡ (r a , t +C invEq ω (p a))
    comparison = Compare.comparison

module Affine {ℓ : Level} (Q : Type ℓ) (q₀ : Q)
  (L R : q₀ ≡ q₀) (ε : Sign) (s k : ℤ) where
  module D = Diagram Q q₀ L R ε s k
  module P = PrimitiveCancellation Q q₀ L R ε

  module Hidden = HideTransport {V = P.V} {B = Q}
    D.m P.r D.correction (D.total-cancel .fst) D.total-cancel-formula

  opaque
    hidden-graph-formula : (a : D.oldGraph) (t : C)
      → D.total-cancel .fst (inl a , ω .fst t)
        ≡ (P.r (inl a) , evaluate 0K (D.correction (inl a)) (ω .fst t))
    hidden-graph-formula a t = Hidden.hidden-formula (inl a) (ω .fst t)

  module GraphAffinity = TransportAffinity
    {A = D.oldGraph} {B = Q}
    (λ a → P.r (inl a)) (λ a → D.correction (inl a))
    (λ z → D.total-cancel .fst (inl (z .fst) , ω .fst (z .snd)))
    hidden-graph-formula

  -- The right endpoint is graph-value's defining expression. Re-exporting
  -- the abstract theorem avoids expanding the correction in conversion.
  open GraphAffinity public using () renaming (comparison to cancel-on-graph)
