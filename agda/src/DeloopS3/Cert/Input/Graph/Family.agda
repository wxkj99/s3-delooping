{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Graph.Family where

-- Dependent-rose flattening by cubical glue/unglue, with one vertex.
-- The coherence is generic in the set-family, independently of finite groups.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.Univalence
open import Cubical.Foundations.HLevels
open import Cubical.Data.Sigma
open import Cubical.Data.SumFin using (fzero; fsuc)
open import DeloopS3.Cert.Interpret.Syntax using (twoGenerators)
open import DeloopS3.Cert.Input.Graph.Core
open import DeloopS3.Move.CancelMinimalCore using (ua-equiv-family)
import DeloopS3.Cert.Interpret.Realization as R

module Normalized (S : Type₀) (e : Generator → S ≃ S) where
  next : S → Generator → S
  next s g = equivFun (e g) s

  Graph : Type₀
  Graph = ActionGraph S next

  Family : R.Rose twoGenerators → Type₀
  Family R.root = S
  Family (R.petal fzero i) = ua (e ga) i
  Family (R.petal (fsuc fzero) i) = ua (e gb) i
  Family (R.petal (fsuc (fsuc ())) i)

  Total : Type₀
  Total = Σ (R.Rose twoGenerators) Family

  forward : Graph → Total
  forward (vertex s) = R.root , s
  forward (edge s ga i) = R.petal fzero i , ua-gluePt (e ga) i s
  forward (edge s gb i) = R.petal (fsuc fzero) i , ua-gluePt (e gb) i s

  backward : Total → Graph
  backward (R.root , s) = vertex s
  backward (R.petal fzero i , s) =
    hcomp (λ j → λ { (i = i0) → edge s ga (~ j)
                     ; (i = i1) → vertex s })
      (vertex (ua-unglue (e ga) i s))
  backward (R.petal (fsuc fzero) i , s) =
    hcomp (λ j → λ { (i = i0) → edge s gb (~ j)
                     ; (i = i1) → vertex s })
      (vertex (ua-unglue (e gb) i s))
  backward (R.petal (fsuc (fsuc ())) i , s)

  abstract
    backward-forward : (x : Graph) → backward (forward x) ≡ x
    backward-forward (vertex s) = refl
    backward-forward (edge s ga i) j =
      hcomp (λ k → λ { (i = i0) → edge s ga (~ k)
                       ; (i = i1) → vertex (e ga .fst s)
                       ; (j = i1) → edge s ga (i ∨ ~ k) })
        (vertex (ua-unglue (e ga) i (ua-gluePt (e ga) i s)))
    backward-forward (edge s gb i) j =
      hcomp (λ k → λ { (i = i0) → edge s gb (~ k)
                       ; (i = i1) → vertex (e gb .fst s)
                       ; (j = i1) → edge s gb (i ∨ ~ k) })
        (vertex (ua-unglue (e gb) i (ua-gluePt (e gb) i s)))

  private
    glue-square : {A B : Type₀} (d : A ≃ B)
      → SquareP (λ i k → ua d i → ua d (i ∨ ~ k))
          (λ k x → ua-gluePt d (~ k) x) (λ k x → x)
          (λ i x → ua-unglue d i x) (λ i x → x)
    glue-square d i k x = ua-glue d (i ∨ ~ k)
      (λ { ((i ∨ ~ k) = i0) → x }) (inS (ua-unglue d i x))

  abstract
    forward-backward : (x : Total) → forward (backward x) ≡ x
    forward-backward (R.root , s) = refl
    forward-backward (R.petal fzero i , s) j =
      comp (λ _ → Total)
        (λ k → λ { (i = i0) → R.petal fzero (~ k) , ua-gluePt (e ga) (~ k) s
                 ; (i = i1) → R.root , s
                 ; (j = i1) → R.petal fzero (i ∨ ~ k) , glue-square (e ga) i k s })
        (R.root , ua-unglue (e ga) i s)
    forward-backward (R.petal (fsuc fzero) i , s) j =
      comp (λ _ → Total)
        (λ k → λ { (i = i0) → R.petal (fsuc fzero) (~ k) , ua-gluePt (e gb) (~ k) s
                 ; (i = i1) → R.root , s
                 ; (j = i1) → R.petal (fsuc fzero) (i ∨ ~ k) , glue-square (e gb) i k s })
        (R.root , ua-unglue (e gb) i s)
    forward-backward (R.petal (fsuc (fsuc ())) i , s)

  flatten : Graph ≃ Total
  flatten = isoToEquiv (iso forward backward forward-backward backward-forward)

  over : (x : Graph) → fst (forward x) ≡ project x
  over (vertex s) = refl
  over (edge s ga i) = refl
  over (edge s gb i) = refl

-- A specified set-family and specified dependent lifts. Setness is
-- used ONLY for uniqueness of dependent edge paths, not for the graph.
module SetFamily (S : Type₀) (e : Generator → S ≃ S)
  (F : R.Rose twoGenerators → Type₀)
  (setF : (x : R.Rose twoGenerators) → isSet (F x))
  (sheets : S ≃ F R.root)
  (liftEdge : (s : S) (g : Generator)
    → PathP (λ i → F (basePetal g i))
        (equivFun sheets s) (equivFun sheets (equivFun (e g) s))) where

  module N = Normalized S e

  comparison : (x : R.Rose twoGenerators) → N.Family x ≃ F x
  comparison R.root = sheets
  comparison (R.petal fzero i) = ua-equiv-family (e ga)
    (λ t → F (R.petal fzero t)) sheets sheets (λ s → liftEdge s ga) i
  comparison (R.petal (fsuc fzero) i) = ua-equiv-family (e gb)
    (λ t → F (R.petal (fsuc fzero) t)) sheets sheets (λ s → liftEdge s gb) i
  comparison (R.petal (fsuc (fsuc ())) i)

  totalEquiv : N.Graph ≃ Σ (R.Rose twoGenerators) F
  totalEquiv = compEquiv N.flatten (Σ-cong-equiv-snd comparison)

  compareTo : N.Total → Σ (R.Rose twoGenerators) F
  compareTo (x , s) = x , equivFun (comparison x) s

  compareFrom : Σ (R.Rose twoGenerators) F → N.Total
  compareFrom (x , s) = x , invEq (comparison x) s

  lowerGraph : Σ (R.Rose twoGenerators) F → N.Graph
  lowerGraph y = N.backward (compareFrom y)

  abstract
    comparison-section : (y : Σ (R.Rose twoGenerators) F)
      → compareTo (compareFrom y) ≡ y
    comparison-section (x , s) i = x , secEq (comparison x) s i

    comparison-retraction : (y : N.Total)
      → compareFrom (compareTo y) ≡ y
    comparison-retraction (x , s) i = x , retEq (comparison x) s i

  -- The forward map has the prescribed dependent edge, not an opaque
  -- map obtained from an abstract equivalence.
  liftGraph : N.Graph → Σ (R.Rose twoGenerators) F
  liftGraph (vertex s) = R.root , equivFun sheets s
  liftGraph (edge s g i) = basePetal g i , liftEdge s g i

  abstract
    liftGraph-comparison : (x : N.Graph) → liftGraph x ≡ equivFun totalEquiv x
    liftGraph-comparison (vertex s) = refl
    liftGraph-comparison (edge s ga i) j = R.petal fzero i ,
      isOfHLevelPathP' 1 (setF R.root) _ _
        (liftEdge s ga)
        (λ t → equivFun (comparison (R.petal fzero t)) (ua-gluePt (e ga) t s)) j i
    liftGraph-comparison (edge s gb i) j = R.petal (fsuc fzero) i ,
      isOfHLevelPathP' 1 (setF R.root) _ _
        (liftEdge s gb)
        (λ t → equivFun (comparison (R.petal (fsuc fzero) t)) (ua-gluePt (e gb) t s)) j i

    lower-lift : (x : N.Graph) → lowerGraph (liftGraph x) ≡ x
    lower-lift x = cong lowerGraph (liftGraph-comparison x)
      ∙ cong N.backward (comparison-retraction (N.forward x))
      ∙ N.backward-forward x

    lift-lower : (y : Σ (R.Rose twoGenerators) F) → liftGraph (lowerGraph y) ≡ y
    lift-lower y = liftGraph-comparison (lowerGraph y)
      ∙ cong compareTo (N.forward-backward (compareFrom y))
      ∙ comparison-section y

    liftGraph-isEquiv : isEquiv liftGraph
    liftGraph-isEquiv = subst isEquiv (sym (funExt liftGraph-comparison)) (totalEquiv .snd)

  liftGraph-over : (x : N.Graph) → fst (liftGraph x) ≡ project x
  liftGraph-over (vertex s) = refl
  liftGraph-over (edge s g i) = refl
