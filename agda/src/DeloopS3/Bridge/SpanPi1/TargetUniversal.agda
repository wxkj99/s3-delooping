{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.TargetUniversal where

-- The full mapping-space universal property at the torus seams.
-- A seam into a 1-type has exactly a point path and its two generator
-- squares.  There is no extra datum or condition for the torus prism.
-- TargetGeneration uses the dependent path version of this pushout
-- universal property to extract finite words, rather than merely
-- asserting the expected presentation of an abstract group.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Equiv.Properties using (preCompEquiv)
open import Cubical.Foundations.Isomorphism
open import Cubical.Foundations.HLevels hiding (extend)
open import Cubical.Data.Sigma
import Cubical.HITs.PropositionalTruncation as PT
import Cubical.HITs.Truncation as T
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Model
open import DeloopS3.Cert.Input.Model.Torus using (module BasedTorus)
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Move.CancelLoopCell using (module PushoutUP)
open import DeloopS3.Bridge.SpanPi1.Connected using (circle-paths)

module TorusUniversal (Y : Type₀) (gpd : isGroupoid Y) (f g : R.T² → Y) where
  Squares : (p : f (R.0C , R.0C) ≡ g (R.0C , R.0C)) → Type₀
  Squares p =
    PathP (λ i → f (hC i , R.0C) ≡ g (hC i , R.0C)) p p
    × PathP (λ i → f (R.0C , hC i) ≡ g (R.0C , hC i)) p p

  Data : Type₀
  Data = Σ[ p ∈ (f (R.0C , R.0C) ≡ g (R.0C , R.0C)) ] Squares p

  restrict : ((t : R.T²) → f t ≡ g t) → Data
  restrict s = s (R.0C , R.0C) , (λ i → s (hC i , R.0C)) , (λ i → s (R.0C , hC i))

  extend : Data → (t : R.T²) → f t ≡ g t
  extend (p , us , ts) = BasedTorus.seam gpd f g p us ts

  abstract
    squares-prop : (p : f (R.0C , R.0C) ≡ g (R.0C , R.0C)) → isProp (Squares p)
    squares-prop p = isProp×
      (isOfHLevelPathP' 1 (gpd _ _) p p)
      (isOfHLevelPathP' 1 (gpd _ _) p p)

    restrict-extend : (d : Data) → restrict (extend d) ≡ d
    restrict-extend (p , us , ts) = Σ≡Prop squares-prop (BasedTorus.seam-base gpd f g p us ts)

    extend-restrict : (s : (t : R.T²) → f t ≡ g t) → extend (restrict s) ≡ s
    extend-restrict s = funExt λ { (u , t) →
      PT.rec (gpd (f (u , t)) (g (u , t)) (extend (restrict s) (u , t)) (s (u , t)))
        (λ qu → PT.rec (gpd (f (u , t)) (g (u , t)) (extend (restrict s) (u , t)) (s (u , t)))
          (λ qt → subst (λ z → extend (restrict s) z ≡ s z)
            (λ i → qu i , qt i)
            (BasedTorus.seam-base gpd f g (s (R.0C , R.0C))
              (λ i → s (hC i , R.0C)) (λ i → s (R.0C , hC i))))
          (circle-paths t)) (circle-paths u) }

    seamUP : ((t : R.T²) → f t ≡ g t) ≃ Data
    seamUP = isoToEquiv (iso restrict extend restrict-extend extend-restrict)

module SeifertUniversal (c : ShortCase) (Y : Type₀) (gpd : isGroupoid Y) where
  private
    left = R.Span.left (Model.BaseSpan c)
    right = R.Span.right (Model.BaseSpan c)

  -- Vertex maps and, for each of the three torus components, precisely
  -- the point/loop compatibility data of its two displayed generators.
  Data : Type₀
  Data = Σ[ l ∈ (Model.Γ × R.C → Y) ] Σ[ r ∈ (Ch.Kind × R.C → Y) ]
    ((k : Ch.Kind) → TorusUniversal.Data Y gpd
      (λ t → l (left (k , t))) (λ t → r (right (k , t))))

  private
    seam-components : (l : Model.Γ × R.C → Y) (r : Ch.Kind × R.C → Y)
      → ((a : Ch.Kind × R.T²) → l (left a) ≡ r (right a))
        ≃ ((k : Ch.Kind) → TorusUniversal.Data Y gpd
          (λ t → l (left (k , t))) (λ t → r (right (k , t))))
    seam-components l r = compEquiv
      (isoToEquiv (iso (λ s k t → s (k , t)) (λ s a → s (fst a) (snd a))
        (λ _ → refl) (λ _ → refl)))
      (equivΠCod (λ k → TorusUniversal.seamUP Y gpd
        (λ t → l (left (k , t))) (λ t → r (right (k , t)))))

  abstract
    model-UP : (Model.M_G c → Y) ≃ Data
    model-UP = compEquiv (PushoutUP.pushoutUP left right Y)
      (Σ-cong-equiv-snd λ l → Σ-cong-equiv-snd λ r → seam-components l r)

    model-1trunc-UP : (T.hLevelTrunc 3 (Model.M_G c) → Y) ≃ Data
    model-1trunc-UP = compEquiv (isoToEquiv (T.univTrunc 3 {B = Y , gpd})) model-UP

    literal-UP : (Model.M-original c → Y) ≃ Data
    literal-UP = compEquiv (preCompEquiv {C = Y} (invEquiv (Model.originalTotalEquiv c))) model-UP

    literal-1trunc-UP : (T.hLevelTrunc 3 (Model.M-original c) → Y) ≃ Data
    literal-1trunc-UP = compEquiv (isoToEquiv (T.univTrunc 3 {B = Y , gpd})) literal-UP

-- Reduce the vertex maps themselves to point/loop data.  The two loops
-- in the rose have one common point.  For the product with the fibre
-- circle each carries the commuting square; there is no higher datum.
open import Cubical.Data.SumFin using (Fin)
open import Cubical.Foundations.Equiv.Properties using (congEquiv)
open import DeloopS3.Move.CancelLoopCell using (module CircleUP)
open import DeloopS3.Cover.Orientation.CircleModel using (S¹≃C)

module VertexUniversal (Y : Type₀) where
  CircleData : Type₀
  CircleData = Σ[ b ∈ Y ] b ≡ b

  circleUP : (R.C → Y) ≃ CircleData
  circleUP = compEquiv (preCompEquiv {C = Y} S¹≃C) (CircleUP.circleUP (λ _ → Y))

  RoseData : (Z : Type₀) → Type₀
  RoseData Z = Σ[ b ∈ Z ] (Fin 2 → b ≡ b)

  roseUP : (Z : Type₀) → (Model.Γ → Z) ≃ RoseData Z
  roseUP Z = isoToEquiv (iso
    (λ f → f R.root , λ k → cong f (R.petal k))
    (λ { (b , ps) → R.roseRec b ps })
    (λ _ → refl) (λ f → funExt (η f)))
    where
    η : (f : Model.Γ → Z) (v : Model.Γ)
      → R.roseRec (f R.root) (λ k → cong f (R.petal k)) v ≡ f v
    η f R.root = refl
    η f (R.petal k i) = refl

  CommuteData : CircleData → Type₀
  CommuteData (b , h) = Σ[ p ∈ (b ≡ b) ] PathP (λ i → p i ≡ p i) h h

  LeftData : Type₀
  LeftData = Σ[ bh ∈ CircleData ] (Fin 2 → CommuteData bh)

  RightData : Type₀
  RightData = Ch.Kind → CircleData

  abstract
    leftUP : (Model.Γ × R.C → Y) ≃ LeftData
    leftUP = compEquiv
      (isoToEquiv (iso (λ f a t → f (a , t)) (λ f a → f (fst a) (snd a))
        (λ _ → refl) (λ _ → refl)))
      (compEquiv (roseUP (R.C → Y))
        (Σ-cong-equiv circleUP (λ f → equivΠCod λ _ →
          compEquiv (congEquiv circleUP) (invEquiv ΣPath≃PathΣ))))

    rightUP : (Ch.Kind × R.C → Y) ≃ RightData
    rightUP = compEquiv
      (isoToEquiv (iso (λ f k t → f (k , t)) (λ f a → f (fst a) (snd a))
        (λ _ → refl) (λ _ → refl)))
      (equivΠCod (λ _ → circleUP))

module PointLoopUniversal (c : ShortCase) (Y : Type₀) (gpd : isGroupoid Y) where
  private
    module V = VertexUniversal Y
    module S = SeifertUniversal c Y gpd

  Relations : (Model.Γ × R.C → Y) → (Ch.Kind × R.C → Y) → Type₀
  Relations l r = (k : Ch.Kind) → TorusUniversal.Data Y gpd
    (λ t → l (R.Span.left (Model.BaseSpan c) (k , t)))
    (λ t → r (R.Span.right (Model.BaseSpan c) (k , t)))

  -- Entirely finite-dimensional point/loop data: four vertex points,
  -- the graph/fibre/core loops, the three tree edges, and the generator
  -- squares. TargetRelations identifies their based group equations as
  -- x²=y³=h, z=y⁻¹x, z^n=h. TargetGeneration removes the tree edges from
  -- word generation without choosing paths from connectedness.
  Data : Type₀
  Data = Σ[ l ∈ V.LeftData ] Σ[ r ∈ V.RightData ]
    Relations (invEq V.leftUP l) (invEq V.rightUP r)

  private
    to-seams : Data ≃ S.Data
    to-seams = compEquiv
      (Σ-cong-equiv-fst {B = λ l → Σ[ r ∈ V.RightData ] Relations l (invEq V.rightUP r)}
        (invEquiv V.leftUP))
      (Σ-cong-equiv-snd λ l → Σ-cong-equiv-fst {B = Relations l} (invEquiv V.rightUP))

  abstract
    model-point-loop-UP : (T.hLevelTrunc 3 (Model.M_G c) → Y) ≃ Data
    model-point-loop-UP = compEquiv S.model-1trunc-UP (invEquiv to-seams)

    literal-point-loop-UP : (T.hLevelTrunc 3 (Model.M-original c) → Y) ≃ Data
    literal-point-loop-UP = compEquiv S.literal-1trunc-UP (invEquiv to-seams)
