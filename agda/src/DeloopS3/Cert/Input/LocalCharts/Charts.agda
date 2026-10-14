{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.LocalCharts.Charts where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (suc)
import Cubical.Data.Int as Z
import Cubical.Data.SumFin as SF
import DeloopS3.Cert.Perm as P
open import DeloopS3.Cert.Input.Model
open import DeloopS3.Cert.Input.LocalCharts.Actual
open import DeloopS3.Cert.Input.LocalCharts.Index
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R

-- Only reassociations and the supplied fibrewise equivalences. In
-- particular the Kind coordinate and the unchanged fibre circle survive.
indexedCharts : {I K U : Type₀} {J : K → Type₀} {F : K → U → Type₀}
  → (Σ K J) ≃ I → ((k : K) → (J k × U) ≃ Σ U (F k))
  → (I × U) ≃ Σ (K × U) (λ z → F (z .fst) (z .snd))
indexedCharts index charts .fst (b , u) =
  (invEq index b .fst , equivFun (charts (invEq index b .fst)) (invEq index b .snd , u) .fst) ,
  equivFun (charts (invEq index b .fst)) (invEq index b .snd , u) .snd
indexedCharts {U = U} index charts .snd =
  compEquiv (≃-× (invEquiv index) (idEquiv U))
    (compEquiv Σ-assoc-≃
      (compEquiv (Σ-cong-equiv-snd charts) (invEquiv Σ-assoc-≃))) .snd

productChart : {J U V : Type₀} {F : U → Type₀}
  → (J × U) ≃ Σ U F → (J × (U × V)) ≃ Σ (U × V) (λ z → F (z .fst))
productChart chart .fst (b , u , t) =
  (equivFun chart (b , u) .fst , t) , equivFun chart (b , u) .snd
productChart {J = J} {U = U} {V = V} {F = F} chart .snd = compEquiv (invEquiv Σ-assoc-≃)
  (compEquiv (≃-× chart (idEquiv V)) rearrange) .snd
  where
  rearrange : ((Σ U F) × V) ≃ Σ (U × V) (λ z → F (z .fst))
  rearrange = isoToEquiv (iso (λ { ((u , q) , t) → (u , t) , q })
    (λ { ((u , t) , q) → (u , q) , t }) (λ _ → refl) (λ _ → refl))

coreChart : (c : ShortCase) → R.R (S₀ c) ≃ R.Span.R (FlatSpan c)
coreChart c = indexedCharts (allBoundaryIndex c) (core-circles c)

overlapChart : (c : ShortCase) → R.O (S₀ c) ≃ R.Span.O (FlatSpan c)
overlapChart c = indexedCharts (allBoundaryIndex c)
  (λ k → productChart (boundary-circles c k))

startSheet : (c : ShortCase) → R.FaceIx (S₀ c) → Sh c
startSheet c b = startOf c (kindAt c b) (localAt c b)

-- All model basepoints here reduce to embase, so no hidden choice of a
-- path or of a sheet is made. startOf is the checked first orbit entry.
boundaryOrigin : (c : ShortCase) → R.FaceIx (S₀ c) → R.Span.O (FlatSpan c)
boundaryOrigin c b = (Ch.kind (bdAllAt c b) , R.0C , R.0C) , sheet c (startSheet c b)

coreOrigin : (c : ShortCase) → R.FaceIx (S₀ c) → R.Span.R (FlatSpan c)
coreOrigin c b = (Ch.kind (bdAllAt c b) , R.0C) , sheet c (startSheet c b)

abstract
  overlap-projection : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u t : R.C)
    → fst (equivFun (overlapChart c) (b , u , t))
      ≡ (Ch.kind (bdAllAt c b) , R.mulC (Z.pos (Ch.orbitLength (bdAllAt c b))) u , t)
  overlap-projection c b u t i = kind-index (face-data c b) i ,
    R.mulC (Z.pos (length-index (face-data c b) i)) u , t

  right-projection : (c : ShortCase) (b : R.FaceIx (S₀ c)) (u : R.C)
    → fst (equivFun (coreChart c) (b , u))
      ≡ (Ch.kind (bdAllAt c b) , R.mulC (Z.pos (Ch.orbitLength (bdAllAt c b))) u)
  right-projection c b u i = kind-index (face-data c b) i ,
    R.mulC (Z.pos (length-index (face-data c b) i)) u

  overlap-base : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → equivFun (overlapChart c) (b , R.0C , R.0C) ≡ boundaryOrigin c b
  overlap-base c b i = (kind-index (face-data c b) i , R.0C , R.0C) ,
    boundary-fibre-base c (kindAt c b) (localAt c b) i

  right-base : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → equivFun (coreChart c) (b , R.0C) ≡ coreOrigin c b
  right-base c b i = (kind-index (face-data c b) i , R.0C) ,
    core-fibre-base c (kindAt c b) (localAt c b) i


abstract
  startSheet-value : (c : ShortCase) (b : R.FaceIx (S₀ c))
    → SF.toℕ (startSheet c b) ≡ P.nth 0 (Ch.orbit (bdAllAt c b)) 0
  startSheet-value c b = startOf-value c (kindAt c b) (localAt c b)
    ∙ cong (λ bd → P.nth 0 (Ch.orbit bd) 0) (boundary-index (face-data c b))
