{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Graph.Total where

-- Flatten the coset family using the explicit sheet coordinates and actions.
open import Cubical.Foundations.Prelude hiding (lift; lower)
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.HITs.EilenbergMacLane1.Base using (embase; emloop)
open import DeloopS3.Cert.Input.Model using (graphMark)
open import DeloopS3.Cert.Input.Sheets using (SheetData; sheet-data)
open import DeloopS3.Cert.Input.Graph.Base
open import DeloopS3.Cert.Input.Graph.Core using (basePetal)
open import DeloopS3.Cert.Input.Graph.Family using (module SetFamily)
open import DeloopS3.Cover.Cosets using (CosetFamily; cosetPoint)
import DeloopS3.Cert.Interpret.Realization as R

abstract
  nextSheet-isEquiv : (c : ShortCase) (g : Generator)
    → isEquiv (λ i → nextSheet c i g)
  nextSheet-isEquiv c g = subst isEquiv
    (sym (funExt (λ i → nextSheet-action c i g)))
    (actEquiv (certOf c) (rawChecks c) (positive g) .snd)

nextEquiv : (c : ShortCase) → Generator → Sh c ≃ Sh c
nextEquiv c g = (λ i → nextSheet c i g) , nextSheet-isEquiv c g

GraphFamily : (c : ShortCase) → Γ → Type₀
GraphFamily c x = CosetFamily (j c) (graphMark c x) .fst

GraphTotal : ShortCase → Type₀
GraphTotal c = Σ Γ (GraphFamily c)

-- Parameterized form also works with any other checked SheetData.
module WithSheets (c : ShortCase) (d : SheetData c) where
  dependentEdge : (s : Sh c) (g : Generator)
    → PathP (λ t → GraphFamily c (basePetal g t))
        (equivFun (SheetData.e d) s)
        (equivFun (SheetData.e d) (nextSheet c s g))
  dependentEdge s ga = toPathP
    (SheetData.square d s a+
      ∙ cong (equivFun (SheetData.e d)) (sym (nextSheet-action c s ga)))
  dependentEdge s gb = toPathP
    (SheetData.square d s b+
      ∙ cong (equivFun (SheetData.e d)) (sym (nextSheet-action c s gb)))

  module Flat = SetFamily (Sh c) (nextEquiv c) (GraphFamily c)
    (λ x → CosetFamily (j c) (graphMark c x) .snd)
    (SheetData.e d) dependentEdge

  lift : LiftedGraph c → GraphTotal c
  lift = Flat.liftGraph

  lower : GraphTotal c → LiftedGraph c
  lower = Flat.lowerGraph

  abstract
    lift-isEquiv : isEquiv lift
    lift-isEquiv = Flat.liftGraph-isEquiv

    lower-lift : (x : LiftedGraph c) → lower (lift x) ≡ x
    lower-lift = Flat.lower-lift

    lift-lower : (y : GraphTotal c) → lift (lower y) ≡ y
    lift-lower = Flat.lift-lower

  over : (x : LiftedGraph c) → fst (lift x) ≡ projectGraph c x
  over = Flat.liftGraph-over

  lift-vertex : (s : Sh c) → lift (vertex s) ≡ (R.root , equivFun (SheetData.e d) s)
  lift-vertex s = refl

  lower-vertex : (u : GraphFamily c R.root)
    → lower (R.root , u) ≡ vertex (invEq (SheetData.e d) u)
  lower-vertex u = refl

liftToTotal : (c : ShortCase) → LiftedGraph c → GraphTotal c
liftToTotal c = WithSheets.lift c (sheet-data c)

liftFromTotal : (c : ShortCase) → GraphTotal c → LiftedGraph c
liftFromTotal c = WithSheets.lower c (sheet-data c)

abstract
  liftToTotal-isEquiv : (c : ShortCase) → isEquiv (liftToTotal c)
  liftToTotal-isEquiv c = WithSheets.lift-isEquiv c (sheet-data c)

  liftFromTotal-liftToTotal : (c : ShortCase) (x : LiftedGraph c)
    → liftFromTotal c (liftToTotal c x) ≡ x
  liftFromTotal-liftToTotal c = WithSheets.lower-lift c (sheet-data c)

  liftToTotal-liftFromTotal : (c : ShortCase) (x : GraphTotal c)
    → liftToTotal c (liftFromTotal c x) ≡ x
  liftToTotal-liftFromTotal c = WithSheets.lift-lower c (sheet-data c)

liftToTotal-over : (c : ShortCase) (x : LiftedGraph c)
  → fst (liftToTotal c x) ≡ projectGraph c x
liftToTotal-over c = WithSheets.over c (sheet-data c)

liftToTotal-vertex : (c : ShortCase) (s : Sh c)
  → liftToTotal c (vertex s) ≡ (R.root , cosetPoint (j c) (repElement c s))
liftToTotal-vertex c s i = R.root , SheetData.at-rep (sheet-data c) s i

liftToTotal-edge : (c : ShortCase) (s : Sh c) (g : Generator)
  → cong (liftToTotal c) (edge s g)
    ≡ (λ t → basePetal g t , WithSheets.dependentEdge c (sheet-data c) s g t)
liftToTotal-edge c s g = refl

liftFromTotal-vertex : (c : ShortCase) (u : GraphFamily c R.root)
  → liftFromTotal c (R.root , u) ≡ vertex (invEq (SheetData.e (sheet-data c)) u)
liftFromTotal-vertex c = WithSheets.lower-vertex c (sheet-data c)
