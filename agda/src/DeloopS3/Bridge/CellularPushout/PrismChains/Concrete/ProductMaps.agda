{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductMaps where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Data.Nat using (ℕ ; suc)
open import Cubical.Data.Fin using (Fin)
open import Cubical.Data.Bool using (Bool)
open import Cubical.Data.Unit using (tt)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.HITs.Susp using (Susp ; north)
open import Cubical.HITs.Pushout using (cofib ; inl ; inr)
open import Cubical.HITs.SphereBouquet using (SphereBouquet)
open import Cubical.HITs.Wedge using (⋁↪)
open import Cubical.CW.Map using (cellMap)
open import DeloopS3.Bridge.ComponentHomology.ProductCells using (module RoseProduct)
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.Wedge
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.ProductCharts
open import DeloopS3.Bridge.CellularPushout.PrismChains.Concrete.Constructors

module ProductMap (n m : ℕ)
  (h : Susp (RoseProduct.Vertices n) → Susp (RoseProduct.Vertices m))
  (h₀ : h north ≡ north) where
  private
    module S = RoseProduct n
    module T = RoseProduct m
    module CS = Chart n
    module CT = Chart m
    wlift = wedge-lift north north (north {A = Bool}) h h₀

  product : CS.Product → CT.Product
  product (x , y) = h x , y

  edges : SphereBouquet 1 (Fin (suc n)) → SphereBouquet 1 (Fin (suc m))
  edges = fst T.target-chart ∘ WedgeLift.map wlift ∘ invEq S.target-chart

  top : cofib S.attaching → cofib T.attaching
  top = invEq CT.top-chart ∘ product ∘ fst CS.top-chart

  abstract
    edge-point : edges (inl tt) ≡ inl tt
    edge-point = cong (fst T.target-chart ∘ WedgeLift.map wlift)
      CS.target-inverse-point
      ∙ cong (fst T.target-chart) (WedgeLift.point wlift)
      ∙ CT.target-point

    edge-square : (x : SphereBouquet 1 (Fin (suc n)))
      → inr (edges x) ≡ top (inr x)
    edge-square x = sym (retEq CT.top-chart (inr (edges x)))
      ∙ cong (invEq CT.top-chart)
        (CT.on-edge (edges x)
          ∙ cong ⋁↪ (retEq T.target-chart (WedgeLift.map wlift (invEq S.target-chart x)))
          ∙ WedgeLift.square wlift (invEq S.target-chart x)
          ∙ cong product (sym (CS.on-edge x)))

    top-square : (x : cofib S.attaching)
      → fst CT.top-chart (top x) ≡ product (fst CS.top-chart x)
    top-square x = secEq CT.top-chart (product (fst CS.top-chart x))

  private
    module Build = TwoToTwo S.attaching T.attaching edges top edge-point edge-square

  cellular : cellMap S.skeleton T.skeleton
  cellular = Build.cellular

  open Build public using (realise-top)
