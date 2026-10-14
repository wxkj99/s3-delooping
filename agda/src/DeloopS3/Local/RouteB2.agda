{-# OPTIONS --cubical --safe #-}
module DeloopS3.Local.RouteB2 where

-- Localization preserves fibres over simply connected bases and compares
-- localized path spaces with paths in the localization, retaining unit laws.
-- RouteB1 and the finite power-square derivative supply the generic inputs;
-- no connectivity of total spaces or telescope theorem is required.
open import DeloopS3.Local.RouteB2.Common public
open import DeloopS3.Local.RouteB2.Derivative public
open import DeloopS3.Local.RouteB2.Finite public
  using (connected-mere-path ; pointed-loop→raw ; connected-loop-reflection ;
         set-local ; one-type-separated ; unit-on-local)
open import DeloopS3.Local.RouteB2.Families public
  using (SC-circle-merely-constant ; local-Σ-SC ; Σ-unit-local-equivalence)
open import DeloopS3.Local.RouteB2.Fibers public
  using (local-equivalence-from-unit ; fiber-unit)
open import DeloopS3.Local.RouteB2.Loops public
  using (path-comparison ; path-comparison-β ; L∙ ; η∙ ; loop-comparison ;
         localize-loops-β ; unit-loop-normalize)
import DeloopS3.Local.RouteB1 as B1
import DeloopS3.Local.RouteB2.Finite as Finite
import DeloopS3.Local.RouteB2.Families as Families
import DeloopS3.Local.RouteB2.Fibers as Fibers
import DeloopS3.Local.RouteB2.Loops as Loops

checked-RouteB1 : RouteB1-Hypotheses
RouteB1-Hypotheses.susp-locality checked-RouteB1 = B1.susp-locality
RouteB1-Hypotheses.local-fiber checked-RouteB1 = B1.local-fiber
RouteB1-Hypotheses.local-universe-separated checked-RouteB1 = B1.local-universe-separated
RouteB1-Hypotheses.S-unit-base-change checked-RouteB1 = B1.S-unit-base-change

open Finite.Reflection checked-RouteB1 loop-power-derivative public
open Families.Total checked-RouteB1 loop-power-derivative public
open Fibers.Preservation checked-RouteB1 loop-power-derivative public
open Loops.Loops fiber-unit-local-equivalence public
