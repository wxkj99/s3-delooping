{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Input.Graph.Core where

open import Cubical.Foundations.Prelude
open import Cubical.Data.SumFin using (fzero; fsuc)
open import DeloopS3.Cert.Interpret.Syntax using (twoGenerators)
import DeloopS3.Cert.Interpret.Realization as R

data Generator : Type₀ where
  ga gb : Generator

-- The untruncated graph of two directed endomorphisms.
-- In particular an involution still has two distinct positive lifts.
data ActionGraph (S : Type₀) (next : S → Generator → S) : Type₀ where
  vertex : S → ActionGraph S next
  edge : (s : S) (g : Generator) → vertex s ≡ vertex (next s g)

basePetal : Generator → Path (R.Rose twoGenerators) R.root R.root
basePetal ga = R.petal fzero
basePetal gb = R.petal (fsuc fzero)

project : {S : Type₀} {next : S → Generator → S}
  → ActionGraph S next → R.Rose twoGenerators
project (vertex s) = R.root
project (edge s g i) = basePetal g i
