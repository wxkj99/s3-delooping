{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Recognition.Representative where

-- Sphere representatives and torsion extensions, with all choices inside
-- propositional truncation.
open import DeloopS3.Bridge.Recognition.Hurewicz public using
  (hurewicz-representative ; hurewicz-equality→merely-homotopy)
open import DeloopS3.Bridge.Recognition.Torsion public using
  (multiple ; reflect-multiple-zero ; precompose-degree3-class ; extend-moore3-from-torsion)

