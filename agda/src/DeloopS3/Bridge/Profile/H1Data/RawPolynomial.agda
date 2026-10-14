{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.H1Data.RawPolynomial where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Algebra.CommRing
open import Cubical.Tactics.CommRingSolver

-- Reify before specializing to integers: integer subtraction otherwise
-- computes through 1-n and obscures the polynomial from the tactic.
module Polynomial {ℓ} (R : CommRing ℓ) where
  open CommRingStr (snd R)
  private
    V = fst R
    two = 1r + 1r
  Pair : Type ℓ
  Pair = V × V
  Source : Type ℓ
  Source = (V × V × V) × (V × V × V)
  Target : Type ℓ
  Target = (V × V) × V × V × V × V
  plusP : Pair → Pair → Pair
  plusP (x , y) (z , w) = x + z , y + w
  plusS : Source → Source → Source
  plusS ((a , b , c) , d , e , f) ((a' , b' , c') , d' , e' , f') =
    (a + a' , b + b' , c + c') , d + d' , e + e' , f + f'
  plusT : Target → Target → Target
  plusT ((a , b) , h , x , y , z) ((a' , b') , h' , x' , y' , z') =
    (a + a' , b + b') , h + h' , x + x' , y + y' , z + z'
  negT : Target → Target
  negT ((a , b) , h , x , y , z) = ((- a) , (- b)) , (- h) , (- x) , (- y) , (- z)
  raw : V → V → Source → Target
  raw q n ((u₁ , u₂ , u₃) , h₁ , h₂ , h₃) =
    (u₁ - u₃ , u₂ - u₃) , (h₁ + (h₂ + h₃)) ,
    (- (u₁ + two · h₁)) , (- (u₂ + q · h₂)) , (- ((1r - n) · u₃ + n · h₃))
  residual : V → V → Pair → Pair
  residual q n (s , t) = two · s + (two - n) · t , (- q) · s + n · t
  project : Target → Pair
  project ((a , b) , h , x , y , z) = a + two · h + x + z , b + y - z
  include : Pair → Target
  include (x , y) = (0r , 0r) , 0r , x , y , 0r
  column : Source → Pair
  column ((u₁ , u₂ , u₃) , h₁ , h₂ , h₃) = h₂ , h₃ - u₃
  columnLift : V → Pair → Source
  columnLift n (s , t) = ((- (n · t)) , (- (n · t)) , (- (n · t))) ,
    ((- s) + (n - 1r) · t) , s , ((1r - n) · t)
  correct : Target → Source
  correct ((a , b) , h , x , y , z) = (a - z , b - z , - z) , (h + z) , 0r , - z

  abstract
    project-add : (v w : Target) → project (plusT v w) ≡ plusP (project v) (project w)
    project-add ((a , b) , h , x , y , z) ((a' , b') , h' , x' , y' , z') =
      ΣPathP ((solve! R) , (solve! R))
    column-add : (v w : Source) → column (plusS v w) ≡ plusP (column v) (column w)
    column-add ((a , b , c) , d , e , f) ((a' , b' , c') , d' , e' , f') =
      ΣPathP (refl , (solve! R))
    lift-add : (n : V) (v w : Pair) → columnLift n (plusP v w) ≡ plusS (columnLift n v) (columnLift n w)
    lift-add n (s , t) (s' , t') = ΣPathP
      (ΣPathP ((solve! R) , ΣPathP ((solve! R) , (solve! R))) ,
        ΣPathP ((solve! R) , ΣPathP (refl , (solve! R))))
    project-square : (q n : V) (u : Source)
      → residual q n (column u) ≡ project (raw q n u)
    project-square q n ((u₁ , u₂ , u₃) , h₁ , h₂ , h₃) =
      ΣPathP ((solve! R) , (solve! R))
    include-square : (q n : V) (v : Pair) → raw q n (columnLift n v) ≡ include (residual q n v)
    include-square q n (s , t) =
      ΣPathP (ΣPathP ((solve! R) , (solve! R)) ,
        ΣPathP ((solve! R) , ΣPathP ((solve! R) , ΣPathP ((solve! R) , (solve! R)))))
    project-include : (v : Pair) → project (include v) ≡ v
    project-include (x , y) = ΣPathP ((solve! R) , (solve! R))
    raw-correct : (q n : V) (v : Target)
      → raw q n (correct v) ≡ plusT v (negT (include (project v)))
    raw-correct q n ((a , b) , h , x , y , z) =
      ΣPathP (ΣPathP ((solve! R) , (solve! R)) ,
        ΣPathP ((solve! R) , ΣPathP ((solve! R) , ΣPathP ((solve! R) , (solve! R)))))

    source-row-reduction : (n s t : V)
      → (0r · (two · s + (two - n) · t) + (- 1r) · ((- two) · s + n · t) ,
          1r · (two · s + (two - n) · t) + 1r · ((- two) · s + n · t))
        ≡ (two · s + (- n) · t , 0r · s + two · t)
    source-row-reduction _ _ _ = ΣPathP ((solve! R) , (solve! R))
