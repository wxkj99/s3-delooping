{-# OPTIONS --cubical --safe --guardedness --lossy-unification #-}
module DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Components where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Data.Int using (ℤ ; pos ; _-_)
open import Cubical.Data.Sum using (inl ; inr)
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (makeIsGroupHom ; compGroupHom)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.HITs.EilenbergMacLane1.Base using (emloop ; emloop-comp)
open import Cubical.Homotopy.Connected using (isConnected)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ)
open import DeloopS3.Bridge.CofibreHomology using (cellular-map)
open import DeloopS3.Bridge.ComponentHomology.Circle using (circleCW)
open import DeloopS3.Bridge.ComponentHomology.Finite using (graph×circleCW)
open import DeloopS3.Bridge.Profile.BaseSeifert.Geometry using (overlapCW ; fillingsCW)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Loops
  using (loop-class ; loop-natural ; loop-add ; loop-inv ; loop-rebase)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.WordPaths
  using (torus-base ; torus-u ; torus-h ; core-base ; core-base₂ ;
         core-a ; core-b ; core-h ; core-edge ; core-fibre ;
         boundary₁-u ; boundary₁-h ; boundary₂-u-conjugate ;
         boundary₃-u ; boundary₃-h ; row-u ; row-h)
import DeloopS3.Bridge.SpanPi1.Connected as Connected
open import DeloopS3.Move.CancelMinimal using (C ; 0C ; T²)
import DeloopS3.Seifert.MarkedSeifert.WEquiv.Definition as Literal

-- These are the homology groups of the literal overlap, core and fillings.
O G R : Group ℓ-zero
O = H̃ᶜʷ overlapCW 1
G = H̃ᶜʷ graph×circleCW 1
R = H̃ᶜʷ fillingsCW 1

t1 t2 t3 : T² → fst overlapCW
t1 = inl ∘ inl
t2 = inl ∘ inr
t3 = inr

c1 c2 c3 : C → fst fillingsCW
c1 = inl ∘ inl
c2 = inl ∘ inr
c3 = inr

-- The six source classes are independent of the filling parameters.
source-u1 source-u2 source-u3 source-h1 source-h2 source-h3 : fst O
source-u1 = loop-class overlapCW (t1 torus-base) (cong t1 torus-u)
source-u2 = loop-class overlapCW (t2 torus-base) (cong t2 torus-u)
source-u3 = loop-class overlapCW (t3 torus-base) (cong t3 torus-u)
source-h1 = loop-class overlapCW (t1 torus-base) (cong t1 torus-h)
source-h2 = loop-class overlapCW (t2 torus-base) (cong t2 torus-h)
source-h3 = loop-class overlapCW (t3 torus-base) (cong t3 torus-h)

core-a-class core-b-class core-h-class : fst G
core-a-class = loop-class graph×circleCW core-base core-a
core-b-class = loop-class graph×circleCW core-base core-b
core-h-class = loop-class graph×circleCW core-base core-h

abstract
  core-connected : isConnected 2 (fst graph×circleCW)
  core-connected = Connected.paths→connected core-base Connected.core-paths

private
  abstract
    circle-integer-add : (n m : ℤ)
      → loop-class circleCW 0C (emloop {Group = ℤGroup} (GroupStr._·_ (snd ℤGroup) n m))
        ≡ GroupStr._·_ (snd (H̃ᶜʷ circleCW 1))
          (loop-class circleCW 0C (emloop {Group = ℤGroup} n))
          (loop-class circleCW 0C (emloop {Group = ℤGroup} m))
    circle-integer-add n m =
      cong {A = 0C ≡ 0C} {B = λ _ → fst (H̃ᶜʷ circleCW 1)}
        (loop-class circleCW 0C) (emloop-comp ℤGroup n m)
      ∙ loop-add circleCW Connected.circle-connected 0C (emloop {Group = ℤGroup} n) (emloop {Group = ℤGroup} m)

circle-integer : GroupHom ℤGroup (H̃ᶜʷ circleCW 1)
fst circle-integer n = loop-class circleCW 0C (emloop {Group = ℤGroup} n)
snd circle-integer = makeIsGroupHom
  {A = ℤ} {B = fst (H̃ᶜʷ circleCW 1)}
  {G = snd ℤGroup}
  {f = λ n → loop-class circleCW 0C (emloop {Group = ℤGroup} n)}
  {H = snd (H̃ᶜʷ circleCW 1)} circle-integer-add

filling1-integer filling2-integer filling3-integer : GroupHom ℤGroup R
filling1-integer = compGroupHom {F = ℤGroup} {G = H̃ᶜʷ circleCW 1} {H = R} circle-integer
  (cellular-map circleCW fillingsCW 1 c1)
filling2-integer = compGroupHom {F = ℤGroup} {G = H̃ᶜʷ circleCW 1} {H = R} circle-integer
  (cellular-map circleCW fillingsCW 1 c2)
filling3-integer = compGroupHom {F = ℤGroup} {G = H̃ᶜʷ circleCW 1} {H = R} circle-integer
  (cellular-map circleCW fillingsCW 1 c3)

left-map : (p q r : ℤ) → GroupHom O G
left-map p q r = cellular-map overlapCW graph×circleCW 1
  (Literal.Seifert.allLeft p q r)

right-map : (p q r : ℤ) → GroupHom O R
right-map p q r = cellular-map overlapCW fillingsCW 1
  (Literal.Seifert.allRight p q r)

abstract
  left-u1 : (p q r : ℤ)
    → fst (left-map p q r) source-u1 ≡ core-a-class
  left-u1 p q r =
    loop-natural overlapCW graph×circleCW (Literal.Seifert.allLeft p q r)
      (t1 torus-base) (cong t1 torus-u)
    ∙ cong {A = core-base ≡ core-base} {B = λ _ → fst G}
        (loop-class graph×circleCW core-base) boundary₁-u

  left-u2 : (p q r : ℤ)
    → fst (left-map p q r) source-u2 ≡ core-b-class
  left-u2 p q r =
    loop-natural overlapCW graph×circleCW (Literal.Seifert.allLeft p q r)
      (t2 torus-base) (cong t2 torus-u)
    ∙ sym (loop-rebase graph×circleCW core-base core-base₂ core-edge
        (cong Literal.boundary₂ torus-u))
    ∙ cong {A = core-base ≡ core-base} {B = λ _ → fst G}
        (loop-class graph×circleCW core-base) boundary₂-u-conjugate

  left-u3 : (p q r : ℤ)
    → fst (left-map p q r) source-u3
      ≡ GroupStr.inv (snd G) (GroupStr._·_ (snd G) core-a-class core-b-class)
  left-u3 p q r =
    loop-natural overlapCW graph×circleCW (Literal.Seifert.allLeft p q r)
      (t3 torus-base) (cong t3 torus-u)
    ∙ cong {A = core-base ≡ core-base} {B = λ _ → fst G}
        (loop-class graph×circleCW core-base) boundary₃-u
    ∙ loop-inv graph×circleCW core-connected core-base (core-a ∙ core-b)
    ∙ cong {A = fst G} {B = λ _ → fst G} (GroupStr.inv (snd G))
        (loop-add graph×circleCW core-connected core-base core-a core-b)

  left-h1 : (p q r : ℤ)
    → fst (left-map p q r) source-h1 ≡ core-h-class
  left-h1 p q r =
    loop-natural overlapCW graph×circleCW (Literal.Seifert.allLeft p q r)
      (t1 torus-base) (cong t1 torus-h)
    ∙ cong {A = core-base ≡ core-base} {B = λ _ → fst G}
        (loop-class graph×circleCW core-base) boundary₁-h

  left-h2 : (p q r : ℤ)
    → fst (left-map p q r) source-h2 ≡ core-h-class
  left-h2 p q r =
    loop-natural overlapCW graph×circleCW (Literal.Seifert.allLeft p q r)
      (t2 torus-base) (cong t2 torus-h)
    ∙ sym (λ i → loop-class graph×circleCW (Literal.edge i , 0C)
        (core-fibre (Literal.edge i)))

  left-h3 : (p q r : ℤ)
    → fst (left-map p q r) source-h3 ≡ core-h-class
  left-h3 p q r =
    loop-natural overlapCW graph×circleCW (Literal.Seifert.allLeft p q r)
      (t3 torus-base) (cong t3 torus-h)
    ∙ cong {A = core-base ≡ core-base} {B = λ _ → fst G}
        (loop-class graph×circleCW core-base) boundary₃-h

private
  abstract
    -- The target may be disconnected: only loop naturality is used here.
    row-image : (c : C → fst fillingsCW) (s n : ℤ)
      (v : torus-base ≡ torus-base) (k : ℤ)
      → cong (Literal.row s n) v ≡ emloop {Group = ℤGroup} k
      → loop-class fillingsCW (c 0C) (cong (c ∘ Literal.row s n) v)
        ≡ fst (compGroupHom {F = ℤGroup} {G = H̃ᶜʷ circleCW 1} {H = R} circle-integer
            (cellular-map circleCW fillingsCW 1 c)) k
    row-image c s n v k word =
      cong {A = 0C ≡ 0C} {B = λ _ → fst R}
        (λ (l : 0C ≡ 0C) → loop-class fillingsCW (c 0C) (cong c l)) word
      ∙ sym (loop-natural circleCW fillingsCW c 0C (emloop {Group = ℤGroup} k))

abstract
  right-u1 : (p q r : ℤ)
    → fst (right-map p q r) source-u1 ≡ fst filling1-integer (pos 1)
  right-u1 p q r =
    loop-natural overlapCW fillingsCW (Literal.Seifert.allRight p q r)
      (t1 torus-base) (cong t1 torus-u)
    ∙ row-image c1 (pos 1) p torus-u (pos 1) (row-u (pos 1) p)

  right-u2 : (p q r : ℤ)
    → fst (right-map p q r) source-u2 ≡ fst filling2-integer (pos 1)
  right-u2 p q r =
    loop-natural overlapCW fillingsCW (Literal.Seifert.allRight p q r)
      (t2 torus-base) (cong t2 torus-u)
    ∙ row-image c2 (pos 1) q torus-u (pos 1) (row-u (pos 1) q)

  right-u3 : (p q r : ℤ)
    → fst (right-map p q r) source-u3 ≡ fst filling3-integer (pos 1 - r)
  right-u3 p q r =
    loop-natural overlapCW fillingsCW (Literal.Seifert.allRight p q r)
      (t3 torus-base) (cong t3 torus-u)
    ∙ row-image c3 (pos 1 - r) r torus-u (pos 1 - r) (row-u (pos 1 - r) r)

  right-h1 : (p q r : ℤ)
    → fst (right-map p q r) source-h1 ≡ fst filling1-integer p
  right-h1 p q r =
    loop-natural overlapCW fillingsCW (Literal.Seifert.allRight p q r)
      (t1 torus-base) (cong t1 torus-h)
    ∙ row-image c1 (pos 1) p torus-h p (row-h (pos 1) p)

  right-h2 : (p q r : ℤ)
    → fst (right-map p q r) source-h2 ≡ fst filling2-integer q
  right-h2 p q r =
    loop-natural overlapCW fillingsCW (Literal.Seifert.allRight p q r)
      (t2 torus-base) (cong t2 torus-h)
    ∙ row-image c2 (pos 1) q torus-h q (row-h (pos 1) q)

  right-h3 : (p q r : ℤ)
    → fst (right-map p q r) source-h3 ≡ fst filling3-integer r
  right-h3 p q r =
    loop-natural overlapCW fillingsCW (Literal.Seifert.allRight p q r)
      (t3 torus-base) (cong t3 torus-h)
    ∙ row-image c3 (pos 1 - r) r torus-h r (row-h (pos 1 - r) r)
