{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Assembly where

open import Cubical.Foundations.Prelude
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ ; pos)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import DeloopS3.Bridge.SeifertChains.Matrices using (ℤ⁶ ; vertex₁ ; Araw)
open import DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Generators
  using (e-u1 ; e-u2 ; e-u3 ; e-h1 ; e-h2 ; e-h3
        ; int-ext ; pair-inl ; pair-inr ; comparison-from-generators)

open IsGroupHom using (pres· ; presinv)

Vertex : Group₀
Vertex = AbGroup→Group vertex₁

module V = GroupStr (snd Vertex)

e-a e-b e-h : fst vertex₁
e-a = (pos 1 , pos 0) , pos 0 , pos 0 , pos 0 , pos 0
e-b = (pos 0 , pos 1) , pos 0 , pos 0 , pos 0 , pos 0
e-h = (pos 0 , pos 0) , pos 1 , pos 0 , pos 0 , pos 0

ic1 ic2 ic3 : GroupHom ℤGroup Vertex
fst ic1 n = (pos 0 , pos 0) , pos 0 , n , pos 0 , pos 0
snd ic1 = makeIsGroupHom λ _ _ → refl
fst ic2 n = (pos 0 , pos 0) , pos 0 , pos 0 , n , pos 0
snd ic2 = makeIsGroupHom λ _ _ → refl
fst ic3 n = (pos 0 , pos 0) , pos 0 , pos 0 , pos 0 , n
snd ic3 = makeIsGroupHom λ _ _ → refl

-- The six signed columns, before evaluating the matrix formula.
C-u1 C-u2 : fst vertex₁
C-u1 = V._·_ e-a (V.inv (fst ic1 (pos 1)))
C-u2 = V._·_ e-b (V.inv (fst ic2 (pos 1)))

C-u3 : ℤ → fst vertex₁
C-u3 r = V._·_ (V.inv (V._·_ e-a e-b))
                    (V.inv (fst ic3 (pos 1 Z.- r)))

C-h1 C-h2 C-h3 : ℤ → fst vertex₁
C-h1 p = V._·_ e-h (V.inv (fst ic1 p))
C-h2 q = V._·_ e-h (V.inv (fst ic2 q))
C-h3 r = V._·_ e-h (V.inv (fst ic3 r))

abstract
  private
    times-zero : (n : ℤ) → n Z.· pos 0 ≡ pos 0
    times-zero n = Z.·Comm n (pos 0)

    negative-zero-row : (n m : ℤ)
      → Z.- (n Z.· pos 0 Z.+ m Z.· pos 0) ≡ pos 0
    negative-zero-row n m =
      cong Z.-_ (cong₂ Z._+_ (times-zero n) (times-zero m))

    negative-unit-row : (n : ℤ)
      → Z.- (pos 0 Z.+ n Z.· pos 1) ≡ pos 0 Z.+ (Z.- n)
    negative-unit-row n =
      cong Z.-_ (cong (pos 0 Z.+_) (Z.·IdR n)
                 ∙ GroupStr.·IdL (snd ℤGroup) n)
      ∙ sym (GroupStr.·IdL (snd ℤGroup) (Z.- n))

    negative-first-unit : (n m : ℤ)
      → Z.- (n Z.· pos 1 Z.+ m Z.· pos 0) ≡ pos 0 Z.+ (Z.- n)
    negative-first-unit n m =
      cong Z.-_ (cong₂ Z._+_ (Z.·IdR n) (times-zero m)
                 ∙ GroupStr.·IdR (snd ℤGroup) n)
      ∙ sym (GroupStr.·IdL (snd ℤGroup) (Z.- n))

    negative-last-unit : (n m : ℤ)
      → Z.- (n Z.· pos 0 Z.+ m Z.· pos 1) ≡ pos 0 Z.+ (Z.- m)
    negative-last-unit n m =
      cong Z.-_ (cong₂ Z._+_ (times-zero n) (Z.·IdR m)
                 ∙ GroupStr.·IdL (snd ℤGroup) m)
      ∙ sym (GroupStr.·IdL (snd ℤGroup) (Z.- m))

  Araw-column-u1 : (p q r : ℤ) → C-u1 ≡ fst (Araw p q r) e-u1
  Araw-column-u1 p q r = sym (ΣPathP (refl , ΣPathP (refl ,
    ΣPathP (cong Z.-_ (cong (pos 1 Z.+_) (times-zero p)) ,
    ΣPathP (cong Z.-_ (cong (pos 0 Z.+_) (times-zero q)) ,
            negative-zero-row (pos 1 Z.- r) r)))))

  Araw-column-u2 : (p q r : ℤ) → C-u2 ≡ fst (Araw p q r) e-u2
  Araw-column-u2 p q r = sym (ΣPathP (refl , ΣPathP (refl ,
    ΣPathP (cong Z.-_ (cong (pos 0 Z.+_) (times-zero p)) ,
    ΣPathP (cong Z.-_ (cong (pos 1 Z.+_) (times-zero q)) ,
            negative-zero-row (pos 1 Z.- r) r)))))

  Araw-column-u3 : (p q r : ℤ) → C-u3 r ≡ fst (Araw p q r) e-u3
  Araw-column-u3 p q r = sym (ΣPathP (refl , ΣPathP (refl ,
    ΣPathP (cong Z.-_ (cong (pos 0 Z.+_) (times-zero p)) ,
    ΣPathP (cong Z.-_ (cong (pos 0 Z.+_) (times-zero q)) ,
            negative-first-unit (pos 1 Z.- r) r)))))

  Araw-column-h1 : (p q r : ℤ) → C-h1 p ≡ fst (Araw p q r) e-h1
  Araw-column-h1 p q r = sym (ΣPathP (refl , ΣPathP (refl ,
    ΣPathP (negative-unit-row p ,
    ΣPathP (cong Z.-_ (cong (pos 0 Z.+_) (times-zero q)) ,
            negative-zero-row (pos 1 Z.- r) r)))))

  Araw-column-h2 : (p q r : ℤ) → C-h2 q ≡ fst (Araw p q r) e-h2
  Araw-column-h2 p q r = sym (ΣPathP (refl , ΣPathP (refl ,
    ΣPathP (cong Z.-_ (cong (pos 0 Z.+_) (times-zero p)) ,
    ΣPathP (negative-unit-row q ,
            negative-zero-row (pos 1 Z.- r) r)))))

  Araw-column-h3 : (p q r : ℤ) → C-h3 r ≡ fst (Araw p q r) e-h3
  Araw-column-h3 p q r = sym (ΣPathP (refl , ΣPathP (refl ,
    ΣPathP (cong Z.-_ (cong (pos 0 Z.+_) (times-zero p)) ,
    ΣPathP (cong Z.-_ (cong (pos 0 Z.+_) (times-zero q)) ,
            negative-last-unit (pos 1 Z.- r) r)))))

module Assemble
  (O G R : Group₀)
  (eO : GroupEquiv O (AbGroup→Group ℤ⁶))
  (eV : GroupEquiv (DirProd G R) Vertex)
  (xu1 xu2 xu3 xh1 xh2 xh3 : fst O)
  (a b h : fst G)
  (c1 c2 c3 : GroupHom ℤGroup R)
  where

  private
    module GG = GroupStr (snd G)
    module RR = GroupStr (snd R)

  core-coordinate : GroupHom G Vertex
  core-coordinate = compGroupHom {F = G} {G = DirProd G R} {H = Vertex}
    (pair-inl G R)
    (GroupEquiv→GroupHom {G = DirProd G R} {H = Vertex} eV)

  filling-coordinate : GroupHom R Vertex
  filling-coordinate = compGroupHom {F = R} {G = DirProd G R} {H = Vertex}
    (pair-inr G R)
    (GroupEquiv→GroupHom {G = DirProd G R} {H = Vertex} eV)

  -- Only chart normalizations: no Seifert parameters or map equations.
  record Markings : Type where
    field
      source-u1 : fst (fst eO) xu1 ≡ e-u1
      source-u2 : fst (fst eO) xu2 ≡ e-u2
      source-u3 : fst (fst eO) xu3 ≡ e-u3
      source-h1 : fst (fst eO) xh1 ≡ e-h1
      source-h2 : fst (fst eO) xh2 ≡ e-h2
      source-h3 : fst (fst eO) xh3 ≡ e-h3
      core-a : fst core-coordinate a ≡ e-a
      core-b : fst core-coordinate b ≡ e-b
      core-h : fst core-coordinate h ≡ e-h
      filling-1 : fst filling-coordinate (fst c1 (pos 1)) ≡ fst ic1 (pos 1)
      filling-2 : fst filling-coordinate (fst c2 (pos 1)) ≡ fst ic2 (pos 1)
      filling-3 : fst filling-coordinate (fst c3 (pos 1)) ≡ fst ic3 (pos 1)

  -- Actual maps supply these equations; they are not chart hypotheses.
  record WordImages (p q r : ℤ)
    (L : GroupHom O G) (Rmap : GroupHom O R) : Type where
    field
      left-u1 : fst L xu1 ≡ a
      left-u2 : fst L xu2 ≡ b
      left-u3 : fst L xu3 ≡ GG.inv (GG._·_ a b)
      left-h1 : fst L xh1 ≡ h
      left-h2 : fst L xh2 ≡ h
      left-h3 : fst L xh3 ≡ h
      right-u1 : fst Rmap xu1 ≡ fst c1 (pos 1)
      right-u2 : fst Rmap xu2 ≡ fst c2 (pos 1)
      right-u3 : fst Rmap xu3 ≡ fst c3 (pos 1 Z.- r)
      right-h1 : fst Rmap xh1 ≡ fst c1 p
      right-h2 : fst Rmap xh2 ≡ fst c2 q
      right-h3 : fst Rmap xh3 ≡ fst c3 r

  abstract
    fill-coordinate-n : (c : GroupHom ℤGroup R) (ic : GroupHom ℤGroup Vertex)
      → fst filling-coordinate (fst c (pos 1)) ≡ fst ic (pos 1)
      → (n : ℤ) → fst filling-coordinate (fst c n) ≡ fst ic n
    fill-coordinate-n c ic marking = int-ext Vertex
      (compGroupHom {F = ℤGroup} {G = R} {H = Vertex} c filling-coordinate)
      ic marking

    fill-coordinate-1 : Markings → (n : ℤ)
      → fst filling-coordinate (fst c1 n) ≡ fst ic1 n
    fill-coordinate-1 m = fill-coordinate-n c1 ic1 (Markings.filling-1 m)

    fill-coordinate-2 : Markings → (n : ℤ)
      → fst filling-coordinate (fst c2 n) ≡ fst ic2 n
    fill-coordinate-2 m = fill-coordinate-n c2 ic2 (Markings.filling-2 m)

    fill-coordinate-3 : Markings → (n : ℤ)
      → fst filling-coordinate (fst c3 n) ≡ fst ic3 n
    fill-coordinate-3 m = fill-coordinate-n c3 ic3 (Markings.filling-3 m)

    core-third : Markings
      → fst core-coordinate (GG.inv (GG._·_ a b)) ≡ V.inv (V._·_ e-a e-b)
    core-third m =
      presinv (snd core-coordinate) (GG._·_ a b)
      ∙ cong V.inv (pres· (snd core-coordinate) a b
          ∙ cong₂ V._·_ (Markings.core-a m) (Markings.core-b m))

    pair-coordinate : (g : fst G) (t : fst R)
      → fst (fst eV) (g , t)
        ≡ V._·_ (fst core-coordinate g) (fst filling-coordinate t)
    pair-coordinate g t =
      cong (fst (fst eV)) (sym (ΣPathP (GG.·IdR g , RR.·IdL t)))
      ∙ pres· (snd eV) (g , RR.1g) (GG.1g , t)

    signed-coordinate : (g : fst G) (t : fst R)
      → fst (fst eV) (g , RR.inv t)
        ≡ V._·_ (fst core-coordinate g) (V.inv (fst filling-coordinate t))
    signed-coordinate g t = pair-coordinate g (RR.inv t)
      ∙ cong (V._·_ (fst core-coordinate g)) (presinv (snd filling-coordinate) t)

    degree-one : Markings → (p q r : ℤ)
      → (L : GroupHom O G) (Rmap : GroupHom O R)
      → (s : GroupHom O (DirProd G R))
      → ((x : fst O) → fst s x ≡ (fst L x , RR.inv (fst Rmap x)))
      → WordImages p q r L Rmap
      → (z : fst O)
      → fst (fst eV) (fst s z) ≡ fst (Araw p q r) (fst (fst eO) z)
    degree-one m p q r L Rmap s s-eval words =
      comparison-from-generators O (DirProd G R) Vertex eO eV s (Araw p q r)
        xu1 xu2 xu3 xh1 xh2 xh3
        (Markings.source-u1 m) (Markings.source-u2 m) (Markings.source-u3 m)
        (Markings.source-h1 m) (Markings.source-h2 m) (Markings.source-h3 m)
        (image xu1 a (fst c1 (pos 1)) e-a (fst ic1 (pos 1))
          (WordImages.left-u1 words) (WordImages.right-u1 words)
          (Markings.core-a m) (fill-coordinate-1 m (pos 1))
          ∙ Araw-column-u1 p q r)
        (image xu2 b (fst c2 (pos 1)) e-b (fst ic2 (pos 1))
          (WordImages.left-u2 words) (WordImages.right-u2 words)
          (Markings.core-b m) (fill-coordinate-2 m (pos 1))
          ∙ Araw-column-u2 p q r)
        (image xu3 (GG.inv (GG._·_ a b)) (fst c3 (pos 1 Z.- r))
          (V.inv (V._·_ e-a e-b)) (fst ic3 (pos 1 Z.- r))
          (WordImages.left-u3 words) (WordImages.right-u3 words)
          (core-third m) (fill-coordinate-3 m (pos 1 Z.- r))
          ∙ Araw-column-u3 p q r)
        (image xh1 h (fst c1 p) e-h (fst ic1 p)
          (WordImages.left-h1 words) (WordImages.right-h1 words)
          (Markings.core-h m) (fill-coordinate-1 m p)
          ∙ Araw-column-h1 p q r)
        (image xh2 h (fst c2 q) e-h (fst ic2 q)
          (WordImages.left-h2 words) (WordImages.right-h2 words)
          (Markings.core-h m) (fill-coordinate-2 m q)
          ∙ Araw-column-h2 p q r)
        (image xh3 h (fst c3 r) e-h (fst ic3 r)
          (WordImages.left-h3 words) (WordImages.right-h3 words)
          (Markings.core-h m) (fill-coordinate-3 m r)
          ∙ Araw-column-h3 p q r)
      where
      image : (x : fst O) (g : fst G) (t : fst R) (v w : fst vertex₁)
        → fst L x ≡ g → fst Rmap x ≡ t
        → fst core-coordinate g ≡ v → fst filling-coordinate t ≡ w
        → fst (fst eV) (fst s x) ≡ V._·_ v (V.inv w)
      image x g t v w left right core filling =
        cong (fst (fst eV)) (s-eval x
          ∙ ΣPathP (left , cong RR.inv right))
        ∙ signed-coordinate g t
        ∙ cong₂ V._·_ core (cong V.inv filling)
