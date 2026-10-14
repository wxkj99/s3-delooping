{-# OPTIONS --cubical --safe #-}
module DeloopS3.Bridge.Profile.BaseSeifert.DegreeOneProof.Generators where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Int using (ℤ ; pos ; negsuc)
import Cubical.Data.Int as Z
open import Cubical.Algebra.Group
open import Cubical.Algebra.Group.DirProd
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties
open import Cubical.Algebra.Group.Instances.Int
open import Cubical.Algebra.AbGroup using (AbGroup→Group)
open import DeloopS3.Bridge.SeifertChains.Matrices using (ℤ² ; ℤ³ ; ℤ⁶)

open IsGroupHom using (pres· ; pres1 ; presinv)

-- The column order is ((u₁,u₂,u₃),(h₁,h₂,h₃)).
e-u1 e-u2 e-u3 e-h1 e-h2 e-h3 : fst ℤ⁶
e-u1 = (pos 1 , pos 0 , pos 0) , (pos 0 , pos 0 , pos 0)
e-u2 = (pos 0 , pos 1 , pos 0) , (pos 0 , pos 0 , pos 0)
e-u3 = (pos 0 , pos 0 , pos 1) , (pos 0 , pos 0 , pos 0)
e-h1 = (pos 0 , pos 0 , pos 0) , (pos 1 , pos 0 , pos 0)
e-h2 = (pos 0 , pos 0 , pos 0) , (pos 0 , pos 1 , pos 0)
e-h3 = (pos 0 , pos 0 , pos 0) , (pos 0 , pos 0 , pos 1)

abstract
  int-ext : (G : Group₀) (f g : GroupHom ℤGroup G)
    → fst f (pos 1) ≡ fst g (pos 1)
    → (z : ℤ) → fst f z ≡ fst g z
  int-ext G f g one = all
    where
    positive : (n : ℕ) → fst f (pos n) ≡ fst g (pos n)
    positive zero = pres1 (snd f) ∙ sym (pres1 (snd g))
    positive (suc n) =
      fst f (pos (suc n))
        ≡⟨ pres· (snd f) (pos n) (pos 1) ⟩
      GroupStr._·_ (snd G) (fst f (pos n)) (fst f (pos 1))
        ≡⟨ cong₂ (GroupStr._·_ (snd G)) (positive n) one ⟩
      GroupStr._·_ (snd G) (fst g (pos n)) (fst g (pos 1))
        ≡⟨ sym (pres· (snd g) (pos n) (pos 1)) ⟩
      fst g (pos (suc n)) ∎

    all : (z : ℤ) → fst f z ≡ fst g z
    all (pos n) = positive n
    all (negsuc n) =
      fst f (negsuc n)
        ≡⟨ presinv (snd f) (pos (suc n)) ⟩
      GroupStr.inv (snd G) (fst f (pos (suc n)))
        ≡⟨ cong (GroupStr.inv (snd G)) (positive (suc n)) ⟩
      GroupStr.inv (snd G) (fst g (pos (suc n)))
        ≡⟨ sym (presinv (snd g) (pos (suc n))) ⟩
      fst g (negsuc n) ∎

-- Product injections allow the six-coordinate decomposition to be proved
-- one pair at a time, without a six-term reassociation calculation.
pair-inl : (G H : Group₀) → GroupHom G (DirProd G H)
fst (pair-inl G H) x = x , GroupStr.1g (snd H)
snd (pair-inl G H) = makeIsGroupHom λ x y →
  ΣPathP (refl , sym (GroupStr.·IdR (snd H) (GroupStr.1g (snd H))))

pair-inr : (G H : Group₀) → GroupHom H (DirProd G H)
fst (pair-inr G H) y = GroupStr.1g (snd G) , y
snd (pair-inr G H) = makeIsGroupHom λ x y →
  ΣPathP (sym (GroupStr.·IdR (snd G) (GroupStr.1g (snd G))) , refl)

abstract
  pair-ext : (G H K : Group₀) (f g : GroupHom (DirProd G H) K)
    → ((x : fst G) → fst f (x , GroupStr.1g (snd H))
                       ≡ fst g (x , GroupStr.1g (snd H)))
    → ((y : fst H) → fst f (GroupStr.1g (snd G) , y)
                       ≡ fst g (GroupStr.1g (snd G) , y))
    → (v : fst (DirProd G H)) → fst f v ≡ fst g v
  pair-ext G H K f g left right (x , y) =
    fst f (x , y)
      ≡⟨ cong (fst f) (sym split) ⟩
    fst f (GroupStr._·_ (snd (DirProd G H)) a b)
      ≡⟨ pres· (snd f) a b ⟩
    GroupStr._·_ (snd K) (fst f a) (fst f b)
      ≡⟨ cong₂ (GroupStr._·_ (snd K)) (left x) (right y) ⟩
    GroupStr._·_ (snd K) (fst g a) (fst g b)
      ≡⟨ sym (pres· (snd g) a b) ⟩
    fst g (GroupStr._·_ (snd (DirProd G H)) a b)
      ≡⟨ cong (fst g) split ⟩
    fst g (x , y) ∎
    where
    a b : fst (DirProd G H)
    a = x , GroupStr.1g (snd H)
    b = GroupStr.1g (snd G) , y

    split : GroupStr._·_ (snd (DirProd G H)) a b ≡ (x , y)
    split = ΣPathP (GroupStr.·IdR (snd G) x , GroupStr.·IdL (snd H) y)

  two-ext : (G : Group₀) (f g : GroupHom (AbGroup→Group ℤ²) G)
    → fst f (pos 1 , pos 0) ≡ fst g (pos 1 , pos 0)
    → fst f (pos 0 , pos 1) ≡ fst g (pos 0 , pos 1)
    → (v : fst ℤ²) → fst f v ≡ fst g v
  two-ext G f g first second = pair-ext ℤGroup ℤGroup G f g
    (int-ext G f-left g-left first)
    (int-ext G f-right g-right second)
    where
    f-left g-left f-right g-right : GroupHom ℤGroup G
    f-left = compGroupHom (pair-inl ℤGroup ℤGroup) f
    g-left = compGroupHom (pair-inl ℤGroup ℤGroup) g
    f-right = compGroupHom (pair-inr ℤGroup ℤGroup) f
    g-right = compGroupHom (pair-inr ℤGroup ℤGroup) g

  three-ext : (G : Group₀) (f g : GroupHom (AbGroup→Group ℤ³) G)
    → fst f (pos 1 , pos 0 , pos 0) ≡ fst g (pos 1 , pos 0 , pos 0)
    → fst f (pos 0 , pos 1 , pos 0) ≡ fst g (pos 0 , pos 1 , pos 0)
    → fst f (pos 0 , pos 0 , pos 1) ≡ fst g (pos 0 , pos 0 , pos 1)
    → (v : fst ℤ³) → fst f v ≡ fst g v
  three-ext G f g first second third =
    pair-ext ℤGroup (AbGroup→Group ℤ²) G f g
      (int-ext G f-left g-left first)
      (two-ext G f-right g-right second third)
    where
    f-left g-left : GroupHom ℤGroup G
    f-left = compGroupHom (pair-inl ℤGroup (AbGroup→Group ℤ²)) f
    g-left = compGroupHom (pair-inl ℤGroup (AbGroup→Group ℤ²)) g

    f-right g-right : GroupHom (AbGroup→Group ℤ²) G
    f-right = compGroupHom (pair-inr ℤGroup (AbGroup→Group ℤ²)) f
    g-right = compGroupHom (pair-inr ℤGroup (AbGroup→Group ℤ²)) g

  six-ext : (G : Group₀) (f g : GroupHom (AbGroup→Group ℤ⁶) G)
    → fst f e-u1 ≡ fst g e-u1
    → fst f e-u2 ≡ fst g e-u2
    → fst f e-u3 ≡ fst g e-u3
    → fst f e-h1 ≡ fst g e-h1
    → fst f e-h2 ≡ fst g e-h2
    → fst f e-h3 ≡ fst g e-h3
    → (v : fst ℤ⁶) → fst f v ≡ fst g v
  six-ext G f g u1 u2 u3 h1 h2 h3 =
    pair-ext (AbGroup→Group ℤ³) (AbGroup→Group ℤ³) G f g
      (three-ext G f-left g-left u1 u2 u3)
      (three-ext G f-right g-right h1 h2 h3)
    where
    f-left g-left f-right g-right : GroupHom (AbGroup→Group ℤ³) G
    f-left = compGroupHom
      (pair-inl (AbGroup→Group ℤ³) (AbGroup→Group ℤ³)) f
    g-left = compGroupHom
      (pair-inl (AbGroup→Group ℤ³) (AbGroup→Group ℤ³)) g
    f-right = compGroupHom
      (pair-inr (AbGroup→Group ℤ³) (AbGroup→Group ℤ³)) f
    g-right = compGroupHom
      (pair-inr (AbGroup→Group ℤ³) (AbGroup→Group ℤ³)) g

  comparison-from-generators : (O V T : Group₀)
    (eO : GroupEquiv O (AbGroup→Group ℤ⁶))
    (eV : GroupEquiv V T) (s : GroupHom O V)
    (A : GroupHom (AbGroup→Group ℤ⁶) T)
    (x-u1 x-u2 x-u3 x-h1 x-h2 x-h3 : fst O)
    → fst (fst eO) x-u1 ≡ e-u1
    → fst (fst eO) x-u2 ≡ e-u2
    → fst (fst eO) x-u3 ≡ e-u3
    → fst (fst eO) x-h1 ≡ e-h1
    → fst (fst eO) x-h2 ≡ e-h2
    → fst (fst eO) x-h3 ≡ e-h3
    → fst (fst eV) (fst s x-u1) ≡ fst A e-u1
    → fst (fst eV) (fst s x-u2) ≡ fst A e-u2
    → fst (fst eV) (fst s x-u3) ≡ fst A e-u3
    → fst (fst eV) (fst s x-h1) ≡ fst A e-h1
    → fst (fst eV) (fst s x-h2) ≡ fst A e-h2
    → fst (fst eV) (fst s x-h3) ≡ fst A e-h3
    → (z : fst O) → fst (fst eV) (fst s z) ≡ fst A (fst (fst eO) z)
  comparison-from-generators O V T eO eV s A
    x-u1 x-u2 x-u3 x-h1 x-h2 x-h3
    coord-u1 coord-u2 coord-u3 coord-h1 coord-h2 coord-h3
    image-u1 image-u2 image-u3 image-h1 image-h2 image-h3 z =
      fst (fst eV) (fst s z)
        ≡⟨ sym (cong (fst forward) (retEq (fst eO) z)) ⟩
      fst transported (fst (fst eO) z)
        ≡⟨ agrees (fst (fst eO) z) ⟩
      fst A (fst (fst eO) z) ∎
    where
    forward : GroupHom O T
    forward = compGroupHom s (GroupEquiv→GroupHom eV)

    transported : GroupHom (AbGroup→Group ℤ⁶) T
    transported = compGroupHom (GroupEquiv→GroupHom (invGroupEquiv eO)) forward

    at-generator : (x : fst O) (e : fst ℤ⁶)
      → fst (fst eO) x ≡ e
      → fst (fst eV) (fst s x) ≡ fst A e
      → fst transported e ≡ fst A e
    at-generator x e coordinate image =
      fst transported e
        ≡⟨ cong (fst forward) (sym (cong (invEq (fst eO)) coordinate)
                               ∙ retEq (fst eO) x) ⟩
      fst (fst eV) (fst s x)
        ≡⟨ image ⟩
      fst A e ∎

    agrees : (v : fst ℤ⁶) → fst transported v ≡ fst A v
    agrees = six-ext T transported A
      (at-generator x-u1 e-u1 coord-u1 image-u1)
      (at-generator x-u2 e-u2 coord-u2 image-u2)
      (at-generator x-u3 e-u3 coord-u3 image-u3)
      (at-generator x-h1 e-h1 coord-h1 image-h1)
      (at-generator x-h2 e-h2 coord-h2 image-h2)
      (at-generator x-h3 e-h3 coord-h3 image-h3)
