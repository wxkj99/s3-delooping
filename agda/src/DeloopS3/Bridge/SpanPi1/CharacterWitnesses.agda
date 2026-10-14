{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.CharacterWitnesses where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Int using (pos)
open import Cubical.Data.Bool using (Bool; true; false; not; _and_; false≢true)
open import Cubical.Data.SumFin using (fzero; fsuc; toℕ)
open import Cubical.Data.Empty as Empty using (⊥)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (GroupIso→GroupHom; idGroupHom)
open import Cubical.Algebra.Group.Properties using (module GroupTheory)
open import Cubical.Algebra.Group.ZAction using (_ℤ[_]·_; homPresℤ·)
open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.SpanPi1.CharacterAlgebra using (NonabelianImage)
open import DeloopS3.Bridge.SpanPi1.CharacterPairs
open import DeloopS3.Bridge.SpanPi1.CharacterTables
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.Enumerated using (certificate-cong)
open import DeloopS3.Groups.Concrete
open import DeloopS3.Groups.Identification using (D₆→A₅; module D₆-inclusion)
import DeloopS3.Groups.Dihedral as D
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Octa3 as O
import DeloopS3.Cert.Icosa10 as I
import DeloopS3.Cert.Interpret.Short as Short
open Short using (ShortCase; octa; icosa; Δ; H)

-- These are literal group words, rather than graph edge-word data.
O-rotation-term O-reflection-term I-conjugator-term I-rotation-term I-reflection-term : Term
O-rotation-term = inverse Y ⊗ X
O-reflection-term = (Y ⊗ X) ⊗ inverse Y
I-conjugator-term = ((X ⊗ inverse Y) ⊗ X) ⊗ Y
I-rotation-term = Y
I-reflection-term = (I-conjugator-term ⊗ X) ⊗ inverse I-conjugator-term

module PairWitness (n e : ℕ) (rt st : P.Table)
  (checked : D.PairTables.Checked n e rt st)
  (G : Group₀) (comparison : GroupIso (D.PairTables.Build.group n e rt st checked) G)
  (rp sp : D.Pairs.Pair e) where
  module T = D.PairTables n e rt st
  module B = T.Build checked
  private
    module G = GroupStr (snd G)
  open GroupTheory G

  forward : GroupHom B.group G
  forward = GroupIso→GroupHom comparison
  rotation reflection : fst G
  rotation = fst forward rp
  reflection = fst forward sp

  eq-refl : (x : T.Pair) → T.eq x x ≡ true
  eq-refl (i , false) = cong (_and true) (natEq-refl (toℕ i))
  eq-refl (i , true) = cong (_and true) (natEq-refl (toℕ i))

  abstract
    unequal : (x y : T.Pair) → not (T.eq x y) ≡ true → x ≡ y → ⊥
    unequal x y neq p = false≢true
      (sym (cong not (cong (T.eq x) (sym p) ∙ eq-refl x)) ∙ neq)

    injective : {x y : T.Pair} → fst forward x ≡ fst forward y → x ≡ y
    injective {x} {y} p = sym (Iso.ret (fst comparison) x)
      ∙ cong (Iso.inv (fst comparison)) p ∙ Iso.ret (fst comparison) y

    inversion : T.eq (T.mul sp rp) (T.mul (T.inverse rp) sp) ≡ true
      → reflection G.· rotation ≡ G.inv rotation G.· reflection
    inversion ok = sym (IsGroupHom.pres· (snd forward) sp rp)
      ∙ cong (fst forward) (T.eq-sound _ _ ok)
      ∙ IsGroupHom.pres· (snd forward) (T.inverse rp) sp
      ∙ cong (G._· reflection) (IsGroupHom.presinv (snd forward) rp)

    not-self-inverse : not (T.eq rp (T.inverse rp)) ≡ true
      → rotation ≡ G.inv rotation → ⊥
    not-self-inverse ok p = unequal rp (T.inverse rp) ok
      (injective (p ∙ sym (IsGroupHom.presinv (snd forward) rp)))

    conjugates-to-inverse : T.eq (T.mul sp rp) (T.mul (T.inverse rp) sp) ≡ true
      → (reflection G.· rotation) G.· G.inv reflection ≡ G.inv rotation
    conjugates-to-inverse ok = cong (G._· G.inv reflection) (inversion ok)
      ∙ sym (G.·Assoc (G.inv rotation) reflection (G.inv reflection))
      ∙ cong (G.inv rotation G.·_) (G.·InvR reflection) ∙ G.·IdR (G.inv rotation)

    noncommuting : T.eq (T.mul sp rp) (T.mul (T.inverse rp) sp) ≡ true
      → not (T.eq rp (T.inverse rp)) ≡ true
      → rotation G.· reflection ≡ reflection G.· rotation → ⊥
    noncommuting rel neq p = not-self-inverse neq (·CancelR reflection (p ∙ inversion rel))

    rotation-power : (k : ℕ) → T.eq (pos k ℤ[ B.group ]· rp) T.unit ≡ true
      → pos k ℤ[ G ]· rotation ≡ G.1g
    rotation-power k ok = sym (homPresℤ· forward rp (pos k))
      ∙ cong (fst forward) (T.eq-sound _ _ ok) ∙ IsGroupHom.pres1 (snd forward)

    rotation-power-nontrivial : (k : ℕ) → not (T.eq (pos k ℤ[ B.group ]· rp) T.unit) ≡ true
      → pos k ℤ[ G ]· rotation ≡ G.1g → ⊥
    rotation-power-nontrivial k ok p = unequal _ _ ok (injective
      (homPresℤ· forward rp (pos k) ∙ p ∙ sym (IsGroupHom.pres1 (snd forward))))

    reflection-square : T.eq (T.mul sp sp) T.unit ≡ true
      → reflection G.· reflection ≡ G.1g
    reflection-square ok = sym (IsGroupHom.pres· (snd forward) sp sp)
      ∙ cong (fst forward) (T.eq-sound _ _ ok) ∙ IsGroupHom.pres1 (snd forward)

module W₈ = PairWitness 4 3 D.r₄ D.s₄ D.checked₈ D₈ D.D₈-pairs≅D₈ (fsuc fzero , false) (fzero , true)
module W₆ = PairWitness 5 2 D.r₃ D.s₃ D.checked₆ D₆ D.D₆-pairs≅D₆ (fsuc fzero , false) (fzero , true)

abstract
  inversion-check₈ : D.P₈.eq (D.P₈.mul (fzero , true) (fsuc fzero , false))
    (D.P₈.mul (D.P₈.inverse (fsuc fzero , false)) (fzero , true)) ≡ true
  inversion-check₈ = refl
  inverse-neq-check₈ : not (D.P₈.eq (fsuc fzero , false) (D.P₈.inverse (fsuc fzero , false))) ≡ true
  inverse-neq-check₈ = refl
  inversion-check₆ : D.P₆.eq (D.P₆.mul (fzero , true) (fsuc fzero , false))
    (D.P₆.mul (D.P₆.inverse (fsuc fzero , false)) (fzero , true)) ≡ true
  inversion-check₆ = refl
  inverse-neq-check₆ : not (D.P₆.eq (fsuc fzero , false) (D.P₆.inverse (fsuc fzero , false))) ≡ true
  inverse-neq-check₆ = refl

rotation reflection : (c : ShortCase) → fst (H c)
rotation octa = W₈.rotation
rotation icosa = W₆.rotation
reflection octa = W₈.reflection
reflection icosa = W₆.reflection

abstract
  rotation-not-self-inverse : (c : ShortCase) → rotation c ≡ GroupStr.inv (snd (H c)) (rotation c) → ⊥
  rotation-not-self-inverse octa = W₈.not-self-inverse inverse-neq-check₈
  rotation-not-self-inverse icosa = W₆.not-self-inverse inverse-neq-check₆

  reflection-inverts-rotation : (c : ShortCase)
    → GroupStr._·_ (snd (H c)) (GroupStr._·_ (snd (H c)) (reflection c) (rotation c))
        (GroupStr.inv (snd (H c)) (reflection c))
      ≡ GroupStr.inv (snd (H c)) (rotation c)
  reflection-inverts-rotation octa = W₈.conjugates-to-inverse inversion-check₈
  reflection-inverts-rotation icosa = W₆.conjugates-to-inverse inversion-check₆

  rotation-reflection-noncommute : (c : ShortCase)
    → GroupStr._·_ (snd (H c)) (rotation c) (reflection c)
      ≡ GroupStr._·_ (snd (H c)) (reflection c) (rotation c) → ⊥
  rotation-reflection-noncommute octa = W₈.noncommuting inversion-check₈ inverse-neq-check₈
  rotation-reflection-noncommute icosa = W₆.noncommuting inversion-check₆ inverse-neq-check₆

  rotation-order₄ : pos 4 ℤ[ D₈ ]· rotation octa ≡ GroupStr.1g (snd D₈)
  rotation-order₄ = W₈.rotation-power 4 refl
  rotation-order₃ : pos 3 ℤ[ D₆ ]· rotation icosa ≡ GroupStr.1g (snd D₆)
  rotation-order₃ = W₆.rotation-power 3 refl
  rotation₈-power₁≠1 : pos 1 ℤ[ D₈ ]· rotation octa ≡ GroupStr.1g (snd D₈) → ⊥
  rotation₈-power₁≠1 = W₈.rotation-power-nontrivial 1 refl
  rotation₈-power₂≠1 : pos 2 ℤ[ D₈ ]· rotation octa ≡ GroupStr.1g (snd D₈) → ⊥
  rotation₈-power₂≠1 = W₈.rotation-power-nontrivial 2 refl
  rotation₈-power₃≠1 : pos 3 ℤ[ D₈ ]· rotation octa ≡ GroupStr.1g (snd D₈) → ⊥
  rotation₈-power₃≠1 = W₈.rotation-power-nontrivial 3 refl
  rotation₆-power₁≠1 : pos 1 ℤ[ D₆ ]· rotation icosa ≡ GroupStr.1g (snd D₆) → ⊥
  rotation₆-power₁≠1 = W₆.rotation-power-nontrivial 1 refl
  rotation₆-power₂≠1 : pos 2 ℤ[ D₆ ]· rotation icosa ≡ GroupStr.1g (snd D₆) → ⊥
  rotation₆-power₂≠1 = W₆.rotation-power-nontrivial 2 refl

  reflection-square : (c : ShortCase)
    → GroupStr._·_ (snd (H c)) (reflection c) (reflection c) ≡ GroupStr.1g (snd (H c))
  reflection-square octa = W₈.reflection-square refl
  reflection-square icosa = W₆.reflection-square refl

  ε₈-rotation : fst ε₈ (rotation octa) ≡ zero₂
  ε₈-rotation = Eight.character-pair (fsuc fzero , false)
  ε₈-reflection : fst ε₈ (reflection octa) ≡ one₂
  ε₈-reflection = Eight.character-pair (fzero , true)
  ε₆-rotation : fst ε₆ (rotation icosa) ≡ zero₂
  ε₆-rotation = Six.character-pair (fsuc fzero , false)
  ε₆-reflection : fst ε₆ (reflection icosa) ≡ one₂
  ε₆-reflection = Six.character-pair (fzero , true)

-- Finite interface for the geometric caller: it must supply the two
-- preimages rather than surjectivity or an identification of loops.
abstract
  two-witnesses-nonabelian : (c : ShortCase) (K : Group₀) (f : GroupHom K (H c))
    (u v : fst K) → fst f u ≡ rotation c → fst f v ≡ reflection c
    → NonabelianImage f
  two-witnesses-nonabelian c K f u v pu pv = PT.∣ u , v , (λ p →
    rotation-reflection-noncommute c
      (sym (cong₂ (GroupStr._·_ (snd (H c))) pu pv) ∙ p
       ∙ cong₂ (GroupStr._·_ (snd (H c))) pv pu)) ∣₁
