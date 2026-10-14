{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.CharacterImages where

-- Four finite image equations identifying actual elements of Short.Δ
-- and Short.H, rather than raw word lists.
open import Cubical.Foundations.Prelude
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Bool using (true; false)
open import Cubical.Data.SumFin using (fzero; fsuc)
open import Cubical.Data.Empty using (⊥)
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Bridge.SpanPi1.CharacterAlgebra using (NonabelianImage)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (idGroupHom)
open import Cubical.Algebra.SymmetricGroup using (FinSymGroup)
open import DeloopS3.Groups.TablePermutation
open import DeloopS3.Groups.Enumerated using (certificate-cong)
open import DeloopS3.Groups.Concrete
open import DeloopS3.Groups.Identification using (D₆→A₅; module D₆-inclusion)
import DeloopS3.Groups.Dihedral as D
open import DeloopS3.Bridge.SpanPi1.CharacterTables
open import DeloopS3.Bridge.SpanPi1.CharacterWitnesses
import DeloopS3.Bridge.SpanPi1.WordAlgebra as WA
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Octa3 as O
import DeloopS3.Cert.Icosa10 as I
import DeloopS3.Cert.Interpret.Short as Short
open Short using (ShortCase; octa; icosa; Δ; H)

degree : ShortCase → ℕ
degree octa = 4
degree icosa = 5

ambient : (c : ShortCase) → GroupHom (Δ c) (FinSymGroup (degree c))
ambient octa = idGroupHom
ambient icosa = A₅→S₅

inclusion : (c : ShortCase) → GroupHom (H c) (Δ c)
inclusion octa = D₈→S₄
inclusion icosa = D₆→A₅

subgroupPermutation : (c : ShortCase) → GroupHom (H c) (FinSymGroup (degree c))
subgroupPermutation octa = D₈-tables.embedding
subgroupPermutation icosa = D₆-tables.embedding

aTable bTable rTable sTable : ShortCase → P.Table
aTable c = Ch.a (Short.certOf c)
bTable c = Ch.b (Short.certOf c)
rTable octa = D.r₄
rTable icosa = D.r₃
sTable octa = D.s₄
sTable icosa = D.s₃

rotationTerm reflectionTerm : ShortCase → Term
rotationTerm octa = O-rotation-term
rotationTerm icosa = I-rotation-term
reflectionTerm octa = O-reflection-term
reflectionTerm icosa = I-reflection-term

rotationDownstairs reflectionDownstairs : (c : ShortCase) → fst (Δ c)
rotationDownstairs c = eval (Δ c) (Short.generator-a c) (Short.generator-b c) (rotationTerm c)
reflectionDownstairs c = eval (Δ c) (Short.generator-a c) (Short.generator-b c) (reflectionTerm c)

abstract
  a-valid : (c : ShortCase) → P.isPerm (degree c) (aTable c) ≡ true
  a-valid octa = refl
  a-valid icosa = refl
  b-valid : (c : ShortCase) → P.isPerm (degree c) (bTable c) ≡ true
  b-valid octa = refl
  b-valid icosa = refl
  r-valid : (c : ShortCase) → P.isPerm (degree c) (rTable c) ≡ true
  r-valid octa = refl
  r-valid icosa = refl
  s-valid : (c : ShortCase) → P.isPerm (degree c) (sTable c) ≡ true
  s-valid octa = refl
  s-valid icosa = refl

  rotation-term-valid : (c : ShortCase) → validTerm (degree c) (aTable c) (bTable c) (rotationTerm c) ≡ true
  rotation-term-valid octa = refl
  rotation-term-valid icosa = refl
  reflection-term-valid : (c : ShortCase) → validTerm (degree c) (aTable c) (bTable c) (reflectionTerm c) ≡ true
  reflection-term-valid octa = refl
  reflection-term-valid icosa = refl

  rotation-table-check : (c : ShortCase)
    → P.tableEq (tableEval (aTable c) (bTable c) (rotationTerm c)) (rTable c) ≡ true
  rotation-table-check octa = refl
  rotation-table-check icosa = refl
  reflection-table-check : (c : ShortCase)
    → P.tableEq (tableEval (aTable c) (bTable c) (reflectionTerm c)) (sTable c) ≡ true
  reflection-table-check octa = refl
  reflection-table-check icosa = refl

  ambient-inclusion : (c : ShortCase) (d : fst (H c))
    → fst (ambient c) (fst (inclusion c) d) ≡ fst (subgroupPermutation c) d
  ambient-inclusion octa d = refl
  ambient-inclusion icosa d = D₆-inclusion.commutes d

  ambient-injective : (c : ShortCase) {x y : fst (Δ c)}
    → fst (ambient c) x ≡ fst (ambient c) y → x ≡ y
  ambient-injective octa p = p
  ambient-injective icosa p = A₅-tables.embed-injective p

  a-image-table : (c : ShortCase)
    → fst (ambient c) (Short.generator-a c) ≡ certificatePermutation {t = aTable c} (a-valid c)
  a-image-table octa = Short.generator-a-octa
    ∙ certificate-cong (aTable octa) (aTable octa) (P.valid O.a-permutation) (a-valid octa) refl
  a-image-table icosa = certificate-cong (A₅-tables.table (Short.generator-a icosa)) (aTable icosa)
    (A₅-tables.valid (Short.generator-a icosa)) (a-valid icosa) Short.generator-a-icosa

  b-image-table : (c : ShortCase)
    → fst (ambient c) (Short.generator-b c) ≡ certificatePermutation {t = bTable c} (b-valid c)
  b-image-table octa = Short.generator-b-octa
    ∙ certificate-cong (bTable octa) (bTable octa) (P.valid O.b-permutation) (b-valid octa) refl
  b-image-table icosa = certificate-cong (A₅-tables.table (Short.generator-b icosa)) (bTable icosa)
    (A₅-tables.valid (Short.generator-b icosa)) (b-valid icosa) Short.generator-b-icosa

  rotation-image-table : (c : ShortCase)
    → fst (subgroupPermutation c) (rotation c) ≡ certificatePermutation {t = rTable c} (r-valid c)
  rotation-image-table octa = D.Compare₈.commutes (fsuc fzero , false)
    ∙ certificate-cong (D.P₈.table (fsuc fzero , false)) D.r₄
      (D.Dihedral₈.validAt (fsuc fzero , false)) (r-valid octa) refl
  rotation-image-table icosa = D.Compare₆.commutes (fsuc fzero , false)
    ∙ certificate-cong (D.P₆.table (fsuc fzero , false)) D.r₃
      (D.Dihedral₆.validAt (fsuc fzero , false)) (r-valid icosa) refl

  reflection-image-table : (c : ShortCase)
    → fst (subgroupPermutation c) (reflection c) ≡ certificatePermutation {t = sTable c} (s-valid c)
  reflection-image-table octa = D.Compare₈.commutes (fzero , true)
    ∙ certificate-cong (D.P₈.table (fzero , true)) D.s₄
      (D.Dihedral₈.validAt (fzero , true)) (s-valid octa) refl
  reflection-image-table icosa = D.Compare₆.commutes (fzero , true)
    ∙ certificate-cong (D.P₆.table (fzero , true)) D.s₃
      (D.Dihedral₆.validAt (fzero , true)) (s-valid icosa) refl

  rotation-word-table : (c : ShortCase)
    → fst (ambient c) (rotationDownstairs c) ≡ certificatePermutation {t = rTable c} (r-valid c)
  rotation-word-table c = interpreted-table (degree c) (ambient c)
    (Short.generator-a c) (Short.generator-b c) (aTable c) (bTable c)
    (a-valid c) (b-valid c) (a-image-table c) (b-image-table c)
    (rotationTerm c) (rotation-term-valid c) (rTable c) (r-valid c) (rotation-table-check c)

  reflection-word-table : (c : ShortCase)
    → fst (ambient c) (reflectionDownstairs c) ≡ certificatePermutation {t = sTable c} (s-valid c)
  reflection-word-table c = interpreted-table (degree c) (ambient c)
    (Short.generator-a c) (Short.generator-b c) (aTable c) (bTable c)
    (a-valid c) (b-valid c) (a-image-table c) (b-image-table c)
    (reflectionTerm c) (reflection-term-valid c) (sTable c) (s-valid c) (reflection-table-check c)

  rotation-word-image : (c : ShortCase) → rotationDownstairs c ≡ fst (inclusion c) (rotation c)
  rotation-word-image c = ambient-injective c (rotation-word-table c
    ∙ sym (ambient-inclusion c (rotation c) ∙ rotation-image-table c))

  reflection-word-image : (c : ShortCase) → reflectionDownstairs c ≡ fst (inclusion c) (reflection c)
  reflection-word-image c = ambient-injective c (reflection-word-table c
    ∙ sym (ambient-inclusion c (reflection c) ∙ reflection-image-table c))

-- Keep the concrete A₅ word behind eval. Expanding its nested inherited
-- 60-table multiplication while checking an alias causes needless reduction.
-- rotationTerm/reflectionTerm above retain exactly z, y x y⁻¹, y, v x v⁻¹.
abstract
  O-rotation-image : rotationDownstairs octa ≡ fst D₈→S₄ (rotation octa)
  O-rotation-image = rotation-word-image octa

  O-reflection-image : reflectionDownstairs octa ≡ fst D₈→S₄ (reflection octa)
  O-reflection-image = reflection-word-image octa

  I-rotation-image : rotationDownstairs icosa ≡ fst D₆→A₅ (rotation icosa)
  I-rotation-image = rotation-word-image icosa

  I-reflection-image : reflectionDownstairs icosa ≡ fst D₆→A₅ (reflection icosa)
  I-reflection-image = reflection-word-image icosa

  inclusion-injective : (c : ShortCase) {x y : fst (H c)}
    → fst (inclusion c) x ≡ fst (inclusion c) y → x ≡ y
  inclusion-injective octa = D₈-tables.embed-injective
  inclusion-injective icosa = D₆-inclusion.injective

  inclusion-image-nonabelian : (c : ShortCase) → NonabelianImage (inclusion c)
  inclusion-image-nonabelian c = PT.∣ rotation c , reflection c , (λ p →
    rotation-reflection-noncommute c (inclusion-injective c
      (IsGroupHom.pres· (snd (inclusion c)) (rotation c) (reflection c)
       ∙ p ∙ sym (IsGroupHom.pres· (snd (inclusion c)) (reflection c) (rotation c))))) ∣₁

-- Word identities use generic operations. This provides the
-- expanded noncommutative endpoints without reducing the A₅ table group.
module WordShapes (G : Group₀) where
  private module G = GroupStr (snd G)

  v : fst G → fst G → fst G
  v x y = ((x G.· G.inv y) G.· x) G.· y

  abstract
    O-rotation-shape : (x y : fst G)
      → eval G x y O-rotation-term ≡ WA.Words.z G x y
    O-rotation-shape x y = refl

    O-reflection-shape : (x y : fst G)
      → eval G x y O-reflection-term ≡ (y G.· x) G.· G.inv y
    O-reflection-shape x y = refl

    I-rotation-shape : (x y : fst G) → eval G x y I-rotation-term ≡ y
    I-rotation-shape x y = refl

    I-reflection-shape : (x y : fst G)
      → eval G x y I-reflection-term ≡ (v x y G.· x) G.· G.inv (v x y)
    I-reflection-shape x y = refl
