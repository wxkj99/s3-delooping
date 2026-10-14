{-# OPTIONS --safe --cubical #-}
module DeloopS3.Groups.Concrete where

-- Concrete permutation groups from finite table certificates,
-- with group laws obtained by reflected closure and ambient inheritance.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Data.SumFin using (discreteFin)
open import Cubical.Relation.Nullary using (EquivPresDiscrete)
open import Cubical.Algebra.Group.Base using (Group₀)
open import Cubical.Algebra.Group.Morphisms using (GroupHom)
open import Cubical.Algebra.SymmetricGroup using (FinSymGroup; ⟨Sym⟩≃factorial)
open import DeloopS3.Groups.Enumerated
import DeloopS3.Cert.Check as C
import DeloopS3.Cert.Octa3 as O
import DeloopS3.Cert.Icosa10 as I

abstract
  S₄-checked : CheckedTables 4 (C.group O.cert)
  CheckedTables.permutations S₄-checked = refl
  CheckedTables.distinct S₄-checked = refl
  CheckedTables.unit-closed S₄-checked = refl
  CheckedTables.product-closed S₄-checked = refl
  CheckedTables.inverse-closed S₄-checked = refl

  A₅-checked : CheckedTables 5 (C.group I.cert)
  CheckedTables.permutations A₅-checked = refl
  CheckedTables.distinct A₅-checked = refl
  CheckedTables.unit-closed A₅-checked = refl
  CheckedTables.product-closed A₅-checked = refl
  CheckedTables.inverse-closed A₅-checked = refl

  D₈-checked : CheckedTables 4 (C.subgroup O.cert)
  CheckedTables.permutations D₈-checked = refl
  CheckedTables.distinct D₈-checked = refl
  CheckedTables.unit-closed D₈-checked = refl
  CheckedTables.product-closed D₈-checked = refl
  CheckedTables.inverse-closed D₈-checked = refl

  D₆-checked : CheckedTables 5 (C.subgroup I.cert)
  CheckedTables.permutations D₆-checked = refl
  CheckedTables.distinct D₆-checked = refl
  CheckedTables.unit-closed D₆-checked = refl
  CheckedTables.product-closed D₆-checked = refl
  CheckedTables.inverse-closed D₆-checked = refl

module S₄-tables = FromTables 4 (C.group O.cert) S₄-checked
module A₅-tables = FromTables 5 (C.group I.cert) A₅-checked
module D₈-tables = FromTables 4 (C.subgroup O.cert) D₈-checked
module D₆-tables = FromTables 5 (C.subgroup I.cert) D₆-checked

S₄ A₅ D₈ D₆ : Group₀
S₄ = FinSymGroup 4
A₅ = A₅-tables.group
D₈ = D₈-tables.group
D₆ = D₆-tables.group

S₄-data : ConcreteGroup 24
ConcreteGroup.group S₄-data = S₄
ConcreteGroup.enumerate S₄-data = ⟨Sym⟩≃factorial 4
ConcreteGroup.decEq S₄-data = EquivPresDiscrete (invEquiv (⟨Sym⟩≃factorial 4)) discreteFin

A₅-data : ConcreteGroup 60
A₅-data = A₅-tables.concrete

D₈-data : ConcreteGroup 8
D₈-data = D₈-tables.concrete

D₆-data : ConcreteGroup 6
D₆-data = D₆-tables.concrete

D₈→S₄ : GroupHom D₈ S₄
D₈→S₄ = D₈-tables.embedding

A₅→S₅ : GroupHom A₅ (FinSymGroup 5)
A₅→S₅ = A₅-tables.embedding

-- These witnesses validate the finite coset certificates; their types are
-- Boolean checks, rather than semantic coset-space equivalences.
index₃-certificate : C.checkCosets O.cert ≡ C.true
index₃-certificate = O.cosets-ok

index₁₀-certificate : C.checkCosets I.cert ≡ C.true
index₁₀-certificate = I.cosets-ok
