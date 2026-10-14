{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.MooreMarked.Marked where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Isomorphism
open import Cubical.Data.Nat using (ℕ ; zero ; suc)
open import Cubical.Data.Nat.Order using (_<_ ; ¬-<-zero)
open import Cubical.Data.Unit using (tt)
open import Cubical.Algebra.Group.Morphisms using (GroupEquiv ; GroupHom)
open import Cubical.Algebra.Group.MorphismProperties using (GroupIso→GroupHom ; compGroupHom)
open import Cubical.Algebra.Group.Instances.Int using (ℤGroup)
open import Cubical.Data.Int using (pos)
import Cubical.Data.Empty as Empty
open import Cubical.CW.Instances.Sn using (Sᶜʷ)
open import Cubical.CW.Homology.Groups.Sn using (ℤ≅HₙSⁿ)
import DeloopS3.Bridge.MooreMarked.Quotient as Quotient
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.Homotopy.Connected
open import Cubical.HITs.Sn using (sphereConnected)
open import Cubical.HITs.Susp using (north)
open import Cubical.HITs.Pushout using (cofib ; inr)
open import Cubical.CW.HurewiczTheorem using (HurewiczMapUntrunc)
open import DeloopS3.Local.EI using (BottomMoore)
open import DeloopS3.Local.Powers using (degSphere)
open import DeloopS3.Bridge.Recognition.Notation using (H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.Recognition.Models using (moore3CW ; bottomCW ; moore3-connected)
open import DeloopS3.Bridge.Recognition.Degree using (degree-degSphere-S² ; degree-degSphere-S³)
open import DeloopS3.Bridge.MooreMarked.Cyclic using (oneMod ; positive₂)
open import DeloopS3.Bridge.MooreMarked.Bouquet using (one-map ; one-cofibre ; module Concrete)

abstract
  bottom-connected : isConnected 3 BottomMoore
  bottom-connected = isConnectedCofib 1
    (isConnectedFunCancel' (degSphere 2 1) (λ _ → tt) 2
      (isConnected→isConnectedFun 3 (sphereConnected 2))
      (isConnected→isConnectedFun 2 (isConnectedSubtr 2 1 (sphereConnected 2))))

private
  abstract
    moore-bouquet-connected : (m : ℕ) → isConnected 2 (cofib (one-map (degSphere m 2)))
    moore-bouquet-connected m = isConnectedRetractFromIso 2
      (equivToIso (one-cofibre (degSphere m 2)))
      (isConnectedSubtr 2 2 (moore3-connected m))

    bottom-bouquet-connected : isConnected 2 (cofib (one-map (degSphere 2 1)))
    bottom-bouquet-connected = isConnectedRetractFromIso 2
      (equivToIso (one-cofibre (degSphere 2 1)))
      (isConnectedSubtr 2 1 bottom-connected)

  module M (m : ℕ) = Concrete (degSphere m 2) refl (snd (moore3CW m)) (moore-bouquet-connected m)
  module B = Concrete (degSphere 2 1) refl (snd bottomCW) bottom-bouquet-connected

  opaque
    integer-bottom3 : (m : ℕ) → GroupHom ℤGroup (H̃ᶜʷ (moore3CW m) 3)
    integer-bottom3 m = compGroupHom (GroupIso→GroupHom (ℤ≅HₙSⁿ 2))
      (H̃ᶜʷ→ {C = Sᶜʷ 3} {D = moore3CW m} 3 inr)

    integer-bottom2 : GroupHom ℤGroup (H̃ᶜʷ bottomCW 2)
    integer-bottom2 = compGroupHom (GroupIso→GroupHom (ℤ≅HₙSⁿ 1))
      (H̃ᶜʷ→ {C = Sᶜʷ 2} {D = bottomCW} 2 inr)

  opaque
    unfolding integer-bottom3 integer-bottom2
    integer-bottom3-one : (m : ℕ)
      → fst (integer-bottom3 m) (pos 1)
        ≡ HurewiczMapUntrunc {n = 2} (moore3CW m) (inr north) (inr , refl)
    integer-bottom3-one m = refl

    integer-bottom2-one : fst integer-bottom2 (pos 1)
      ≡ HurewiczMapUntrunc {n = 1} bottomCW (inr north) (inr , refl)
    integer-bottom2-one = refl

  module Rebuilt3 (m : ℕ) (positive : 0 < suc m) where
    seed : GroupEquiv (H̃ᶜʷ (moore3CW (suc m)) 3) (ℤGroup/ suc m)
    seed = M.marked (suc m) (suc m) positive (degree-degSphere-S³ (suc m))
    module Q = Quotient.Modulus m
    module C = Q.Calibrate (H̃ᶜʷ (moore3CW (suc m)) 3) (integer-bottom3 (suc m)) seed
      (cong (equivFun (fst seed)) (integer-bottom3-one (suc m))
       ∙ M.marked-generator (suc m) (suc m) positive (degree-degSphere-S³ (suc m)))

  module Rebuilt2 where
    seed : GroupEquiv (H̃ᶜʷ bottomCW 2) (ℤGroup/ 2)
    seed = B.marked 2 positive₂ (degree-degSphere-S² 2)
    module Q = Quotient.Modulus 1
    module C = Q.Calibrate (H̃ᶜʷ bottomCW 2) integer-bottom2 seed
      (cong (equivFun (fst seed)) integer-bottom2-one
       ∙ B.marked-generator 2 positive₂ (degree-degSphere-S² 2))

-- The final equivalences are inverses of the quotient-UP maps defined
-- on the ACTUAL integer bottom inclusion, not the seed coordinates.
opaque
  moore3-H₃-marked : (m : ℕ) (positive : 0 < m)
    → GroupEquiv (H̃ᶜʷ (moore3CW m) 3) (ℤGroup/ m)
  moore3-H₃-marked zero positive = Empty.rec (¬-<-zero positive)
  moore3-H₃-marked (suc m) positive = Rebuilt3.C.marked-from-bottom m positive

  bottom-H₂-marked : GroupEquiv (H̃ᶜʷ bottomCW 2) (ℤGroup/ 2)
  bottom-H₂-marked = Rebuilt2.C.marked-from-bottom

opaque
  unfolding moore3-H₃-marked bottom-H₂-marked
  moore3-bottom-generator : (m : ℕ) (positive : 0 < m)
    → equivFun (fst (moore3-H₃-marked m positive))
        (HurewiczMapUntrunc {n = 2} (moore3CW m) (inr north) (inr , refl))
      ≡ oneMod m positive
  moore3-bottom-generator zero positive = Empty.rec (¬-<-zero positive)
  moore3-bottom-generator (suc m) positive =
    cong (equivFun (fst (moore3-H₃-marked (suc m) positive))) (sym (integer-bottom3-one (suc m)))
    ∙ Rebuilt3.C.marked-from-bottom-generator m positive

  bottom-bottom-generator :
    equivFun (fst bottom-H₂-marked)
      (HurewiczMapUntrunc {n = 1} bottomCW (inr north) (inr , refl))
    ≡ oneMod 2 positive₂
  bottom-bottom-generator = cong (equivFun (fst bottom-H₂-marked)) (sym integer-bottom2-one)
    ∙ Rebuilt2.C.marked-from-bottom-generator
