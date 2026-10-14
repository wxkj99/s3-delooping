{-# OPTIONS --cubical --safe --lossy-unification #-}
module DeloopS3.Bridge.Profile.BottomCofibre where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv using (isEquiv)
open import Cubical.Data.Sigma using (_×_)
open import Cubical.Data.Unit using (tt)
open import Cubical.Algebra.Group.Base using (Group₀)
open import Cubical.Algebra.Group.Morphisms using (GroupHom ; GroupEquiv)
open import Cubical.Algebra.Group.MorphismProperties using
  (compGroupEquiv ; invGroupEquiv)
open import Cubical.Algebra.Group.Instances.IntMod using (ℤGroup/_)
open import Cubical.HITs.Pushout.Base using (cofib)
open import Cubical.Homotopy.Connected using
  (isConnected ; isConnectedCofib ; isConnectedFunCancel'
  ; isConnected→isConnectedFun ; isConnectedSubtr)
import Cubical.HITs.PropositionalTruncation as PT

open import DeloopS3.Bridge.Profile.Types using (IProfile)
open import DeloopS3.Bridge.Profile.CofibreLES using (finite-cofibreLES-merely)
open import DeloopS3.Bridge.CofibreHomology using
  (CofibreLES ; finite-cofibreCW)
open import DeloopS3.Bridge.DMCExactness.Consequences using (bottom-cofib-homology)
open import DeloopS3.Bridge.Recognition.Notation using
  (CW₀ ; Finite≤ ; Hzero ; Hiso ; H̃ᶜʷ ; H̃ᶜʷ→)
open import DeloopS3.Bridge.Recognition.Hurewicz using (hurewicz-raise)
open import DeloopS3.Bridge.FiniteDim using
  (BottomMoore ; bottomCW ; bottom-finite≤ ; cofib-finite≤)
open import DeloopS3.Bridge.MooreMarked using (bottom-connected)

-- Keep the underlying type definitionally equal to the given HIT cofibre.
bottom-cofibCW : (X : CW₀) → Finite≤ 4 (fst X)
  → (BottomMoore → fst X) → CW₀
bottom-cofibCW X fin a =
  finite-cofibreCW bottomCW X a 3 4 bottom-finite≤ fin

private
  abstract
    -- Package the equivalence over arbitrary groups, before specializing
    -- to cellular homology and its potentially large endpoint expressions.
    pull-coordinates : (G H K : Group₀) (u : GroupHom G H)
      → isEquiv (fst u) → GroupEquiv G K → GroupEquiv H K
    pull-coordinates G H K u eu eG =
      compGroupEquiv (invGroupEquiv ((fst u , eu) , snd u)) eG

abstract
  bottom-cofib-simple : (X : Type) → isConnected 3 X
    → (a : BottomMoore → X) → isConnected 3 (cofib a)
  bottom-cofib-simple X simpleX a = isConnectedCofib 1 {f = a}
    (isConnectedFunCancel' a (λ (_ : X) → tt) 2
      (isConnected→isConnectedFun {X = X} 3 simpleX)
      (isConnected→isConnectedFun {X = BottomMoore} 2
        (isConnectedSubtr 2 1 bottom-connected)))

  bottom-cofib-profile : (X : CW₀) (p : IProfile X)
    (a : BottomMoore → fst X) → Hiso bottomCW X 2 a
    → PT.∥ Finite≤ 4 (cofib a)
        × isConnected 4 (cofib a)
        × GroupEquiv
            (H̃ᶜʷ (bottom-cofibCW X (IProfile.finite p) a) 3) (ℤGroup/ 10)
        × Hzero (bottom-cofibCW X (IProfile.finite p) a) 4 ∥₁
  bottom-cofib-profile X p a ea =
    PT.map
      {A = CofibreLES bottomCW X a F}
      {B = Finite≤ 4 (cofib a)
        × isConnected 4 (cofib a)
        × GroupEquiv (H̃ᶜʷ F 3) (ℤGroup/ 10)
        × Hzero F 4}
      from-LES
      (finite-cofibreLES-merely bottomCW X a 3 4
        bottom-finite≤ (IProfile.finite p))
    where
    F : CW₀
    F = bottom-cofibCW X (IProfile.finite p) a

    from-LES : CofibreLES bottomCW X a F
      → Finite≤ 4 (cofib a)
        × isConnected 4 (cofib a)
        × GroupEquiv (H̃ᶜʷ F 3) (ℤGroup/ 10)
        × Hzero F 4
    from-LES les =
      cofib-finite≤ a 3 4 bottom-finite≤ (IProfile.finite p) ,
      hurewicz-raise F 0
        (bottom-cofib-simple (fst X) (IProfile.simple p) a) (fst h) ,
      coordinates , snd (snd h)
      where
      i : fst X → fst F
      i = CofibreLES.inclusion bottomCW X a F les

      h : Hzero F 2 × Hiso X F 3 i × Hzero F 4
      h = bottom-cofib-homology X F a les ea (IProfile.H₄-zero p)

      u : GroupHom (H̃ᶜʷ X 3) (H̃ᶜʷ F 3)
      u = H̃ᶜʷ→ {C = X} {D = F} 3 i

      ei : isEquiv (fst u)
      ei = fst (snd h)

      coordinates : GroupEquiv (H̃ᶜʷ F 3) (ℤGroup/ 10)
      coordinates = pull-coordinates (H̃ᶜʷ X 3) (H̃ᶜʷ F 3) (ℤGroup/ 10)
        u ei (IProfile.H₃ p)
