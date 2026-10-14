{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.SourceCharacter.Filled where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.Data.Int using (ℤ)
open import Cubical.Data.Unit using (tt)
open import Cubical.Algebra.Group.Base
open import Cubical.Algebra.Group.Morphisms
open import Cubical.Algebra.Group.MorphismProperties using (compGroupHom; GroupEquiv→GroupHom)
open import Cubical.Homotopy.Group.Base using (πHom)
open import Cubical.Homotopy.Group.Properties using (connectedFun→πSurj)
open import Cubical.Homotopy.Connected using (isConnectedFun; isConnectedComp; isEquiv→isConnected; isConnectedRetractFromIso)
open import Cubical.HITs.Pushout.Base
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Move.CancelMinimal using (C; 0C)
open import DeloopS3.Cover.Orientation.CircleModel using (hC)
open import DeloopS3.Bridge.SpanPi1.Seam using (Π; πHom-loop)
open import DeloopS3.Bridge.SpanPi1.Fibre using (fibre-loop-null)
open import DeloopS3.Bridge.SpanPi1.Character using (KleinNF; KleinCharacter; C₂; zero₂)
open import DeloopS3.Bridge.SpanPi1.Connected using (circle-connected)
open import DeloopS3.Bridge.SpanPi1.SourceInclusion using (fill-inclusion; fill-inclusion-π-surjective)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Third using (Fill; cong-based)
open import DeloopS3.Seifert.MarkedSeifert.TorusFilling.Boundary using (based; based-refl)
import DeloopS3.Seifert.MarkedSeifert.TorusFilling.MappingTorus as M
import DeloopS3.Seifert.MarkedSeifert.TorusFilling.FilledLoops as Loops
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)
open import DeloopS3.Sphere.RP2UnitFiber using (RP²)
import DeloopS3.Bridge.SpanPi1.SourceCharacter.Klein as Klein
import DeloopS3.Bridge.SpanPi1.SourceCharacter.Algebra as Algebra
import DeloopS3.Bridge.SpanPi1.SourceCharacter.Cap as Cap

abstract
  based-unit : ∀ {ℓ} {X : Type ℓ} {a b : X} (p : a ≡ b) → based p refl ≡ refl
  based-unit p = J (λ b p → based p refl ≡ refl) (based-refl refl) p

  based-null-reflects : ∀ {ℓ} {X : Type ℓ} {a b : X} (p : a ≡ b) (l : a ≡ a)
    → based p l ≡ refl → l ≡ refl
  based-null-reflects p l = J (λ b p → based p l ≡ refl → l ≡ refl)
    (λ h → sym (based-refl l) ∙ h) p

  bundle-connected : (e : ℤ) → isConnectedFun 2 (Bundle.pₑ e)
  bundle-connected e b = PT.rec isPropIsContr
    (λ eq → isConnectedRetractFromIso 2 (equivToIso eq) circle-connected)
    (Bundle.circleFibres e b)

module Filled (e : ℤ) where
  module G = Cap.Geometry e
  module L = Loops.Filling e
  point : Fill e
  point = inl Klein.point
  P : Group₀
  P = Π (Fill e) point
  include : GroupHom Klein.P P
  include = πHom 0 (fill-inclusion e , refl)
  r j : fst P
  r = fst include Klein.r
  j = fst include Klein.j

  abstract
    generated : KleinNF P r j
    generated = Algebra.Image.generated Klein.P P include
      (fill-inclusion-π-surjective e Klein.point) Klein.r Klein.j Klein.generated

    inversion : GroupStr._·_ (snd P) j r ≡ GroupStr._·_ (snd P) (GroupStr.inv (snd P) r) j
    inversion = Algebra.Image.inversion Klein.P P include
      (fill-inclusion-π-surjective e Klein.point) Klein.r Klein.j Klein.inversion

    core-loop-null : cong G.projection (cong L.core hC) ≡ refl
    core-loop-null = fibre-loop-null G.projection L.coreBase (inr tt)
      (G.core-null 0C) (λ i → L.core (hC i) , G.core-null (hC i))

    old-r-null : cong (G.projection ∘ L.include) M.r ≡ refl
    old-r-null = based-null-reflects (cong G.projection L.seam)
      (cong (G.projection ∘ L.include) M.r)
      (sym (cong-based G.projection L.seam (cong L.include M.r))
        ∙ cong (cong G.projection) L.fibre-is-core ∙ core-loop-null)

    r-loop-null : cong (G.projection ∘ L.include) Klein.rLoop ≡ refl
    r-loop-null = cong (cong (G.projection ∘ L.include)) (sym Klein.r-mark)
      ∙ cong-based (G.projection ∘ L.include) M.klein-base M.r
      ∙ cong (based (cong (G.projection ∘ L.include) M.klein-base)) old-r-null
      ∙ based-unit (cong (G.projection ∘ L.include) M.klein-base)

    q-r : fst (πHom 0 (G.projection , refl)) r
      ≡ GroupStr.1g (snd (Π RP² (G.projection point)))
    q-r = cong (fst (πHom 0 (G.projection , refl)))
      (πHom-loop L.include Klein.point Klein.rLoop)
      ∙ πHom-loop G.projection point (cong L.include Klein.rLoop)
      ∙ cong ST.∣_∣₂ r-loop-null

    q-connected : isConnectedFun 2 G.projection
    q-connected = subst (isConnectedFun 2) (sym G.projection-map)
      (isConnectedComp {A = Fill e} {B = Bundle.Mₑ e} {C = RP²}
        (Bundle.pₑ e) (fst G.equivalence) 2 (bundle-connected e)
        (isEquiv→isConnected (fst G.equivalence) (snd G.equivalence) 2))

  character : (rp : GroupEquiv (Π RP² (G.projection point)) C₂)
    → KleinCharacter P (compGroupHom (πHom 0 (G.projection , refl)) (GroupEquiv→GroupHom rp))
  character rp = Algebra.character P χ r j inversion generated r-zero onto where
    χ : GroupHom P C₂
    χ = compGroupHom (πHom 0 (G.projection , refl)) (GroupEquiv→GroupHom rp)
    r-zero : fst χ r ≡ zero₂
    r-zero = cong (fst (fst rp)) q-r ∙ IsGroupHom.pres1 (snd rp)
    onto : (v : fst C₂) → PT.∥ fiber (fst χ) v ∥₁
    onto v = PT.map (λ { (u , p) → u , cong (fst (fst rp)) p ∙ secEq (fst rp) v })
      (connectedFun→πSurj 0 (G.projection , refl) q-connected (invEq (fst rp) v))
