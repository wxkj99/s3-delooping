{-# OPTIONS --cubical --safe #-}
module DeloopS3.Assembly.LocalizedLoops where

-- Localized fibre-loop equivalences and connectivity of their bases.
-- Library indexing: Conn = isConnected 2, SC = isConnected 3.
-- The base-connectivity argument needs only Conn of the fibre.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Data.Nat using (ℕ)
open import Cubical.Data.Unit using (Unit ; tt)
open import Cubical.Data.Sigma using (Σ-contractFst)
open import Cubical.Homotopy.Connected
  using (isConnected ; isConnectedFun ; isConnectedPath ;
         isConnectedFunCancel ; isConnected→isConnectedFun ;
         isConnectedFun→isConnected)
import Cubical.HITs.Truncation as Tr
open import DeloopS3.Local.Base using (L ; η)
open import DeloopS3.Local.RouteB2 using (Conn ; SC ; L-map)
import DeloopS3.Local.RouteB2 as B2

abstract
  -- Connectedness of the base transports the connectedness of one fibre
  -- to every fibre. The target proposition permits truncated elimination.
  connected-fibers : (E P : Type) (p : E → P) (b : P)
    → Conn P → Conn (fiber p b) → isConnectedFun 2 p
  connected-fibers E P p b cP cF y = Tr.rec isPropIsContr
    (λ q → subst (λ z → isConnected 2 (fiber p z)) q cF)
    (fst (isConnectedPath 1 cP b y))

  -- Explicit pointed data: e₀, b and p₀ : p e₀ ≡ b. A1 itself only
  -- needs b; the other two arguments align its interface with A2.
  P-sc-from-E-sc : (E P : Type) (p : E → P)
    (e₀ : E) (b : P) (p₀ : p e₀ ≡ b)
    → SC E → Conn P → Conn (fiber p b) → SC P
  P-sc-from-E-sc E P p e₀ b p₀ scE cP cF =
    isConnectedFun→isConnected {X = P} 3
      (isConnectedFunCancel {X = E} {Y = P} {Z = Unit}
        p (λ _ → tt) 2 (connected-fibers E P p b cP cF)
        (isConnected→isConnectedFun {X = E} 3 scE))

  -- Recenter the contraction at the specified point, not its original
  -- centre. This is the contractible-total-space fibre calculation.
  fiber-from-contractible : (E P : Type) (f : E → P)
    (e₀ : E) (y : P) → isContr E → fiber f y ≃ (f e₀ ≡ y)
  fiber-from-contractible E P f e₀ y cE =
    Σ-contractFst {A = E} {B = λ e → f e ≡ y}
      (e₀ , isContr→isProp cE e₀)

  -- This packages the RouteB2 fibre theorem without unfolding its proof.
  -- Its forward map extends B2.fiber-unit m p b along the localization unit.
  localized-fiber : (m : ℕ) (E P : Type) (p : E → P) (b : P)
    → SC P → L m (fiber p b) ≃ fiber (L-map m {A = E} {B = P} p) (η {m} {P} b)
  localized-fiber m E P p b scP =
    _ , B2.localization-preserves-fiber m {E = E} {B = P} p b scP

  -- The displayed path type is Ω(L m P, η b). No connectivity hypothesis
  -- on E, nor any choice of contraction centre compatible with η, is needed.
  loop-of-localization : (m : ℕ) (E P : Type) (p : E → P)
    (e₀ : E) (b : P) (p₀ : p e₀ ≡ b)
    → SC P → isContr (L m E)
    → (η {m} {P} b ≡ η {m} {P} b) ≃ L m (fiber p b)
  loop-of-localization m E P p e₀ b p₀ scP cLE =
    compEquiv
      (invEquiv
        (compEquiv
          (fiber-from-contractible (L m E) (L m P)
            (L-map m {A = E} {B = P} p) (η {m} {E} e₀) (η {m} {P} b) cLE)
          (compPathlEquiv (sym (cong (η {m} {P}) p₀)))))
      (invEquiv (localized-fiber m E P p b scP))

-- Contraction and fibre interfaces retain the maps of the abstract
-- equivalences above.
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.GroupoidLaws using (lUnit)

contractible-fiber-coordinate : (E P : Type) (f : E → P)
  (e₀ : E) (b : P) (p₀ : f e₀ ≡ b) → isContr E → fiber f b → b ≡ b
contractible-fiber-coordinate E P f e₀ b p₀ cE (x , s) =
  sym p₀ ∙ cong f (isContr→isProp cE e₀ x) ∙ s

abstract
  -- Transport along the reversed contraction is left composition by its
  -- image. This small path-induction lemma avoids unfolding Σ transport.
  fiber-contraction-transport : (E P : Type) (f : E → P)
    (e₀ x : E) (c : e₀ ≡ x) (b : P) (s : f x ≡ b)
    → subst (λ e → f e ≡ b) (sym c) s ≡ cong f c ∙ s
  fiber-contraction-transport E P f e₀ x c =
    J (λ x c → (b : P) (s : f x ≡ b)
      → subst (λ e → f e ≡ b) (sym c) s ≡ cong f c ∙ s)
      (λ b s → transportRefl s ∙ lUnit s) c

  fiber-from-contractible-map : (E P : Type) (f : E → P)
    (e₀ : E) (y : P) (cE : isContr E)
    → equivFun (fiber-from-contractible E P f e₀ y cE)
      ≡ (λ (v : fiber f y) → cong f (isContr→isProp cE e₀ (fst v)) ∙ snd v)
  fiber-from-contractible-map E P f e₀ y cE = funExt λ (x , s) →
    fiber-contraction-transport E P f e₀ x (isContr→isProp cE e₀ x) y s

  localized-fiber-map : (m : ℕ) (E P : Type) (f : E → P)
    (b : P) (sc : SC P)
    → equivFun (localized-fiber m E P f b sc) ≡ B2.fiber-comparison m f b
  localized-fiber-map m E P f b sc = refl

  loop-of-localization-inverse : (m : ℕ) (E P : Type) (f : E → P)
    (e₀ : E) (b : P) (p₀ : f e₀ ≡ b) (sc : SC P) (cLE : isContr (L m E))
    → invEq (loop-of-localization m E P f e₀ b p₀ sc cLE)
      ≡ contractible-fiber-coordinate (L m E) (L m P) (L-map m f)
          (η {m} {E} e₀) (η {m} {P} b) (cong (η {m} {P}) p₀) cLE
        ∘ B2.fiber-comparison m f b
  loop-of-localization-inverse m E P f e₀ b p₀ sc cLE =
    cong (λ k → (λ q → sym (cong (η {m} {P}) p₀) ∙ k q)
      ∘ B2.fiber-comparison m f b)
      (fiber-from-contractible-map (L m E) (L m P) (L-map m f)
        (η {m} {E} e₀) (η {m} {P} b) cLE)
