{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.Bridge.SpanPi1.TargetGeneration where

-- The dependent universal property of pushout path spaces.  The base
-- overlap in each component supplies its unique tree edge.  Its entire
-- torus can be reduced to that point because the seam obligation is a
-- proposition.  In particular no edge generator or prism relation is
-- silently added to the fundamental group.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.HLevels
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.GroupoidLaws
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base using (push)
import Cubical.HITs.Pushout.KrausVonRaumer as KV
import Cubical.HITs.SetTruncation as ST
import Cubical.HITs.PropositionalTruncation as PT
open import DeloopS3.Cert.Interpret.Short using (ShortCase)
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Interpret.Realization as R
import DeloopS3.Cert.Input.Model as Model
open import DeloopS3.Bridge.SpanPi1.TargetLoops
open import DeloopS3.Bridge.SpanPi1.TargetVertexGeneration
open import DeloopS3.Bridge.SpanPi1.Connected using (circle-paths)

abstract
  cancel-inverse-tail : ∀ {ℓ} {A : Type ℓ} {a b d : A}
    (p : a ≡ b) (q : d ≡ b) → (p ∙ sym q) ∙ q ≡ p
  cancel-inverse-tail p q = sym (assoc p (sym q) q)
    ∙ cong (p ∙_) (lCancel q) ∙ sym (rUnit p)

  close-edge : ∀ {ℓ} {A : Type ℓ} {a b : A}
    (p : a ≡ a) (e : a ≡ b)
    → ((p ∙ e) ∙ refl) ∙ sym e ≡ p
  close-edge p e = cong (_∙ sym e) (sym (rUnit (p ∙ e)))
    ∙ sym (assoc p e (sym e)) ∙ cong (p ∙_) (rCancel e) ∙ sym (rUnit p)

  inverse-conjugate-tail : ∀ {ℓ} {A : Type ℓ} {a b : A}
    (p : a ≡ a) (e : a ≡ b) (q : b ≡ b)
    → ((p ∙ e) ∙ sym q) ∙ sym e ≡ p ∙ sym (e ∙∙ q ∙∙ sym e)
  inverse-conjugate-tail {a = a} p e = J
    (λ b e → (q : b ≡ b)
      → ((p ∙ e) ∙ sym q) ∙ sym e ≡ p ∙ sym (e ∙∙ q ∙∙ sym e))
    (λ q → sym (rUnit ((p ∙ refl) ∙ sym q))
      ∙ cong (_∙ sym q) (sym (rUnit p))
      ∙ cong (λ t → p ∙ sym t) (rUnit q)) e

module Generation (c : ShortCase) where
  open Vertices c

  LCode : (b : Model.Γ × R.C) → m₀ c ≡ leftIncl b → Type₀
  LCode b p = PT.∥ Σ[ q ∈ Path (Model.Γ × R.C) (R.root , R.0C) b ]
    GenPath (p ∙ sym (cong leftIncl q)) ∥₁

  RCode : (v : Ch.Kind × R.C) → m₀ c ≡ coreCircle c (fst v) (snd v) → Type₀
  RCode (k , u) p = PT.∥ Σ[ q ∈ Path R.C R.0C u ]
    GenPath ((p ∙ sym (cong (coreCircle c k) q)) ∙ sym (coreEdge c k)) ∥₁

  abstract
    insert-left : (p : m₀ c ≡ m₀ c) → GenPath p → LCode (R.root , R.0C) p
    insert-left p gp = PT.∣ refl , subst GenPath (rUnit p) gp ∣₁

    extract-left : (p : m₀ c ≡ m₀ c) → LCode (R.root , R.0C) p → GenPath p
    extract-left p = PT.rec PT.squash₁ (λ { (q , gq) → subst GenPath
      (cancel-inverse-tail p (cong leftIncl q)) (product gq (left-loop-generated q)) })

    insert-right : (k : Ch.Kind) (p : m₀ c ≡ m₀ c) → GenPath p
      → RCode (k , R.0C) (p ∙ coreEdge c k)
    insert-right k p gp = PT.∣ refl , subst GenPath (sym (close-edge p (coreEdge c k))) gp ∣₁

    extract-right : (k : Ch.Kind) (p : m₀ c ≡ m₀ c)
      → RCode (k , R.0C) (p ∙ coreEdge c k) → GenPath p
    extract-right k p = PT.rec PT.squash₁ (λ { (q , gq) → subst GenPath
      (cancel-inverse-tail p (coreEdge c k ∙∙ cong (coreCircle c k) q ∙∙ sym (coreEdge c k)))
      (product (subst GenPath (inverse-conjugate-tail p (coreEdge c k) (cong (coreCircle c k) q)) gq)
        (core-loop-generated k q)) })

    seam-base : (k : Ch.Kind) (p : m₀ c ≡ m₀ c)
      → LCode (R.root , R.0C) p ≃ RCode (k , R.0C) (p ∙ coreEdge c k)
    seam-base k p = propBiimpl→Equiv PT.squash₁ PT.squash₁
      (λ gp → insert-right k p (extract-left p gp))
      (λ gp → insert-left p (extract-right k p gp))

  Seam : (k : Ch.Kind) → R.T² → Type₀
  Seam k t = (p : m₀ c ≡ leftIncl (R.Span.left (Model.BaseSpan c) (k , t)))
    → LCode (R.Span.left (Model.BaseSpan c) (k , t)) p
      ≃ RCode (R.Span.right (Model.BaseSpan c) (k , t)) (p ∙ push (k , t))

  abstract
    seam : (a : Ch.Kind × R.T²)
      (p : m₀ c ≡ leftIncl (R.Span.left (Model.BaseSpan c) a))
      → LCode (R.Span.left (Model.BaseSpan c) a) p
        ≃ RCode (R.Span.right (Model.BaseSpan c) a) (p ∙ push a)
    seam (k , u , t) = PT.rec (isPropΠ (λ _ → isOfHLevel≃ 1 PT.squash₁ PT.squash₁))
      (λ qu → PT.rec (isPropΠ (λ _ → isOfHLevel≃ 1 PT.squash₁ PT.squash₁))
        (λ qt → subst (Seam k) (λ i → qu i , qt i) (seam-base k))
        (circle-paths t)) (circle-paths u)

  module Paths = KV.ElimL LCode RCode (insert-left refl one) seam

  abstract
    loop-generated : (p : m₀ c ≡ m₀ c) → GenPath p
    loop-generated p = extract-left p (Paths.elimL (R.root , R.0C) p)

    generated : (u : fst (G c)) → Generated u
    generated = ST.elim (λ _ → isProp→isSet PT.squash₁) loop-generated
