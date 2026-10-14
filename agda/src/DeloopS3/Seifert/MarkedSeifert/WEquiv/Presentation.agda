{-# OPTIONS --safe --cubical #-}

-- Computational encoding and decoding of mapping data in j,r coordinates.
module DeloopS3.Seifert.MarkedSeifert.WEquiv.Presentation where

open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Path using (compPathlEquiv)
open import Cubical.Data.Sigma
open import Cubical.HITs.Pushout.Base
open import Cubical.HITs.S1.Base using (base; loop)
open import DeloopS3.Move.CancelLoopCell using (powerEquiv; minus)
import DeloopS3.Seifert.MarkedSeifert.WInterface as R
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.Edge using (WHit; module Mapping)
open import DeloopS3.Seifert.MarkedSeifert.WEquiv.NielsenMapping using (module MappingJR)

module Computational {ℓ : Level} (X : Type ℓ) where
  private
    change : Mapping.RelationData X ≃ MappingJR.JRData X
    change = Σ-cong-equiv-snd λ a → Σ-cong-equiv-snd λ j →
      invEquiv (Σ-cong-equiv-fst {B = λ y → j ∙ j ≡ y ∙ y}
        (compEquiv (powerEquiv a minus) (compPathlEquiv j)))

  encode : (WHit → X) → MappingJR.JRData X
  encode f = change .fst (Mapping.hitEncode X f)
  decode : MappingJR.JRData X → WHit → X
  decode d = Mapping.hitDecode X (invEq change d)

  abstract
    encode-decode : (d : MappingJR.JRData X) → encode (decode d) ≡ d
    encode-decode d = cong (change .fst) (Mapping.hitEncodeDecode X (invEq change d))
      ∙ secEq change d
    decode-encode : (f : WHit → X) → decode (encode f) ≡ f
    decode-encode f = cong (Mapping.hitDecode X) (retEq change (Mapping.hitEncode X f))
      ∙ Mapping.hitDecodeEncode X f

canonical : MappingJR.JRData R.RelJR
canonical = R.vertex , R.j , R.r , R.relation

toJR : WHit → R.RelJR
toJR = Computational.decode R.RelJR canonical

native : MappingJR.JRData WHit
native = Computational.encode WHit (idfun WHit)

private
  compConcat : {ℓ : Level} {X : Type ℓ} {a b c : X}
    → a ≡ b → b ≡ c → a ≡ c
  compConcat {X = X} {a = a} p q i =
    comp (λ (_ : I) → X) (doubleComp-faces (refl {x = a}) q i) (p i)

  compConcatPath : {ℓ : Level} {X : Type ℓ} {a b c : X}
    (p : a ≡ b) (q : b ≡ c) → compConcat p q ≡ p ∙ q
  compConcatPath {X = X} {a = a} p q k i = hcomp
    (λ j o → transp (λ (_ : I) → X) (j ∨ k)
      (doubleComp-faces (refl {x = a}) q i j o))
    (transp (λ (_ : I) → X) k (p i))

  nj nr : native .fst ≡ native .fst
  nj = native .snd .fst
  nr = native .snd .snd .fst
  rightCorrection : compConcat (compConcat nj (sym nr)) (compConcat nj (sym nr))
    ≡ (nj ∙ sym nr) ∙ (nj ∙ sym nr)
  rightCorrection = compConcatPath (compConcat nj (sym nr)) (compConcat nj (sym nr))
    ∙ cong₂ _∙_ (compConcatPath nj (sym nr)) (compConcatPath nj (sym nr))

fromJR : R.RelJR → WHit
fromJR R.vertex = native .fst
fromJR (R.j i) = nj i
fromJR (R.r i) = nr i
fromJR (R.relation i k) =
  (compConcatPath nj nj ∙ native .snd .snd .snd ∙ sym rightCorrection) i k

-- toJR and fromJR are computational maps, not an equivalence package.
-- WRelJR constructs the marked HIT equivalence separately.
