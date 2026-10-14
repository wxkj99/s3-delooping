{-# OPTIONS --safe --cubical --guardedness #-}
module DeloopS3.HPInf.CommonSquare where

-- The common corner and its specified square homotopy.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function using (_∘_)
open import Cubical.Foundations.Pointed using (Pointed; typ; pt)
open import Cubical.Foundations.GroupoidLaws using (lUnit; rUnit)
open import Cubical.Foundations.HLevels using (isContrΣ; isContr→isContrPath)
open import Cubical.HITs.Pushout.Base using (push)
open import DeloopS3.Local.Base using (L; η)
open import DeloopS3.Local.Fracture.Arithmetic.Foundations using (PB)
open import DeloopS3.Assembly.LocalizationMaps using
  (L-map; overlap-map₃; overlap-map₁₀)
import DeloopS3.Assembly.Final.Geometry as G
import DeloopS3.Assembly.Final as Final
import DeloopS3.Assembly.DefB as DefB
import DeloopS3.Assembly.StarCube as Star
import DeloopS3.Assembly.MixedTruncation as Mixed
import DeloopS3.Assembly.LocalizedFibreNaturality as LF

B∙ : Pointed ℓ-zero
B∙ = DefB.B-def (G.Q G.octa) (G.Q G.icosa) G.T (G.u G.octa) (G.u G.icosa)

B : Type
B = typ B∙

TE : G.ShortCase → Type
TE c = L (G.m c) (G.E c)

TE* : Type
TE* = L 30 G.E*

v : (c : G.ShortCase) → TE c → TE*
v G.octa = overlap-map₃ (G.kE G.octa)
v G.icosa = overlap-map₁₀ (G.kE G.icosa)

pL : (c : G.ShortCase) → TE c → typ (G.Q c)
pL c = L-map (G.m c) (G.p c)

pL* : TE* → typ G.T
pL* = L-map 30 G.p*

module O = LF.Square 3 10 LF.left
  (G.E G.octa) (G.P G.octa) G.E* G.P*
  (G.p G.octa) G.p* (G.kE G.octa) (G.kP G.octa) refl
  (G.b G.octa) G.b* Star.bO

module I = LF.Square 3 10 LF.right
  (G.E G.icosa) (G.P G.icosa) G.E* G.P*
  (G.p G.icosa) G.p* (G.kE G.icosa) (G.kP G.icosa) refl
  (G.b G.icosa) G.b* Star.bI

HO : (x : TE G.octa)
  → pL* (v G.octa x) ≡ fst (G.u G.octa) (pL G.octa x)
HO = O.HᴸG

HI : (x : TE G.icosa)
  → pL* (v G.icosa x) ≡ fst (G.u G.icosa) (pL G.icosa x)
HI = I.HᴸG

ET : Type
ET = PB (v G.octa) (v G.icosa)

pT : ET → B
pT (x , y , s) = pL G.octa x , pL G.icosa y ,
  sym (HO x) ∙ cong pL* s ∙ HI y

seamR : (r : G.R)
  → G.kE G.octa (G.iR G.octa r) ≡ G.kE G.icosa (G.iR G.icosa r)
seamR r = push r

seamN : (n : G.N)
  → G.kP G.octa (G.jN G.octa n) ≡ G.kP G.icosa (G.jN G.icosa n)
seamN n = push n

base-seam : (n : G.N)
  → fst (G.u G.octa) (η {3} {G.P G.octa} (G.jN G.octa n))
    ≡ fst (G.u G.icosa) (η {10} {G.P G.icosa} (G.jN G.icosa n))
base-seam n = cong (η {30} {G.P*}) (seamN n)

alpha : G.R → ET
alpha r = η {3} {G.E G.octa} (G.iR G.octa r) ,
  η {10} {G.E G.icosa} (G.iR G.icosa r) ,
  cong (η {30} {G.E*}) (seamR r)

j : G.N → B
j n = η {3} {G.P G.octa} (G.jN G.octa n) ,
  η {10} {G.P G.icosa} (G.jN G.icosa n) , base-seam n

abstract
  H-seam : (r : G.R)
    → snd (snd (pT (alpha r))) ≡ base-seam (Mixed.u r)
  H-seam r =
    cong₂ (λ hO hI → sym hO ∙ base-seam (Mixed.u r) ∙ hI)
      (O.HᴸG-β (G.iR G.octa r)) (I.HᴸG-β (G.iR G.icosa r))
    ∙ sym (lUnit (base-seam (Mixed.u r) ∙ refl))
    ∙ sym (rUnit (base-seam (Mixed.u r)))

-- Only the seam moves: the first two coordinate paths are literally refl.
H : (r : G.R) → pT (alpha r) ≡ j (Mixed.u r)
H r k = η {3} {G.P G.octa} (G.jN G.octa (Mixed.u r)) ,
  η {10} {G.P G.icosa} (G.jN G.icosa (Mixed.u r)) , H-seam r k

H-fst : (r : G.R) → cong fst (H r) ≡ refl
H-fst r = refl

H-snd-fst : (r : G.R) → cong (fst ∘ snd) (H r) ≡ refl
H-snd-fst r = refl

abstract
  j-point-seam : base-seam G.n₀
    ≡ DefB.B-seam (G.Q G.octa) (G.Q G.icosa) G.T (G.u G.octa) (G.u G.icosa)
  j-point-seam = lUnit (base-seam G.n₀)
    ∙ lUnit (refl ∙ base-seam G.n₀)
    ∙ sym (doubleCompPath≡compPath refl refl (base-seam G.n₀))

j-point : j G.n₀ ≡ pt B∙
j-point k = η {3} {G.P G.octa} (G.b G.octa) ,
  η {10} {G.P G.icosa} (G.b G.icosa) , j-point-seam k

e₀ : ET
e₀ = alpha G.r₀

pT-point : pT e₀ ≡ pt B∙
pT-point = H G.r₀ ∙ j-point

abstract
  ET-contr : Final.HomologyProfileInput → isContr ET
  ET-contr h = isContrΣ (Final.HomologyProfileInput.contrO h) λ x →
    isContrΣ (Final.HomologyProfileInput.contrI h) λ y →
      isContr→isContrPath (Final.contrStar h) (v G.octa x) (v G.icosa y)
