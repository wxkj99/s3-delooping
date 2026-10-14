{-# OPTIONS --safe --cubical --guardedness --no-import-sorts #-}
module DeloopS3.Cert.Interpret.Short where

-- Finite certificate interpretation and assembly from specified endpoint charts.
-- Cert.Interpret.Done supplies the concrete endpoint data.
open import Cubical.Foundations.Prelude
open import Cubical.Foundations.Function
open import Cubical.Foundations.Equiv
open import Cubical.Foundations.Univalence using (pathToEquiv)
open import Cubical.Data.Sigma
open import Cubical.Data.Nat using (ℕ; suc)
open import Cubical.Data.Bool using (true; _and_)
open import Cubical.Data.List.Base using (List; []; _∷_)
import DeloopS3.Cert.Perm as P
import DeloopS3.Cert.Check as Ch
import DeloopS3.Cert.Octa3 as Octa
import DeloopS3.Cert.Icosa10 as Icosa
open import DeloopS3.Cert.Interpret.Syntax
open import DeloopS3.Cert.Interpret.Realization
open import DeloopS3.Cert.Interpret.Realized
import DeloopS3.Cert.Interpret.Cancel as Cancel
import DeloopS3.Cert.Interpret.Terminal as Terminal

abstract
  step-sound : (ct : Ch.Certificate) (S S′ : Ch.State) (m : Move)
    → WellFormed (suc (Ch.index ct)) S
    → checkMove ct S m S′ ≡ true
    → RealizedStep (suc (Ch.index ct)) S S′
  step-sound ct S S′ (cancel s) wf ok = Cancel.cancel-step-sound ct S S′ s wf
    (checkMove-clause {ct = ct} {S = S} {S′ = S′} {m = cancel s} ok)
  step-sound ct S S′ (basis₂ b) = Terminal.basis₂-sound ct S S′ b
  step-sound ct S S′ unshear = Terminal.unshear-sound ct S S′
  step-sound ct S S′ (gauge zs) = Terminal.gauge-sound ct S S′ zs

  run-frames-sound : (ct : Ch.Certificate) (S : Ch.State) (fs : List Frame)
    → WellFormed (suc (Ch.index ct)) S
    → checkRun ct S fs ≡ true → T S ≃ T (endState S fs)
  run-frames-sound ct S [] wf ok = idEquiv (T S)
  run-frames-sound ct S (f ∷ fs) wf ok = compEquiv
    {A = T S} {B = T (next f)} {C = T (endState (next f) fs)}
    (RealizedStep.total step)
    (run-frames-sound ct (next f) fs (RealizedStep.next-wf step)
      (checkRun-tail {ct = ct} {S = S} {f = f} {fs = fs} ok))
    where
    step : RealizedStep (suc (Ch.index ct)) S (next f)
    step = step-sound ct S (next f) (instruction f) wf
      (checkRun-head {ct = ct} {S = S} {f = f} {fs = fs} ok)

  run-sound : (ct : Ch.Certificate) (p : Program)
    → CheckedProgram ct p → T (initial p) ≃ T (finish p)
  run-sound ct p ok = run-frames-sound ct (initial p) (frames p)
    (wf-reflect (initial-wf ok)) (moves-ok ok)

  -- Reuse the generated check, adding only syntactic well-formedness.
  cancel-ok : (ct : Ch.Certificate) (S S′ : Ch.State) (s : Ch.Step)
    → wfB (suc (Ch.index ct)) S ≡ true
    → Ch.checkStep ct S s S′ ≡ true
    → checkMove ct S (cancel s) S′ ≡ true
  cancel-ok ct S S′ s wf ok = and-intro wf (and-intro
    (wf-reify {n = suc (Ch.index ct)} {S = S′}
      (advance-wf {n = suc (Ch.index ct)} {S = S} {S′ = S′} {ct = ct} {s = s}
        (wf-reflect {n = suc (Ch.index ct)} {S = S} wf) ok refl)) ok)

  cons-ok : (ct : Ch.Certificate) (S : Ch.State) (f : Frame) (fs : List Frame)
    → checkMove ct S (instruction f) (next f) ≡ true
    → checkRun ct (next f) fs ≡ true → checkRun ct S (f ∷ fs) ≡ true
  cons-ok ct S f fs = and-intro

data ShortCase : Type₀ where
  octa icosa : ShortCase

certOf : ShortCase → Ch.Certificate
certOf octa = Octa.cert
certOf icosa = Icosa.cert

exponentOf : ShortCase → ℕ
exponentOf octa = 4
exponentOf icosa = 3

standard : ℕ → Ch.State
standard e = Ch.state twoGenerators
  (Ch.face 0 2 (P.pos 1) (P.fwd 1 ∷ []) (P.pos 0) ∷
   Ch.face 1 2 (P.pos 1) (P.fwd 2 ∷ []) (P.pos 0) ∷
   Ch.face 2 e (P.pos 1 P.-z P.pos e) (P.bwd 2 ∷ P.bwd 1 ∷ []) (P.pos 0) ∷ [])

-- This is the interpreter's rose/finite-position model, not Bundle.Mₑ,
-- nor definitionally MarkedSeifert.WEquiv.M22e (which uses another span).
M22e : ℕ → Type₀
M22e e = T (standard e)

basis-O basis-I : Basis2
basis-O = basis2
  ((P.fwd 2 ∷ []) ∷ (P.bwd 2 ∷ P.bwd 1 ∷ []) ∷ [])
  ((P.bwd 4 ∷ P.bwd 3 ∷ []) ∷ (P.fwd 3 ∷ []) ∷ [])
  (Ch.ordered Octa.normalized)
basis-I = basis2
  ((P.fwd 2 ∷ []) ∷ (P.bwd 2 ∷ P.bwd 1 ∷ []) ∷ [])
  ((P.bwd 11 ∷ P.bwd 9 ∷ []) ∷ (P.fwd 9 ∷ []) ∷ [])
  (Ch.ordered Icosa.normalized)

-- Small literal terminal snapshots, in U,V,W order.
based-O based-I unsheared-O unsheared-I : Ch.State
based-O = Ch.state twoGenerators
  (Ch.face 0 2 (P.neg 2) (P.fwd 1 ∷ []) (P.neg 0) ∷
   Ch.face 1 2 (P.pos 1) (P.fwd 2 ∷ []) (P.pos 0) ∷
   Ch.face 2 4 (P.neg 2) (P.bwd 2 ∷ P.bwd 1 ∷ []) (P.neg 0) ∷ [])
based-I = Ch.state twoGenerators
  (Ch.face 0 2 (P.pos 1) (P.fwd 1 ∷ []) (P.pos 0) ∷
   Ch.face 1 2 (P.pos 1) (P.fwd 2 ∷ []) (P.pos 0) ∷
   Ch.face 2 3 (P.pos 1) (P.bwd 2 ∷ P.bwd 1 ∷ []) (P.pos 1) ∷ [])
unsheared-O = unshearState based-O
unsheared-I = unshearState based-I

gauge-O gauge-I : List P.Z
gauge-O = P.pos 1 ∷ P.pos 0 ∷ []
gauge-I = P.pos 0 ∷ P.pos 0 ∷ []

terminalFrames-O terminalFrames-I : List Frame
terminalFrames-O = frame (basis₂ basis-O) based-O ∷
  frame unshear unsheared-O ∷ frame (gauge gauge-O) (standard 4) ∷ []
terminalFrames-I = frame (basis₂ basis-I) based-I ∷
  frame unshear unsheared-I ∷ frame (gauge gauge-I) (standard 3) ∷ []

shortProgram : ShortCase → Program
shortProgram octa = program Octa.state-0
  (frame (cancel Octa.move-0) Octa.state-1 ∷
   frame (cancel Octa.move-1) Octa.state-2 ∷ terminalFrames-O)
shortProgram icosa = program Icosa.state-0
  (frame (cancel Icosa.move-0) Icosa.state-1 ∷
   frame (cancel Icosa.move-1) Icosa.state-2 ∷
   frame (cancel Icosa.move-2) Icosa.state-3 ∷
   frame (cancel Icosa.move-3) Icosa.state-4 ∷
   frame (cancel Icosa.move-4) Icosa.state-5 ∷
   frame (cancel Icosa.move-5) Icosa.state-6 ∷
   frame (cancel Icosa.move-6) Icosa.state-7 ∷
   frame (cancel Icosa.move-7) Icosa.state-8 ∷
   frame (cancel Icosa.move-8) Icosa.state-9 ∷ terminalFrames-I)

abstract
  terminal-ok-O : checkRun Octa.cert Octa.state-2 terminalFrames-O ≡ true
  terminal-ok-O = refl
  terminal-ok-I : checkRun Icosa.cert Icosa.state-9 terminalFrames-I ≡ true
  terminal-ok-I = refl

  shortProgram-ok : (c : ShortCase) → CheckedProgram (certOf c) (shortProgram c)
  initial-wf (shortProgram-ok octa) = refl
  moves-ok (shortProgram-ok octa) =
    and-intro (cancel-ok Octa.cert Octa.state-0 Octa.state-1 Octa.move-0 refl Octa.move-0-ok)
    (and-intro (cancel-ok Octa.cert Octa.state-1 Octa.state-2 Octa.move-1 refl Octa.move-1-ok)
      terminal-ok-O)
  initial-wf (shortProgram-ok icosa) = refl
  moves-ok (shortProgram-ok icosa) =
    and-intro (cancel-ok Icosa.cert Icosa.state-0 Icosa.state-1 Icosa.move-0 refl Icosa.move-0-ok)
    (and-intro (cancel-ok Icosa.cert Icosa.state-1 Icosa.state-2 Icosa.move-1 refl Icosa.move-1-ok)
    (and-intro (cancel-ok Icosa.cert Icosa.state-2 Icosa.state-3 Icosa.move-2 refl Icosa.move-2-ok)
    (and-intro (cancel-ok Icosa.cert Icosa.state-3 Icosa.state-4 Icosa.move-3 refl Icosa.move-3-ok)
    (and-intro (cancel-ok Icosa.cert Icosa.state-4 Icosa.state-5 Icosa.move-4 refl Icosa.move-4-ok)
    (and-intro (cancel-ok Icosa.cert Icosa.state-5 Icosa.state-6 Icosa.move-5 refl Icosa.move-5-ok)
    (and-intro (cancel-ok Icosa.cert Icosa.state-6 Icosa.state-7 Icosa.move-6 refl Icosa.move-6-ok)
    (and-intro (cancel-ok Icosa.cert Icosa.state-7 Icosa.state-8 Icosa.move-7 refl Icosa.move-7-ok)
    (and-intro (cancel-ok Icosa.cert Icosa.state-8 Icosa.state-9 Icosa.move-8 refl Icosa.move-8-ok)
      terminal-ok-I))))))))

  shortProgram-start : (c : ShortCase)
    → initial (shortProgram c) ≡ Ch.initialState (certOf c)
  shortProgram-start octa = stateEq-sound Octa.state-0 (Ch.initialState Octa.cert) Octa.initial-state-ok
  shortProgram-start icosa = stateEq-sound Icosa.state-0 (Ch.initialState Icosa.cert) Icosa.initial-state-ok

  shortProgram-end : (c : ShortCase)
    → finish (shortProgram c) ≡ standard (exponentOf c)
  shortProgram-end octa = refl
  shortProgram-end icosa = refl

  shortProgram-length : (c : ShortCase) → P.length (frames (shortProgram c)) ≡
    (case c of λ { octa → 5 ; icosa → 12 })
  shortProgram-length octa = refl
  shortProgram-length icosa = refl

  normalize-short : (c : ShortCase)
    → T (Ch.initialState (certOf c)) ≃ M22e (exponentOf c)
  normalize-short c = compEquiv
    {A = T (Ch.initialState (certOf c))} {B = T (initial (shortProgram c))}
    {C = M22e (exponentOf c)}
    (pathToEquiv (cong T (sym (shortProgram-start c))))
    (compEquiv {A = T (initial (shortProgram c))} {B = T (finish (shortProgram c))}
      {C = M22e (exponentOf c)}
      (run-sound (certOf c) (shortProgram c) (shortProgram-ok c))
      (pathToEquiv (cong T (shortProgram-end c))))

  terminal-O : T Octa.state-2 ≃ M22e 4
  terminal-O = run-frames-sound Octa.cert Octa.state-2 terminalFrames-O (wf-reflect refl) terminal-ok-O
  terminal-I : T Icosa.state-9 ≃ M22e 3
  terminal-I = run-frames-sound Icosa.cert Icosa.state-9 terminalFrames-I (wf-reflect refl) terminal-ok-I

-- Output endpoint charts comparing the normalized Seifert model with the bundle.
import Cubical.Data.Int as Z
open import Cubical.HITs.Pushout.Base using (Pushout)
open import Cubical.HITs.Pushout.Properties using (pushoutEquiv)
open import DeloopS3.Seifert.TwistedBundle.Base using (λA)
import DeloopS3.Seifert.TwistedBundle.SmallChart as SmallChart
import DeloopS3.Seifert.TwistedBundle.Flattening as Flattening
open import DeloopS3.Seifert.TwistedBundle.Cell using (module Bundle)

-- Explicit codomains keep inference from expanding the descended universe.
open import DeloopS3.Seifert.TwistedBundle.Base using (Ksign)
import DeloopS3.Move.CancelMinimal as CircleModel

module SmallSpanMaps (e : Z.ℤ) where
  private
    module F = Flattening.Total e
    module S = SmallChart.Filling e
  abstract
    left-source left-target : F.O → Ksign
    left-source z = equivFun {A = F.L} {B = Ksign} S.leftTotal (F.left z)
    left-target z = λA (equivFun {A = F.O} {B = DeloopS3.Seifert.TwistedBundle.Base.A × CircleModel.C}
      S.overlapTotal z)
    right-source right-target : F.O → CircleModel.C
    right-source z = equivFun {A = F.R} {B = CircleModel.C} S.rightTotal (F.right z)
    right-target z = S.rowShift (equivFun {A = F.O}
      {B = DeloopS3.Seifert.TwistedBundle.Base.A × CircleModel.C} S.overlapTotal z)

    left-source-β : left-source ≡ (λ z → S.leftTotal .fst (F.left z))
    left-source-β = refl
    left-target-β : left-target ≡ (λ z → λA (S.overlapTotal .fst z))
    left-target-β = refl
    right-source-β : right-source ≡ (λ z → S.rightTotal .fst (F.right z))
    right-source-β = refl
    right-target-β : right-target ≡ (λ z → S.rowShift (S.overlapTotal .fst z))
    right-target-β = refl

record SmallSpanCompletion (e : Z.ℤ) : Type₁ where
  private
    module F = Flattening.Total e
    module S = SmallSpanMaps e
  field
    -- The Final.SmallSpan squares behind opaque coordinate maps;
    -- the β paths above identify their endpoints.
    left-square : Path (F.O → Ksign) S.left-source S.left-target
    right-square : Path (F.O → CircleModel.C) S.right-source S.right-target

record DescendedAdapter (e : ℕ) : Type₁ where
  field
    -- The normalized-to-small equivalence and the two flattening squares.
    -- Cert.Interpret.Done.descended constructs these data for both cases.
    seifert-to-small : M22e e ≃ Pushout λA (SmallChart.Filling.rowShift (Z.pos e))
    small-squares : SmallSpanCompletion (Z.pos e)

module Descended (e : ℕ) (adapter : DescendedAdapter e) where
  private
    module F = Flattening.Total (Z.pos e)
    module S = SmallChart.Filling (Z.pos e)
    open DescendedAdapter adapter
    open SmallSpanCompletion small-squares

  abstract
    standard-to-descended : M22e e ≃ Bundle.Mₑ (Z.pos e)
    standard-to-descended = compEquiv
      {A = M22e e} {B = Pushout λA S.rowShift} {C = Bundle.Mₑ (Z.pos e)}
      seifert-to-small
      (compEquiv {A = Pushout λA S.rowShift} {B = F.Filling}
        {C = Bundle.Mₑ (Z.pos e)}
        (invEquiv (pushoutEquiv F.left F.right λA S.rowShift
          S.overlapTotal S.leftTotal S.rightTotal
          (sym (SmallSpanMaps.left-source-β (Z.pos e)) ∙ left-square ∙ SmallSpanMaps.left-target-β (Z.pos e))
          (sym (SmallSpanMaps.right-source-β (Z.pos e)) ∙ right-square ∙ SmallSpanMaps.right-target-β (Z.pos e))))
        F.fillToTotal)
open Descended public

-- Input endpoint. Decoding is fixed, not a field asserting
-- an unspecified relation between a table and a group element.
open import Cubical.Foundations.HLevels
open import Cubical.Data.Nat using (zero; _<ᵇ_)
open import Cubical.Data.Bool using (false≢true)
open import Cubical.Data.SumFin using (Fin; fzero; fsuc; toℕ; isSetFin; SumFin≃Fin)
import Cubical.Data.Empty as Empty
open import Cubical.Algebra.Group.Base using (Group₀; GroupStr)
open import Cubical.HITs.EilenbergMacLane1.Base using (EM₁; embase; emloop)
open import DeloopS3.Cover.Cosets using (SubgroupEmbedding; subgroupEmbedding; CosetFamily; cosetPoint)
open import DeloopS3.Cover.CircleOrbit using (FinitePermutation; CyclicOrbitData)
import DeloopS3.Groups.TablePermutation as Tables
import DeloopS3.Groups.Concrete as Groups
import DeloopS3.Groups.Identification as Identification

Δ H : ShortCase → Group₀
Δ octa = Groups.S₄
Δ icosa = Groups.A₅
H octa = Groups.D₈
H icosa = Groups.D₆

j : (c : ShortCase) → SubgroupEmbedding (H c) (Δ c)
j octa = subgroupEmbedding Groups.D₈→S₄ Groups.D₈-tables.embed-injective
j icosa = subgroupEmbedding Identification.D₆→A₅ Identification.D₆-inclusion.injective

Sheet : Ch.Certificate → Type₀
Sheet ct = Fin (Ch.index ct)

data BaseLetter : Type₀ where
  a+ a- b+ b- : BaseLetter

wireLetter : BaseLetter → P.Letter
wireLetter a+ = P.fwd 1
wireLetter a- = P.bwd 1
wireLetter b+ = P.fwd 2
wireLetter b- = P.bwd 2

abstract
  rawChecks : (c : ShortCase) → RawChecks (certOf c)
  rawChecks octa = record
    { group-ok = Octa.group-ok ; subgroup-ok = Octa.subgroup-ok ; cosets-ok = Octa.cosets-ok
    ; action-a-ok = Octa.action-a-ok ; action-b-ok = Octa.action-b-ok
    ; action-a-inverse-ok = Octa.action-a-inverse-ok ; action-b-inverse-ok = Octa.action-b-inverse-ok
    ; graph-ok = Octa.graph-ok ; labels-ok = Octa.labels-ok
    ; boundary-partition-ok = Octa.boundary-partition-ok ; boundaries-ok = Octa.boundaries-ok }
  rawChecks icosa = record
    { group-ok = Icosa.group-ok ; subgroup-ok = Icosa.subgroup-ok ; cosets-ok = Icosa.cosets-ok
    ; action-a-ok = Icosa.action-a-ok ; action-b-ok = Icosa.action-b-ok
    ; action-a-inverse-ok = Icosa.action-a-inverse-ok ; action-b-inverse-ok = Icosa.action-b-inverse-ok
    ; graph-ok = Icosa.graph-ok ; labels-ok = Icosa.labels-ok
    ; boundary-partition-ok = Icosa.boundary-partition-ok ; boundaries-ok = Icosa.boundaries-ok }

  action-checked : (ct : Ch.Certificate) (checked : RawChecks ct) (t : BaseLetter)
    → Ch.checkAction ct (wireLetter t) ≡ true
  action-checked ct checked a+ = RawChecks.action-a-ok checked
  action-checked ct checked a- = RawChecks.action-a-inverse-ok checked
  action-checked ct checked b+ = RawChecks.action-b-ok checked
  action-checked ct checked b- = RawChecks.action-b-inverse-ok checked

actEquiv : (ct : Ch.Certificate) → RawChecks ct → BaseLetter → Sheet ct ≃ Sheet ct
actEquiv ct checked t = Tables.tablePermutation
  {n = Ch.index ct} {t = Ch.actTable (Ch.action ct) (wireLetter t)}
  (and-left (action-checked ct checked t))

actFin : (ct : Ch.Certificate) → RawChecks ct → BaseLetter → Sheet ct → Sheet ct
actFin ct checked t = equivFun (actEquiv ct checked t)

-- Actions on sheets follow the wire tables; GROUP elements instead use
-- certificatePermutation, whose inverse corrects symmetric-group composition.
abstract
  generator-a generator-b : (c : ShortCase) → Δ c .fst
  generator-a octa = Tables.certificatePermutation {t = Ch.a Octa.cert} (P.valid Octa.a-permutation)
  generator-a icosa = Groups.A₅-tables.locate (Ch.a Icosa.cert) refl
  generator-b octa = Tables.certificatePermutation {t = Ch.b Octa.cert} (P.valid Octa.b-permutation)
  generator-b icosa = Groups.A₅-tables.locate (Ch.b Icosa.cert) refl

  -- Small decoding interfaces keep group closure opaque.
  generator-a-octa : generator-a octa ≡ Tables.certificatePermutation
    {t = Ch.a Octa.cert} (P.valid Octa.a-permutation)
  generator-a-octa = refl
  generator-b-octa : generator-b octa ≡ Tables.certificatePermutation
    {t = Ch.b Octa.cert} (P.valid Octa.b-permutation)
  generator-b-octa = refl
  generator-a-icosa : Groups.A₅-tables.table (generator-a icosa) ≡ Ch.a Icosa.cert
  generator-a-icosa = Groups.A₅-tables.locate-hit (Ch.a Icosa.cert) refl
  generator-b-icosa : Groups.A₅-tables.table (generator-b icosa) ≡ Ch.b Icosa.cert
  generator-b-icosa = Groups.A₅-tables.locate-hit (Ch.b Icosa.cert) refl

letterElement : (c : ShortCase) → BaseLetter → Δ c .fst
letterElement c a+ = generator-a c
letterElement c a- = GroupStr.inv (Δ c .snd) (generator-a c)
letterElement c b+ = generator-b c
letterElement c b- = GroupStr.inv (Δ c .snd) (generator-b c)

-- The only supported generator IDs of representatives are 1 and 2;
-- checkCosets checks wordValid 2. The total fallback is the identity.
baseElement : (c : ShortCase) → ℕ → Δ c .fst
baseElement c 1 = generator-a c
baseElement c 2 = generator-b c
baseElement c _ = GroupStr.1g (Δ c .snd)

wordElement : (c : ShortCase) → P.Word → Δ c .fst
wordElement c [] = GroupStr.1g (Δ c .snd)
wordElement c (P.fwd n ∷ w) = GroupStr._·_ (Δ c .snd) (baseElement c n) (wordElement c w)
wordElement c (P.bwd n ∷ w) = GroupStr._·_ (Δ c .snd)
  (GroupStr.inv (Δ c .snd) (baseElement c n)) (wordElement c w)

repElement : (c : ShortCase) → Sheet (certOf c) → Δ c .fst
repElement c i = wordElement c (P.nth [] (Ch.reps (certOf c)) (toℕ i))

localAction : (ct : Ch.Certificate) → RawChecks ct → Ch.Kind → Sheet ct ≃ Sheet ct
localAction ct checked Ch.A = actEquiv ct checked a+
localAction ct checked Ch.B = actEquiv ct checked b+
localAction ct checked Ch.C = compEquiv (actEquiv ct checked b-) (actEquiv ct checked a-)

localPermutation : (ct : Ch.Certificate) → RawChecks ct → Ch.Kind → FinitePermutation (Sheet ct)
localPermutation ct checked k = record
  { size = Ch.index ct ; enumerate = SumFin≃Fin (Ch.index ct)
  ; setX = isSetFin ; permutation = localAction ct checked k }

boundariesOf : Ch.Certificate → Ch.Kind → List Ch.Boundary
boundariesOf ct k = P.filter (λ b → Ch.kindEq (Ch.kind b) k) (Ch.boundaries ct)

Bd : Ch.Certificate → Ch.Kind → Type₀
Bd ct k = Fin (P.length (boundariesOf ct k))

private
  boundedFin : (n x : ℕ) → (x <ᵇ n) ≡ true → Fin n
  boundedFin zero x p = Empty.rec (false≢true p)
  boundedFin (suc n) zero p = fzero
  boundedFin (suc n) (suc x) p = fsuc (boundedFin n x p)

  firstInRange : (n : ℕ) (xs : List ℕ)
    → (0 <ᵇ P.length xs) ≡ true
    → P.all (λ x → x <ᵇ n) xs ≡ true → Fin n
  firstInRange n [] positive range = Empty.rec (false≢true positive)
  firstInRange n (x ∷ xs) positive range = boundedFin n x (and-left range)

  abstract
    boundary-checked : (ct : Ch.Certificate) (checked : RawChecks ct)
      (k : Ch.Kind) (i : Bd ct k) → Ch.checkBoundary ct (at (boundariesOf ct k) i) ≡ true
    boundary-checked ct checked k i = all-sound (Ch.checkBoundary ct)
      (RawChecks.boundaries-ok checked)
      (filter-member (λ b → Ch.kindEq (Ch.kind b) k) (Ch.boundaries ct)
        (at-member (boundariesOf ct k) i))

firstSheet : (ct : Ch.Certificate) (bd : Ch.Boundary)
  → Ch.checkBoundary ct bd ≡ true → Sheet ct
firstSheet ct bd ok = firstInRange (Ch.index ct) (Ch.orbit bd)
  (and-left ok) (and-left (and-right {a = 0 <ᵇ P.length (Ch.orbit bd)} ok))

record ShortInput (c : ShortCase) : Type₁ where
  private
    ct : Ch.Certificate
    ct = certOf c
  field
    checked : RawChecks ct
    sheets : Sheet ct ≃ CosetFamily (j c) embase .fst
    sheets-at-rep : (i : Sheet ct) → equivFun sheets i ≡ cosetPoint (j c) (repElement c i)
    action-square : (i : Sheet ct) (t : BaseLetter)
      → subst (λ b → CosetFamily (j c) b .fst) (emloop (letterElement c t)) (equivFun sheets i)
        ≡ equivFun sheets (actFin ct checked t i)
    orbits : (k : Ch.Kind) → CyclicOrbitData (localPermutation ct checked k)
    orbit-index : (k : Ch.Kind) → CyclicOrbitData.Rep (orbits k) ≃ Bd ct k

  boundaryAt : (k : Ch.Kind) → CyclicOrbitData.Rep (orbits k) → Ch.Boundary
  boundaryAt k r = at (boundariesOf ct k) (equivFun (orbit-index k) r)

  firstSheetAt : (k : Ch.Kind) → CyclicOrbitData.Rep (orbits k) → Sheet ct
  firstSheetAt k r = firstSheet ct (boundaryAt k r)
    (boundary-checked ct checked k (equivFun (orbit-index k) r))

  field
    orbit-start : (k : Ch.Kind) (r : CyclicOrbitData.Rep (orbits k))
      → CyclicOrbitData.repr (orbits k) r ≡ firstSheetAt k r
    orbit-length : (k : Ch.Kind) (r : CyclicOrbitData.Rep (orbits k))
      → CyclicOrbitData.length (orbits k) r ≡ Ch.orbitLength (boundaryAt k r)
    orbit-order : (k : Ch.Kind) (r : CyclicOrbitData.Rep (orbits k))
      → suc (CyclicOrbitData.order-1 (orbits k) r) ≡ Ch.order (boundaryAt k r)

open import Cubical.HITs.Pushout.Base using (inl; inr; push)
open import Cubical.Functions.Fibration using (fiberEquiv)
open import DeloopS3.Cover.MarkedDescent.Family using (module FamilyFlattening)
open import DeloopS3.Move.CancelMinimalCore using (EquivOver)
import DeloopS3.Sphere.TruncationCartesian as Cartesian

originalExponent : ShortCase → ℕ
originalExponent octa = 4
originalExponent icosa = 5

originalState : ShortCase → Ch.State
originalState c = Ch.state twoGenerators
  (Ch.face 0 2 (P.pos 1) (P.fwd 1 ∷ []) (P.pos 0) ∷
   Ch.face 1 3 (P.pos 1) (P.fwd 2 ∷ []) (P.pos 0) ∷
   Ch.face 2 (originalExponent c) (P.pos 1 P.-z P.pos (originalExponent c))
     (P.bwd 2 ∷ P.bwd 1 ∷ []) (P.pos 0) ∷ [])

M_G : ShortCase → Type₀
M_G c = T (originalState c)

-- Shared endpoint charts, specialized by Cert.Input.Model at its
-- Kind-indexed family-flattening span.
record InitialSpanCharts (S : Ch.State) (D : Span ℓ-zero ℓ-zero ℓ-zero) : Type₁ where
  field
    leftChart : L S ≃ Span.L D
    overlapChart : O S ≃ Span.O D
    rightChart : R S ≃ Span.R D
    leftSquare : (z : O S)
      → equivFun leftChart (left S z) ≡ Span.left D (equivFun overlapChart z)
    rightSquare : (z : O S)
      → equivFun rightChart (right S z) ≡ Span.right D (equivFun overlapChart z)

-- The classifier maps to the fixed concrete group's classifying space.
-- Pulling back its coset family defines Q and its total space A_G.
module CoverFamily (c : ShortCase) (ρ-M : M_G c → EM₁ (Δ c)) where
  Q : M_G c → Type₀
  Q m = CosetFamily (j c) (ρ-M m) .fst

  A_G : Type₀
  A_G = Σ (M_G c) Q

  module Flat = FamilyFlattening (left (originalState c)) (right (originalState c)) Q

  FlatSpan : Span ℓ-zero ℓ-zero ℓ-zero
  FlatSpan = record
    { O = Σ (O (originalState c)) (λ a → Q (inl (left (originalState c) a)))
    ; L = Σ (L (originalState c)) (Q ∘ inl)
    ; R = Σ (R (originalState c)) (Q ∘ inr)
    ; left = Flat.Flat.Σf ; right = Flat.Flat.Σg }

  InitialCharts : Type₁
  InitialCharts = InitialSpanCharts (Ch.initialState (certOf c)) FlatSpan
  module InitialCharts = InitialSpanCharts

  -- The vertex/overlap charts and their squares induce cover-initial
  -- together with its projection homotopy.
  module Initial (input : ShortInput c) (charts : InitialCharts) where
    open InitialCharts charts

    chartSpan : SpanEquiv (diagram (Ch.initialState (certOf c))) FlatSpan
    chartSpan = record
      { overlapEquiv = overlapChart ; leftVertex = leftChart ; rightVertex = rightChart
      ; leftSquare = leftSquare ; rightSquare = rightSquare }

    abstract
      chart-total : T (Ch.initialState (certOf c)) ≃ Total FlatSpan
      chart-total = spanEquiv chartSpan

      cover-initial : T (Ch.initialState (certOf c)) ≃ A_G
      cover-initial = compEquiv
        {A = T (Ch.initialState (certOf c))} {B = Total FlatSpan} {C = A_G}
        chart-total Flat.flatten

    initialProjection : T (Ch.initialState (certOf c)) → M_G c
    initialProjection = Flat.projection ∘ equivFun chart-total

    abstract
      cover-initial-over : EquivOver initialProjection (fst {B = Q})
      cover-initial-over = cover-initial , λ x → Flat.over .snd (equivFun chart-total x)

  abstract
    projection-fibres : (m : M_G c) → fiber (fst {B = Q}) m ≃ Q m
    projection-fibres = fiberEquiv Q

    Q-set : (m : M_G c) → isSet (Q m)
    Q-set m = CosetFamily (j c) (ρ-M m) .snd

open CoverFamily public using (Q; A_G; FlatSpan; InitialCharts)

-- Assemble the covering and its cartesian truncation square from endpoint data.
-- Cert.Interpret.Done instantiates this assembly for both concrete groups.
module Assembly
  (ρ-M : (c : ShortCase) → M_G c → EM₁ (Δ c))
  (short-input : (c : ShortCase) → ShortInput c)
  (initial-charts : (c : ShortCase) → InitialCharts c (ρ-M c))
  (descended : (c : ShortCase) → DescendedAdapter (exponentOf c)) where

  module Case (c : ShortCase) where
    private
      module F = CoverFamily c (ρ-M c)
      module I = F.Initial (short-input c) (initial-charts c)
      E : ℕ
      E = exponentOf c

    abstract
      short-total : Bundle.Mₑ (Z.pos E) ≃ F.A_G
      short-total = compEquiv
        {A = Bundle.Mₑ (Z.pos E)} {B = M22e E} {C = F.A_G}
        (invEquiv (standard-to-descended E (descended c)))
        (compEquiv {A = M22e E} {B = T (Ch.initialState (certOf c))} {C = F.A_G}
          (invEquiv (normalize-short c)) I.cover-initial)

    p : Bundle.Mₑ (Z.pos E) → M_G c
    p = fst ∘ equivFun short-total

    abstract
      p-fibres : (m : M_G c) → fiber p m ≃ F.Q m
      p-fibres m = compEquiv
        {A = fiber p m} {B = fiber (fst {B = F.Q}) m} {C = F.Q m}
        (Σ-cong-equiv-fst {B = λ t → fst t ≡ m} short-total)
        (F.projection-fibres m)

      p-is-cover : (m : M_G c) → isSet (fiber p m)
      p-is-cover m = isOfHLevelRespectEquiv 2 (invEquiv (p-fibres m)) (F.Q-set m)

      B-cartesian : Cartesian.CartSquare p (Cartesian.τ₁-map p)
        Cartesian.η₁ Cartesian.η₁ (Cartesian.trunc₁-naturality p)
      B-cartesian = Cartesian.trunc₁-cover-cartesian p p-is-cover

      B-unit-fibers : (z : Cartesian.τ₁ (Bundle.Mₑ (Z.pos E)))
        → fiber Cartesian.η₁ z ≃ fiber Cartesian.η₁ (Cartesian.τ₁-map p z)
      B-unit-fibers = Cartesian.trunc₁-cover-unit-fibers p p-is-cover

  open Case public
