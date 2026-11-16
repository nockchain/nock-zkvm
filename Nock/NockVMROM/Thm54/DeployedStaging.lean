/-
  Nock/NockVMROM/Thm54/DeployedStaging.lean

  Compute: `ProductionNamedComputeRAP` = `computeChipAt`'s RAP, `w = 303`,
  `s = 418` (`correctedFinalComputeAllGates`).  Memory: `namedFinalMemoryRAP` =
  `memoryChipAt`'s RAP, `w = 205`, `s = 156` (`memorySourceTemplate … allGates`; the 23 inert
  residual columns carry no gate).

  **Why not the type `StagedChip`.**  `StagedChip.air : Reified.AIR` (`StagedTableRAP.lean`)
  whose constants are `Expr.Const : ℤ → Expr` (`AIR.lean`); the deployed gates are
  `CoeffExpr F`, whose `.const : F → …` that constructor "cannot provide"
  (`CoordinateCompiler.lean`, `CoeffExpr` docstring).  This file instead
  carries the same data — the deployed `RAP`, a `RoundSchedule` of its own width, and a
  `ChallengeChronology` — as `StagedRAPView`, with no dummy and no chip edit.

  **B1 — the measured column → round map** (paper order, three blocks; earliest round in which
  the column's honest content is defined).  Round `0`: before `z`; round `1`: after `z, a, b, c`
  (fingerprints); round `2`: after `αM, αC, γ, IO, pole, λ` (timestamps, accumulators, `λ`).

  | chip | columns | content | round |
  |---|---|---|---|
  | compute | `0..12` | selectors, structural summaries, first/last masks (cols 11, 12) | 0 |
  | compute | `202..264` | Form R `c_1..c_63` | 0 |
  | compute | `265..270` | Form R `m_0..m_5` | 0 |
  | compute | `271`, `272` | base power helpers `h`, `t` | 0 |
  | compute | `273`, `274` | `p`, `top` | 0 |
  | compute | `275..295` | eq-chain helpers `E_1..E_21` (base; read `top`, `c`, no coin) | 0 |
  | compute | `296..298`, `299..301` | `𝕂` helpers `H`, `T` (read `λ`) | 2 |
  | compute | roles `0..35` (cols `13..120`) | label fingerprints (`z`) | 1 |
  | compute | roles `6,7,9,10,18,19,27,28` | walk-overlay hosts (`walkCount`, `walkAcc`; `overlayRoleA`) | 2 |
  | compute | role `32`; roles `33..35` | `ioAcc` host; Form R denominators at `λ` | 2 |
  | compute | roles `36..53` | decomposition fingerprints (`z`) | 1 |
  | compute | roles `54`, `55` | `ln_prev`, `ln` (`α` powers) | 2 |
  | compute | roles `56`, `57` | `cons_inv`, `inv_gen` (inverses of fingerprint quantities) | 1 |
  | compute | roles `58..62` | residual witnesses, walk line, queue witness | 2 |
  | memory | `0..5` | state selectors, first/last masks | 0 |
  | memory | `153`, `154` | preprocessing `rootMask`, `dequeueMask` (role 49 coords 0, 1) | 0 |
  | memory | `182..204` | inert residual (no gate) | 0 |
  | memory | roles `0..2`, `5..7`, `10..12` | `pt`/`lc`/`rc` NPR (`size` = cols `6..8` holds `z`) | 1 |
  | memory | roles `3,4,8,9,13,14` | Form R `pw`, `counts` (`λ`) | 2 |
  | memory | roles `15..18` | child state selectors | 0 |
  | memory | roles `19..24`; `25`; `26` | record NPR (`z`); record `T = λ^m`; `ts = α^e` | 1; 2; 2 |
  | memory | roles `27..29`; `30` | intermediate pre/cur/inverse; seed inverse `z⁻¹` | 2; 1 |
  | memory | roles `31..33`; `34..36` | walk `ln`, `count`, `acc`; dead (`cur/cc/cm`) | 2; 0 |
  | memory | roles `37,38,40..44,50` | sampled-IO denominator, inverse, terminal, accumulators | 2 |
  | memory | roles `39`, `45..49`, `51..54`, `56` | `ver`, hosted tags, mask/selector mirrors | 0 |
  | memory | roles `55`; `57` | queue inverse; `C' = Cpoly(λ)` | 2; 2 |

  **Coins.**  The eleven coordinates of the landed tuple (`FormRAxisEvent.landedVec`):
  `z, a, b, c` sampled after round 0; `αC, γ, αM, IO γ, IO pole, interPole, λ` after round 1
  (`deployedChronology`, which is `min 1 ∘ FormRAxisEvent.landedRound`).

  `gateReadsLaterColumn colRound chalRound cols chals` is true when the gate reads a column
  committed AFTER its latest coin (no challenge: `0`).  Under commit-then-sample that is the
  LEGITIMATE case: a round-`r` column may depend on any coin sampled before round `r`
  (`usableByColumnOf` is `<`).  The soundness
  criterion is on EVENTS, not gates: an event's bad set over the coin vector must read only
  coordinates sampled strictly before the coin its Schwartz–Zippel count is taken over,
  `ReadsOn (priorCoords …)` — which `FormRAxisEvent.formRBadAt_readsOn` (A4) states for the Form R
  event.  B2 maps which columns are bound to which coins; its passing gates (coin round ≥ column
  round) are the identities over pre-committed columns whose EVENTS need read-set receipts.
  Every deployed gate is enumerated at the level of the deployed lists it comes from (typed
  sources for the compiled compute blocks, mixed sources for memory, raw `CoeffExpr` for the base,
  equality and certificate blocks); each typed / mixed source stands for its three coordinate
  gates.
-/
import Nock.NockVMROM.Thm54.FormRAxisEvent
import Nock.NockVMROM.Thm54.CommitmentModel
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
import Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.NockVMROM.Thm54.PaperResourceCounts
import Nock.RedTeam.SecondWave.Rev2
import Nock.NockVMROM.Thm54.P8Core.DeployedStaging

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxRecDepth 200000

open scoped BigOperators Classical

namespace Nock.NockVMROM.Thm54.DeployedStaging

open Nock
open Nock.Framework
open Nock.Reified
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.Staging
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MixedCoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeRangeCertificate
open Module

/-! ## B1. Column → round maps at the deployed widths -/

/-- Compute `𝕂`-role → round (roles `0..62`, physical columns `13 + 3r + k`). -/
def computeRoleRound (r : ℕ) : ℕ :=
  if r ∈ [6, 7, 9, 10, 18, 19, 27, 28, 32, 33, 34, 35] then 2
  else if r < 54 then 1
  else if r = 54 ∨ r = 55 then 2
  else if r = 56 ∨ r = 57 then 1
  else 2

/-- Compute physical column → round. -/
def computeColRound (c : ℕ) : ℕ :=
  if c < 13 then 0
  else if c < 202 then computeRoleRound ((c - 13) / 3)
  else if c < 296 then 0
  else if c < 302 then 2
  else 0

/-- Compute `𝕂` challenge slot (`computeKOfTuple`) → the round after which it is sampled. -/
def computeSlotRound (q : ℕ) : ℕ :=
  if q = 0 ∨ q = 6 ∨ q = 7 ∨ q = 8 ∨ q = 9 ∨ q = 10 then 1 else 0

/-- Memory `𝕂` challenge slot (`memoryKOfTuple`) → the round after which it is sampled. -/
def memorySlotRound (q : ℕ) : ℕ :=
  if 2 ≤ q ∧ q ≤ 8 then 1 else 0

/-- Compute raw `𝔽` challenge slot (`computeChalValOfTuple`: `3q + k`, `q < 12`). -/
def computeRawChalRound (j : ℕ) : ℕ := if j < 36 then computeSlotRound (j / 3) else 0

/-- Memory raw `𝔽` challenge slot (`memoryChalValOfTuple`: `6 + 3q + k`, `q < 9`). -/
def memoryRawChalRound (j : ℕ) : ℕ :=
  if 6 ≤ j ∧ j < 33 then memorySlotRound ((j - 6) / 3) else 0

theorem deployedChronology_eq_landedRound (i : Fin 11) :
    ((deployedChronology.sampledAfter i : Fin 3) : ℕ) = min (FormRAxisEvent.landedRound i) 1 := by
  fin_cases i <;> rfl

/-- `λ` is sampled after round 1, with `αM`; `z` after round 0. -/
theorem deployedChronology_lambda :
    deployedChronology.sampledAfter FormRAxisEvent.lamIdx =
        deployedChronology.sampledAfter FormRAxisEvent.alphaMIdx ∧
      ((deployedChronology.sampledAfter FormRAxisEvent.lamIdx : Fin 3) : ℕ) = 1 ∧
      ((deployedChronology.sampledAfter FormRAxisEvent.seedIdx : Fin 3) : ℕ) = 0 :=
  ⟨rfl, rfl, rfl⟩

def computeRoundFin (c : Fin 303) : Fin 3 :=
  ⟨computeColRound c, by unfold computeColRound computeRoleRound; split_ifs <;> omega⟩

/-- Measured block widths (B4 tile). -/
def computeBlockWidth : Fin 3 → ℕ := ![108, 132, 63]

set_option maxRecDepth 20000 in
theorem computeBlockWidth_eq (r : Fin 3) :
    computeBlockWidth r = (Finset.univ.filter fun c : Fin 303 => computeRoundFin c = r).card := by
  fin_cases r <;> decide

def deployedComputeSchedule : RoundSchedule 303 3 where
  roundOf := computeRoundFin
  width := computeBlockWidth
  width_eq := computeBlockWidth_eq

section Views

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

theorem computeChip_w {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) :
    (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.w = 303 := rfl

theorem computeChip_s {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) :
    (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap.s = 418 :=
  correctedFinalComputeAllGates_length n b

/-- **B1.**  The staged view of the deployed compute chip, `w = 303`, `s = 418`. -/
noncomputable def deployedComputeView {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictExtension.StrictOrbitDomain F 3 h) :
    StagedRAPView F 3 deployedChronology where
  rap := (ProductionNamedComputeRAP hn nodes b chalVal pubVal orbit).rap
  width := 303
  hw := computeChip_w hn nodes b chalVal pubVal orbit
  schedule := deployedComputeSchedule
  columnChallenges := fun c => roundChallenges (computeRoundFin c)
  columns_commit_before_sampling := fun c => roundChallenges_usable (computeRoundFin c)

theorem memoryChip_s {h n : ℕ} (hn : 0 < n) (nodes : Fin n → F) (b : Basis (Fin 3) F K)
    (chalVal pubVal : ℕ → F) (orbit : StrictExtension.StrictOrbitDomain F 3 h) (kMem : ℕ) :
    (OptimizedMemoryRAP.namedFinalMemoryRAP hn nodes b chalVal pubVal orbit kMem).rap.s = 156 :=
  (OptimizedMemoryRAP.finalMemoryRAP_fingerprint hn nodes b chalVal pubVal orbit kMem).2.1

end Views

/-! ## B2. The gate criterion and its extractors -/

/-- Latest round of a list under a round map (`0` on the empty list). -/
def maxRound (rnd : ℕ → ℕ) (l : List ℕ) : ℕ := l.foldr (fun x m => max (rnd x) m) 0

/-- **B2 criterion.**  A gate fails when it reads a column committed in a later round than the
round after which its latest challenge is sampled (`column.round > challenge.sampledAfter`). -/
def gateReadsLaterColumn (colRound chalRound : ℕ → ℕ) (cols chals : List ℕ) : Bool :=
  decide (maxRound chalRound chals < maxRound colRound cols)

/-- B2 failure class: `0` passes; `1` coin-free gate over a later column; `2` the latest coin is a
round-0 coin (`z`, `a`, `b`, `c`, `z⁻¹`) and a column is later; `3` the latest coin is a round-1
coin (`α`, `αC`, `γ`, IO, pole, `λ`) and a column is later (round 2). -/
def failClass (colRound chalRound : ℕ → ℕ) (cols chals : List ℕ) : ℕ :=
  if gateReadsLaterColumn colRound chalRound cols chals then
    (if chals = [] then 1 else if maxRound chalRound chals = 0 then 2 else 3)
  else 0

/-- Trace columns (current and next row) of a `CoeffExpr`. -/
def coeffTraceCols {F : Type*} : CoeffExpr F → List ℕ
  | .const _ => []
  | .var .traceCur i => [i]
  | .var .traceNext i => [i]
  | .var .challenge _ => []
  | .var .publicVal _ => []
  | .add a b => coeffTraceCols a ++ coeffTraceCols b
  | .sub a b => coeffTraceCols a ++ coeffTraceCols b
  | .mul a b => coeffTraceCols a ++ coeffTraceCols b
  | .neg a => coeffTraceCols a
  | .pow a _ => coeffTraceCols a

/-- Raw challenge slots of a `CoeffExpr`. -/
def coeffChals {F : Type*} : CoeffExpr F → List ℕ
  | .const _ => []
  | .var .challenge i => [i]
  | .var _ _ => []
  | .add a b => coeffChals a ++ coeffChals b
  | .sub a b => coeffChals a ++ coeffChals b
  | .mul a b => coeffChals a ++ coeffChals b
  | .neg a => coeffChals a
  | .pow a _ => coeffChals a

/-- Physical columns of a compute typed source (all three coordinates of an `𝕂` role). -/
def typedCols : CorrectedFinalTypedExpr → List ℕ
  | .baseCur i => [i.val]
  | .baseNext i => [i.val]
  | .extCur i => [13 + 3 * i.val, 14 + 3 * i.val, 15 + 3 * i.val]
  | .extNext i => [13 + 3 * i.val, 14 + 3 * i.val, 15 + 3 * i.val]
  | .certBase i => [202 + i.val]
  | .certExt i => [296 + 3 * i.val, 297 + 3 * i.val, 298 + 3 * i.val]
  | .expCur => [302]
  | .add x y => typedCols x ++ typedCols y
  | .sub x y => typedCols x ++ typedCols y
  | .mul x y => typedCols x ++ typedCols y
  | .neg x => typedCols x
  | .pow x _ => typedCols x
  | _ => []

/-- `𝕂` challenge slots of a compute typed source; `lamPow` reads the `λ` slot `9`. -/
def typedSlots : CorrectedFinalTypedExpr → List ℕ
  | .challenge i => [i.val]
  | .lamPow _ => [9]
  | .add x y => typedSlots x ++ typedSlots y
  | .sub x y => typedSlots x ++ typedSlots y
  | .mul x y => typedSlots x ++ typedSlots y
  | .neg x => typedSlots x
  | .pow x _ => typedSlots x
  | _ => []

/-- Physical columns of a memory mixed source. -/
def mixedCols {F : Type*} : MixedExpr F → List ℕ
  | .Var .traceCur i => [6 + 3 * i, 7 + 3 * i, 8 + 3 * i]
  | .Var .traceNext i => [6 + 3 * i, 7 + 3 * i, 8 + 3 * i]
  | .Var _ _ => []
  | .Lift c => coeffTraceCols c
  | .Scale c m => coeffTraceCols c ++ mixedCols m
  | .Const _ => []
  | .Add a b => mixedCols a ++ mixedCols b
  | .Sub a b => mixedCols a ++ mixedCols b
  | .Mul a b => mixedCols a ++ mixedCols b
  | .Neg a => mixedCols a
  | .Pow a _ => mixedCols a

/-- `𝕂` challenge slots of a memory mixed source (base-field challenges inside `Lift`/`Scale`
are raw slots; none occurs in the deployed list, `memoryMixed_noRawChallenge`). -/
def mixedSlots {F : Type*} : MixedExpr F → List ℕ
  | .Var .challenge i => [i]
  | .Var _ _ => []
  | .Lift _ => []
  | .Scale _ m => mixedSlots m
  | .Const _ => []
  | .Add a b => mixedSlots a ++ mixedSlots b
  | .Sub a b => mixedSlots a ++ mixedSlots b
  | .Mul a b => mixedSlots a ++ mixedSlots b
  | .Neg a => mixedSlots a
  | .Pow a _ => mixedSlots a

def mixedRawChals {F : Type*} : MixedExpr F → List ℕ
  | .Lift c => coeffChals c
  | .Scale c m => coeffChals c ++ mixedRawChals m
  | .Add a b => mixedRawChals a ++ mixedRawChals b
  | .Sub a b => mixedRawChals a ++ mixedRawChals b
  | .Mul a b => mixedRawChals a ++ mixedRawChals b
  | .Neg a => mixedRawChals a
  | .Pow a _ => mixedRawChals a
  | _ => []

/-- B2 verdict of a raw compute gate. -/
def computeCoeffFails {F : Type*} (g : CoeffExpr F) : Bool :=
  gateReadsLaterColumn computeColRound computeRawChalRound (coeffTraceCols g) (coeffChals g)

/-- B2 verdict of a compute typed source (all three of its coordinate gates). -/
def computeTypedFails (t : CorrectedFinalTypedExpr) : Bool :=
  gateReadsLaterColumn computeColRound computeSlotRound (typedCols t) (typedSlots t)

/-- B2 verdict of a raw memory gate. -/
def memoryCoeffFails {F : Type*} (g : CoeffExpr F) : Bool :=
  gateReadsLaterColumn memoryColRound memoryRawChalRound (coeffTraceCols g) (coeffChals g)

/-- B2 verdict of a memory mixed source (all three of its coordinate gates). -/
def memoryMixedFails {F : Type*} (g : MixedExpr F) : Bool :=
  gateReadsLaterColumn memoryColRound memorySlotRound (mixedCols g) (mixedSlots g)

def computeCoeffClass {F : Type*} (g : CoeffExpr F) : ℕ :=
  failClass computeColRound computeRawChalRound (coeffTraceCols g) (coeffChals g)
/-- `typedCols` over-reads `.pow x 0` (the compile's `powVec _ _ 0 = oneVec` reads nothing). -/
def typedColsC : CorrectedFinalTypedExpr → List ℕ
  | .baseCur i => [i.val]
  | .baseNext i => [i.val]
  | .extCur i => [13 + 3 * i.val, 14 + 3 * i.val, 15 + 3 * i.val]
  | .extNext i => [13 + 3 * i.val, 14 + 3 * i.val, 15 + 3 * i.val]
  | .certBase i => [202 + i.val]
  | .certExt i => [296 + 3 * i.val, 297 + 3 * i.val, 298 + 3 * i.val]
  | .expCur => [302]
  | .add x y => typedColsC x ++ typedColsC y
  | .sub x y => typedColsC x ++ typedColsC y
  | .mul x y => typedColsC x ++ typedColsC y
  | .neg x => typedColsC x
  | .pow x n => if n = 0 then [] else typedColsC x
  | _ => []

/-- Slots without the `lamPow` leaf: `lamPow d` reads `λ` only when `d < pwScaleExp K`, so this
is the `K`-uniform lower bound; `typedSlots` is the upper bound. -/
def typedSlotsC : CorrectedFinalTypedExpr → List ℕ
  | .challenge i => [i.val]
  | .add x y => typedSlotsC x ++ typedSlotsC y
  | .sub x y => typedSlotsC x ++ typedSlotsC y
  | .mul x y => typedSlotsC x ++ typedSlotsC y
  | .neg x => typedSlotsC x
  | .pow x n => if n = 0 then [] else typedSlotsC x
  | _ => []

/-- B2 class of a compute typed source with the compile's read set. -/
def computeTypedClassC (t : CorrectedFinalTypedExpr) : ℕ :=
  failClass computeColRound computeSlotRound (typedColsC t) (typedSlotsC t)

/-- On every deployed source it agrees
with `computeTypedClassC` (`computeTypedClass_eq_C`). -/
def computeTypedClass (t : CorrectedFinalTypedExpr) : ℕ :=
  failClass computeColRound computeSlotRound (typedCols t) (typedSlots t)
def memoryCoeffClass {F : Type*} (g : CoeffExpr F) : ℕ :=
  failClass memoryColRound memoryRawChalRound (coeffTraceCols g) (coeffChals g)
def memoryMixedClass {F : Type*} (g : MixedExpr F) : ℕ :=
  failClass memoryColRound memorySlotRound (mixedCols g) (mixedSlots g)

/-! ## The deployed source lists -/

/-- `notLast · x` at the typed level (`notLastCoeff = 1 − isLast`, `isLast` = base col 12). -/
def notLastTyped (x : CorrectedFinalTypedExpr) : CorrectedFinalTypedExpr :=
  .mul (.sub (.const 1) (.baseCur 12)) x

/-- The typed source of core gate `i`, mirroring `correctedCoreCoord`'s dispatch
(residual witnesses at roles `58`, `59` = `residualWitnessRole 0/1`). -/
def correctedCoreSource (i : CorrectedCoreExtGateId) : CorrectedFinalTypedExpr :=
  if i = packedWalkCountId then notLastTyped (.extCur 58)
  else if i = packedWalkAccId then notLastTyped (.extCur 59)
  else if i = packedChainId then accAfterChain
  else if i = packedLnChainId ∨ i = packedWalkLnId then notLastTyped (correctedFinalExtGate i)
  else correctedFinalExtGate i

/-- The typed source of aux gate `j`, mirroring `correctedAuxCoord`. -/
def correctedAuxSource (j : CorrectedResidualWitnessId) : CorrectedFinalTypedExpr :=
  if j = 2 then correctedAccAfterStep
  else .sub (.extCur ⟨58 + j.val, by omega⟩) (correctedFinalResidualSource j)

theorem residualWitnessRole_val (j : CorrectedResidualWitnessId) (hj : j ≠ 2) :
    (OptimizedComputeCorrectedFinal.residualWitnessRole j : ℕ) = 58 + j.val := by
  fin_cases j <;> simp_all <;> rfl

set_option maxHeartbeats 2000000

/-! ## B2 enumeration — compute

Deployed order (`correctedFinalComputeAllGates`): base `15` | core `82 × 3` | aux `3 × 3` |
endpoint-2 `6 × 3` | endpoint-4 `1 × 3` | equality `22` | Form R certificate `97` |
`λ` pins `2 × 3` = `416`.  Each typed source's class is the class of its three coordinate gates. -/

/-- Core: the class of each of the 82 typed sources. -/

theorem compute_core_classes :
    (List.finRange 82).map (fun i => computeTypedClass (correctedCoreSource i)) =
      [1, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 2,
        2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 3, 1,
        2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 3, 3, 3, 1] := by
  decide

theorem compute_aux_classes :
    (List.finRange 3).map (fun j => computeTypedClass (correctedAuxSource j)) = [3, 3, 1] := by
  decide

theorem compute_endpoint2_classes :
    correctedEndpoint2.map computeTypedClass = [3, 3, 1, 1, 1, 1] := by
  decide

theorem compute_endpoint4_classes :
    correctedEndpoint4.map computeTypedClass = [3] := by
  decide

theorem compute_lamPins_classes :
    formRLamPins.map computeTypedClass = [3, 3] := by
  decide

section Generic

variable {F : Type*} [Field F]

theorem compute_base_classes (n : ℕ) :
    (finalBaseTransitionGates (F := F) n).map computeCoeffClass = List.replicate 15 0 := by
  by_cases hn : n = 1
  · simp only [finalBaseTransitionGates, endpointOverlapConsistency, hn, if_true]; rfl
  · simp only [finalBaseTransitionGates, endpointOverlapConsistency, hn, if_false]; rfl

theorem compute_equality_classes :
    (finalEndpointEqualityChecks (F := F)).map computeCoeffClass = List.replicate 22 0 := rfl

/-- Reads of the axis equation (`ftLeaf` = col `136`, `fthLeaf` = col `145`, `t` = col `272`,
`csum` = cols `202..264`, selectors `0`, `9`). -/
def axisEquationReads : List ℕ × List ℕ :=
  ([0, 136, 272] ++ (List.range 63).foldl (fun acc j => acc ++ [202 + j]) [] ++
      [9, 145, 272] ++ (List.range 63).foldl (fun acc j => acc ++ [202 + j]) [], [])

theorem csumAcc_cols (n : ℕ) :
    coeffTraceCols (csumAcc (F := F) n) = (List.range n).foldl (fun acc j => acc ++ [202 + j]) [] ∧
      coeffChals (csumAcc (F := F) n) = [] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
      refine ⟨?_, ?_⟩
      · simp only [csumAcc, coeffTraceCols, ih.1, colC, bcur, col0, List.range_succ,
          List.foldl_append, List.foldl_cons, List.foldl_nil, List.append_nil]
      · simp only [csumAcc, coeffChals, ih.2, colC, bcur, List.append_nil]

theorem axisEquation_reads :
    (coeffTraceCols (axisEquation (F := F)), coeffChals (axisEquation (F := F))) =
      axisEquationReads := by
  simp only [axisEquation, ftLeaf, fthLeaf, colTbase, csum, bcur, col0, coeffTraceCols,
    coeffChals, (csumAcc_cols 63).1, (csumAcc_cols 63).2, axisEquationReads]
  rfl

/-- The axis equation reads the leaf-fingerprint columns `136`, `145` (compute roles `41`, `44`,
round `1`) with no coin: class `1`. -/
theorem axisEquation_class : computeCoeffClass (axisEquation (F := F)) = 1 := by
  have h1 := congrArg Prod.fst (axisEquation_reads (F := F))
  have h2 := congrArg Prod.snd (axisEquation_reads (F := F))
  simp only at h1 h2
  rw [computeCoeffClass, h1, h2]
  decide

/-- A gate reading only Form R base columns `202..295` and no challenge. -/
def CertLocal (g : CoeffExpr F) : Prop :=
  coeffChals g = [] ∧ ∀ c ∈ coeffTraceCols g, 202 ≤ c ∧ c < 296

theorem maxRound_eq_zero (rnd : ℕ → ℕ) (l : List ℕ) (h : ∀ x ∈ l, rnd x = 0) :
    maxRound rnd l = 0 := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
      simp only [maxRound, List.foldr_cons] at ih ⊢
      rw [h x (by simp), ih (fun y hy => h y (by simp [hy]))]
      rfl

theorem class_of_certLocal (g : CoeffExpr F) (h : CertLocal g) : computeCoeffClass g = 0 := by
  have hc : maxRound computeColRound (coeffTraceCols g) = 0 :=
    maxRound_eq_zero _ _ fun c hc => by
      obtain ⟨h1, h2⟩ := h.2 c hc
      unfold computeColRound
      rw [if_neg (by omega), if_neg (by omega), if_pos h2]
  simp [computeCoeffClass, failClass, gateReadsLaterColumn, hc]

theorem certLocal_const (x : F) : CertLocal (.const x) := ⟨rfl, by simp [coeffTraceCols]⟩

theorem certLocal_bcur (i : ℕ) (h1 : 202 ≤ i) (h2 : i < 296) : CertLocal (bcur (F := F) i) :=
  ⟨rfl, by simp [bcur, coeffTraceCols]; omega⟩

theorem certLocal_add {a b : CoeffExpr F} (ha : CertLocal a) (hb : CertLocal b) :
    CertLocal (.add a b) :=
  ⟨by simp [coeffChals, ha.1, hb.1], by
    intro c hc; simp only [coeffTraceCols, List.mem_append] at hc
    exact hc.elim (ha.2 c) (hb.2 c)⟩

theorem certLocal_sub {a b : CoeffExpr F} (ha : CertLocal a) (hb : CertLocal b) :
    CertLocal (.sub a b) :=
  ⟨by simp [coeffChals, ha.1, hb.1], by
    intro c hc; simp only [coeffTraceCols, List.mem_append] at hc
    exact hc.elim (ha.2 c) (hb.2 c)⟩

theorem certLocal_mul {a b : CoeffExpr F} (ha : CertLocal a) (hb : CertLocal b) :
    CertLocal (.mul a b) :=
  ⟨by simp [coeffChals, ha.1, hb.1], by
    intro c hc; simp only [coeffTraceCols, List.mem_append] at hc
    exact hc.elim (ha.2 c) (hb.2 c)⟩

theorem certLocal_colC (j : ℕ) (hj : j < 63) : CertLocal (colC (F := F) j) :=
  certLocal_bcur _ (by simp only [col0]; omega) (by simp only [col0]; omega)
theorem certLocal_colM (k : ℕ) (hk : k < 6) : CertLocal (colM (F := F) k) :=
  certLocal_bcur _ (by simp only [col0]; omega) (by simp only [col0]; omega)
theorem certLocal_colE (k : ℕ) (hk : k < 21) : CertLocal (colE (F := F) k) :=
  certLocal_bcur _ (by simp only [col0]; omega) (by simp only [col0]; omega)
theorem certLocal_colTop : CertLocal (colTop (F := F)) := certLocal_bcur _ (by decide) (by decide)
theorem certLocal_colP : CertLocal (colP (F := F)) := certLocal_bcur _ (by decide) (by decide)
theorem certLocal_colHbase : CertLocal (colHbase (F := F)) :=
  certLocal_bcur _ (by decide) (by decide)
theorem certLocal_colTbase : CertLocal (colTbase (F := F)) :=
  certLocal_bcur _ (by decide) (by decide)

theorem certLocal_bbool {e : CoeffExpr F} (h : CertLocal e) : CertLocal (bbool e) :=
  certLocal_mul h (certLocal_sub h (certLocal_const _))

theorem certLocal_lm (k : ℕ) (hk : k < 6) : CertLocal (lm (F := F) k) := by
  unfold lm; split
  · exact certLocal_colM k hk
  · exact certLocal_sub (certLocal_const _) (certLocal_colM k hk)

theorem certLocal_linCol (j : ℕ) (hj : j < 63) : CertLocal (linCol (F := F) j) := by
  unfold linCol; split
  · exact certLocal_colC j hj
  · exact certLocal_sub (certLocal_const _) (certLocal_colC j hj)

theorem certLocal_bitCoeff (b : Bool) : CertLocal (bitCoeff (F := F) b) := by
  unfold bitCoeff; split <;> exact certLocal_const _

theorem certLocal_helperAt (k : ℕ) (hk : k ≤ 21) : CertLocal (helperAt (F := F) k) := by
  unfold helperAt; split
  · exact certLocal_colTop
  · exact certLocal_colE _ (by omega)

theorem certLocal_foldMul (ls : List (CoeffExpr F)) (E : CoeffExpr F)
    (hE : CertLocal E) (hl : ∀ l ∈ ls, CertLocal l) : CertLocal (foldMul ls E) := by
  induction ls generalizing E with
  | nil => simpa [foldMul] using hE
  | cons l ls ih =>
      simp only [foldMul]
      exact ih _ (certLocal_mul hE (hl l (by simp))) (fun x hx => hl x (by simp [hx]))

theorem certLocal_sumExpr (ls : List (CoeffExpr F)) (hl : ∀ l ∈ ls, CertLocal l) :
    CertLocal (sumExpr ls) := by
  induction ls with
  | nil => exact certLocal_const _
  | cons l ls ih =>
      exact certLocal_add (hl l (by simp)) (ih fun x hx => hl x (by simp [hx]))

theorem certLocal_termAt (k : ℕ) (hk : k < 63) : CertLocal (termAt (F := F) k) := by
  unfold termAt
  refine certLocal_mul (certLocal_foldMul _ _ (certLocal_helperAt _ (by omega)) ?_)
    (certLocal_sub (certLocal_const _) (certLocal_colC k hk))
  intro l hl
  simp only [List.mem_map, List.mem_range] at hl
  obtain ⟨j, hj, rfl⟩ := hl
  have : k % 3 ≤ k := Nat.mod_le k 3
  exact certLocal_linCol _ (by omega)

theorem certLocal_eqmAt (k : ℕ) : CertLocal (eqmAt (F := F) k) := by
  unfold eqmAt
  split
  · exact certLocal_mul (certLocal_mul certLocal_colP (certLocal_lm 2 (by decide)))
      (certLocal_lm 1 (by decide))
  · exact certLocal_mul certLocal_colP (certLocal_lm 2 (by decide))
  · exact certLocal_colP
  · exact certLocal_mul (certLocal_lm 5 (by decide)) (certLocal_lm 4 (by decide))
  · exact certLocal_lm 5 (by decide)
  · exact certLocal_const _
  · exact certLocal_const _

theorem certLocal_rangeTerm (k : ℕ) (hk : k < 6) : CertLocal (rangeTerm (F := F) k) := by
  unfold rangeTerm
  refine certLocal_mul (certLocal_mul (certLocal_eqmAt _)
    (certLocal_sub (certLocal_const _) (certLocal_colM k hk))) ?_
  split <;> exact certLocal_const _

theorem certLocal_factor2 (k : ℕ) (hk : k < 6) : CertLocal (factor2 (F := F) k) :=
  certLocal_add (certLocal_const _)
    (certLocal_mul (certLocal_colM k hk) (certLocal_sub (certLocal_const _) (certLocal_const _)))

theorem certLocal_helperPinAt (k : ℕ) (hk : k < 21) : CertLocal (helperPinAt (F := F) k) := by
  unfold helperPinAt
  exact certLocal_sub (certLocal_colE k hk)
    (certLocal_mul (certLocal_mul (certLocal_mul (certLocal_helperAt k (by omega))
      (certLocal_linCol _ (by omega))) (certLocal_linCol _ (by omega)))
      (certLocal_linCol _ (by omega)))

theorem certLocal_first96 :
    ∀ g ∈ (booleanGates (F := F) ++ powerPins ++ formRPins ++ helperPins ++
      [comparisonGate, rangeGate]), CertLocal g := by
  intro g hg
  simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ((((hb | hp) | hr) | hh) | hc | hc)
  · simp only [booleanGates, List.mem_append, List.mem_map, List.mem_range] at hb
    rcases hb with ⟨j, hj, rfl⟩ | ⟨k, hk, rfl⟩
    · split_ifs
      · exact certLocal_colC j hj
      · exact certLocal_bbool (certLocal_colC j hj)
    · exact certLocal_bbool (certLocal_colM k hk)
  · simp only [powerPins, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl
    · exact certLocal_sub certLocal_colHbase (certLocal_mul (certLocal_mul
        (certLocal_factor2 0 (by decide)) (certLocal_factor2 1 (by decide)))
        (certLocal_factor2 2 (by decide)))
    · exact certLocal_sub certLocal_colTbase (certLocal_mul (certLocal_mul (certLocal_mul
        certLocal_colHbase (certLocal_factor2 3 (by decide))) (certLocal_factor2 4 (by decide)))
        (certLocal_factor2 5 (by decide)))
  · simp only [formRPins, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact certLocal_sub certLocal_colP (certLocal_mul (certLocal_mul
        (certLocal_lm 5 (by decide)) (certLocal_lm 4 (by decide))) (certLocal_lm 3 (by decide)))
    · exact certLocal_sub certLocal_colTop (certLocal_mul (certLocal_mul (certLocal_mul
        certLocal_colP (certLocal_lm 2 (by decide))) (certLocal_lm 1 (by decide)))
        (certLocal_lm 0 (by decide)))
  · simp only [helperPins, List.mem_map, List.mem_range] at hh
    obtain ⟨k, hk, rfl⟩ := hh
    exact certLocal_helperPinAt k hk
  · subst hc
    refine certLocal_sub (certLocal_sumExpr _ ?_) certLocal_colTop
    intro t ht
    simp only [comparisonTerms, List.mem_map, List.mem_range] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact certLocal_mul (certLocal_bitCoeff _) (certLocal_termAt k hk)
  · subst hc
    refine certLocal_sub (certLocal_add (certLocal_sumExpr _ ?_) certLocal_colTop)
      (certLocal_const _)
    intro t ht
    simp only [rangeTerms, List.mem_map, List.mem_range] at ht
    obtain ⟨k, hk, rfl⟩ := ht
    exact certLocal_rangeTerm k hk

/-- Form R certificate block (97 raw gates): 96 pass; the axis equation is class `1`. -/
theorem compute_cert_classes :
    (formRCertificateGates (F := F)).map computeCoeffClass = List.replicate 96 0 ++ [1] := by
  have hsplit : formRCertificateGates (F := F) =
      (booleanGates (F := F) ++ powerPins ++ formRPins ++ helperPins ++
        [comparisonGate, rangeGate]) ++ [axisEquation] := by
    simp [formRCertificateGates, formRNamed]
  have hlen : (booleanGates (F := F) ++ powerPins ++ formRPins ++ helperPins ++
      [comparisonGate, rangeGate]).length = 96 := by
    simp [booleanGates_length, helperPins_length, formRPins]
  have h1 : (booleanGates (F := F) ++ powerPins ++ formRPins ++ helperPins ++
      [comparisonGate, rangeGate]).map computeCoeffClass = List.replicate 96 0 := by
    rw [List.eq_replicate_iff]
    refine ⟨by rw [List.length_map, hlen], ?_⟩
    intro x hx
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hx
    exact class_of_certLocal g (certLocal_first96 g hg)
  have h2 : [axisEquation (F := F)].map computeCoeffClass = [1] := by
    rw [List.map_singleton, axisEquation_class]
  rw [hsplit, List.map_append, h1, h2]

end Generic

theorem computeTypedClass_eq_C :
    (List.finRange 82).map (fun i => computeTypedClassC (correctedCoreSource i)) =
        (List.finRange 82).map (fun i => computeTypedClass (correctedCoreSource i)) ∧
      (List.finRange 3).map (fun j => computeTypedClassC (correctedAuxSource j)) =
        (List.finRange 3).map (fun j => computeTypedClass (correctedAuxSource j)) ∧
      correctedEndpoint2.map computeTypedClassC = correctedEndpoint2.map computeTypedClass ∧
      correctedEndpoint4.map computeTypedClassC = correctedEndpoint4.map computeTypedClass ∧
      formRLamPins.map computeTypedClassC = formRLamPins.map computeTypedClass := by
  decide

/-! ## B2 enumeration — memory

Deployed order (`memorySourceTemplate … allGates`): base `6` | mixed `50 × 3`; no endpoint or
equality gate (`degreeOneEndpoints = degreeThreeEndpoints = equalityChecks = []`).  Mixed index
map: `0..15` `tab:v_mem` classes `q ∈ [0,2,3,4,5,6,7,10,11,12,15,16,17,18,19,20]`, `16`
`paperConsDyck`, `17` timestamp (`q = 22`), `18` `paperAggregator`, `19..21` `q = 21, 25, 26`,
`22..25` bottom pins, `26` intermediate chain, `27..33` walk (`ln1`, `count1`, `accInit`,
`lnStep`, `countStep`, `accStep`, `terminal`), `34..42` IO core (`verBool`, `safeNorm`,
`safeInv`, `contribution`, `accStep`, `accInit`, `accTerminal`, `terminalRole`,
`denominatorPin`), `43..46` endpoints (`intermediateInit`, `intermediateTerminal`,
`rootMaskCounts`, `rootMaskPw`), `47..48` queue witness, `49` `haltAtomMixed`. -/

section Memory

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-- The read lists `(mixedCols g, mixedSlots g)` of the 50 deployed mixed sources (measured). -/
def memoryMixedReads : List (List ℕ × List ℕ) :=
  [([0, 6, 7, 8, 21, 22, 23, 36, 37, 38, 1, 6, 7, 8, 2, 6, 7, 8, 21, 22, 23, 3, 6, 7, 8, 21, 22,
  23], [0]), ([0, 12, 13, 14, 27, 28, 29, 21, 22, 23, 42, 43, 44, 1, 2, 12, 13, 14, 27, 28, 29, 3,
  12, 13, 14, 27, 28, 29], []), ([0, 15, 16, 17, 30, 31, 32, 45, 46, 47, 1, 15, 16, 17, 2, 15, 16,
  17, 30, 31, 32, 81, 82, 83, 84, 85, 86, 3, 15, 16, 17, 30, 31, 32, 84, 85, 86], [8, 8, 8]), ([0,
  18, 19, 20, 33, 34, 35, 48, 49, 50, 30, 31, 32, 45, 46, 47, 45, 46, 47, 1, 18, 19, 20, 2, 18,
  19, 20, 33, 34, 35, 81, 82, 83, 177, 178, 179, 84, 85, 86, 3, 18, 19, 20, 33, 34, 35, 84, 85,
  86], [8, 8]), ([0, 1, 21, 22, 23, 2, 3], []), ([0, 1, 24, 25, 26, 2, 3], []), ([0, 1, 27, 28,
  29, 2, 3], []), ([0, 1, 36, 37, 38, 2, 36, 37, 38, 3, 36, 37, 38], []), ([0, 1, 39, 40, 41, 2,
  39, 40, 41, 3, 39, 40, 41], []), ([0, 1, 42, 43, 44, 2, 42, 43, 44, 3, 42, 43, 44], []), ([0,
  63, 64, 65, 1, 63, 64, 65, 2, 63, 64, 65, 6, 7, 8, 3], []), ([0, 66, 67, 68, 1, 66, 67, 68, 2,
  66, 67, 68, 9, 10, 11, 3], []), ([0, 69, 70, 71, 1, 69, 70, 71, 2, 69, 70, 71, 12, 13, 14, 3],
  []), ([0, 72, 73, 74, 1, 72, 73, 74, 2, 3, 72, 73, 74, 6, 7, 8], []), ([0, 75, 76, 77, 1, 75,
  76, 77, 2, 3, 75, 76, 77, 9, 10, 11], []), ([0, 78, 79, 80, 1, 78, 79, 80, 2, 3, 78, 79, 80, 12,
  13, 14], []), ([0, 9, 10, 11, 24, 25, 26, 21, 22, 23, 21, 22, 23, 21, 22, 23, 21, 22, 23, 39,
  40, 41, 1, 9, 10, 11, 2, 9, 10, 11, 24, 25, 26, 3, 9, 10, 11, 24, 25, 26], [0, 0, 0]), ([0, 84,
  85, 86, 1, 84, 85, 86, 2, 3], []), ([63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77,
  78, 79, 80, 81, 82, 83, 84, 85, 86, 177, 178, 179, 181, 90, 91, 92, 87, 88, 89, 2, 3], [6, 4, 4,
  4, 4, 4, 4, 4, 4, 4]), ([0, 81, 82, 83, 1, 81, 82, 83, 2, 3], []), ([0, 1, 2, 57, 58, 59, 3], []),
  ([0, 1, 2, 3, 60, 61, 62], []), ([0, 1, 30, 31, 32, 2, 3], []), ([0, 1, 33, 34, 35, 2, 3], []),
  ([0, 1, 45, 46, 47, 2, 45, 46, 47, 3, 45, 46, 47], []), ([0, 1, 48, 49, 50, 2, 48, 49, 50, 3,
  48, 49, 50], []), ([5, 90, 91, 92, 87, 88, 89], []), ([4, 99, 100, 101], [3]), ([4, 102, 103,
  104, 0, 1, 2, 3], [3, 3, 3, 3]), ([4, 105, 106, 107, 0, 141, 142, 143, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 33, 34, 35, 30, 31, 32, 144, 145, 146, 36, 37, 38, 39, 40, 41, 42, 43, 44, 48, 49,
  50, 45, 46, 47, 1, 2, 141, 142, 143, 21, 22, 23, 24, 25, 26, 27, 28, 29, 33, 34, 35, 30, 31, 32,
  3, 141, 142, 143, 21, 22, 23, 24, 25, 26, 27, 28, 29, 33, 34, 35, 30, 31, 32], [3, 7, 7, 7, 7,
  7, 7, 3, 7, 7, 7, 7, 7, 7, 3, 7, 7, 7, 7, 7, 7, 3, 7, 7, 7, 7, 7, 7]), ([5, 99, 100, 101, 99,
  100, 101], [3]), ([5, 102, 103, 104, 102, 103, 104, 0, 1, 2, 3], [3, 3, 3, 3]), ([154, 99, 100,
  101, 0, 6, 7, 8, 9, 10, 11, 12, 13, 14, 18, 19, 20, 15, 16, 17, 1, 6, 7, 8, 9, 10, 11, 12, 13,
  14, 18, 19, 20, 15, 16, 17, 2, 6, 7, 8, 9, 10, 11, 12, 13, 14, 18, 19, 20, 15, 16, 17, 3, 6, 7,
  8, 9, 10, 11, 12, 13, 14, 18, 19, 20, 15, 16, 17, 5, 105, 106, 107, 105, 106, 107, 102, 103,
  104, 0, 141, 142, 143, 21, 22, 23, 24, 25, 26, 27, 28, 29, 33, 34, 35, 30, 31, 32, 144, 145,
  146, 36, 37, 38, 39, 40, 41, 42, 43, 44, 48, 49, 50, 45, 46, 47, 1, 2, 141, 142, 143, 21, 22,
  23, 24, 25, 26, 27, 28, 29, 33, 34, 35, 30, 31, 32, 3, 141, 142, 143, 21, 22, 23, 24, 25, 26,
  27, 28, 29, 33, 34, 35, 30, 31, 32], [7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7, 7,
  7, 7, 7, 7, 7, 3, 7, 7, 7, 7, 7, 7, 3, 7, 7, 7, 7, 7, 7, 3, 7, 7, 7, 7, 7, 7, 3, 7, 7, 7, 7, 7,
  7]), ([5, 105, 106, 107], []), ([123, 124, 125, 123, 124, 125], []), ([156, 157, 158, 123, 124,
  125, 117, 118, 119, 123, 124, 125], []), ([156, 157, 158, 120, 121, 122], []), ([132, 133, 134,
  123, 124, 125, 120, 121, 122], []), ([5, 135, 136, 137, 135, 136, 137, 132, 133, 134], []), ([4,
  135, 136, 137], []), ([5, 135, 136, 137, 132, 133, 134], []), ([126, 127, 128], []), ([117, 118,
  119, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85,
  86, 177, 178, 179, 181], [5, 4, 4, 4, 4, 4, 4, 4, 4, 4]), ([4, 87, 88, 89], []), ([5, 90, 91, 92], []),
  ([153, 18, 19, 20], []), ([153, 15, 16, 17], []), ([5, 171, 172, 173, 102, 103, 104, 99, 100,
  101], []), ([5, 102, 103, 104, 99, 100, 101], []), ([1, 12, 13, 14, 180], [])]

theorem memory_mixed_reads (b : Basis (Fin 3) F K) :
    (OptimizedMemoryGateBasis.mixedTransitionGates b).map (fun g => (mixedCols g, mixedSlots g)) =
      memoryMixedReads := rfl

theorem memoryMixedReads_classes :
    memoryMixedReads.map (fun p => failClass memoryColRound memorySlotRound p.1 p.2) =
      [2, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 0, 0, 1, 1, 1, 1, 1, 3, 3, 3,
        3, 3, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1] := by
  decide

theorem memory_mixed_classes (b : Basis (Fin 3) F K) :
    (OptimizedMemoryGateBasis.mixedTransitionGates b).map memoryMixedClass =
      [2, 1, 3, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 2, 1, 3, 1, 0, 0, 1, 1, 1, 1, 1, 3, 3, 3,
        3, 3, 3, 1, 0, 1, 1, 1, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1] := by
  rw [← memoryMixedReads_classes, ← memory_mixed_reads b, List.map_map]
  rfl

/-- No deployed mixed gate hides a raw base-field challenge inside a `Lift` / `Scale`. -/

theorem memoryMixed_noRawChallenge (b : Basis (Fin 3) F K) :
    (OptimizedMemoryGateBasis.mixedTransitionGates b).map mixedRawChals =
      List.replicate 50 [] := rfl

theorem memory_base_classes (b : Basis (Fin 3) F K) :
    (OptimizedMemoryGateBasis.baseTransitionGates b).map memoryCoeffClass =
      List.replicate 6 0 := rfl

theorem memory_no_endpoint_or_equality (b : Basis (Fin 3) F K) :
    (OptimizedMemoryGateBasis.memorySourceTemplate b).extDeg1 = [] ∧
      (OptimizedMemoryGateBasis.memorySourceTemplate b).extDeg3 = [] ∧
      (OptimizedMemoryGateBasis.memorySourceTemplate b).equalityChecks = [] := ⟨rfl, rfl, rfl⟩

end Memory

/-! At 302/204:
compute cols `196..201` are roles `61`, `62` (walk line, queue witness); memory cols `194..199`
are inert residual columns no gate reads. -/

/-- Reads one of the compute columns `196..201`. -/
def readsWalkTail (cols : List ℕ) : Bool := cols.any fun c => 196 ≤ c && c < 202

/-- Core sources reading cols `196..201`, with their slots' rounds: core `73` (`walkLn`, `αC`),
`76`, `77` (coin-free). -/

theorem tenSeven_core_tail :
    ((List.finRange 82).filter (fun i => readsWalkTail (typedCols (correctedCoreSource i)))).map
        (fun i => (i.val, computeTypedClass (correctedCoreSource i))) =
      [(73, 3), (76, 1), (77, 1)] := by
  decide

theorem tenSeven_aux_endpoint_tail :
    ((List.finRange 3).filter (fun j => readsWalkTail (typedCols (correctedAuxSource j)))).map
        (fun j => (j.val, computeTypedClass (correctedAuxSource j))) = [(1, 3)] ∧
      (correctedEndpoint2 ++ correctedEndpoint4).map
          (fun t => (readsWalkTail (typedCols t), computeTypedClass t)) =
        [(true, 3), (false, 3), (false, 1), (false, 1), (false, 1), (false, 1), (true, 3)] := by
  decide

/-- C-seed is gone: no deployed compute source reads cols `196..201` with a round-0 coin only
(class `2`). -/

theorem tenSeven_cSeed_gone :
    ((List.finRange 82).filter (fun i => readsWalkTail (typedCols (correctedCoreSource i)) &&
        computeTypedClass (correctedCoreSource i) == 2)) = [] := by
  decide


theorem tenSeven_mLate_gone {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] (b : Basis (Fin 3) F K) :
    ((OptimizedMemoryGateBasis.mixedTransitionGates b).map
        (fun g => (mixedCols g).any fun c => 182 ≤ c)) = List.replicate 50 false ∧
    ((OptimizedMemoryGateBasis.mixedTransitionGates b).map
        (fun g => (mixedCols g).any fun c => 194 ≤ c)) = List.replicate 50 false := ⟨rfl, rfl⟩

/-! ## B4. Tile, chronology, and the `atom` round -/

/-- The tile equality at the deployed widths. -/
theorem deployed_blocks_tile_the_chips :
    (108 + 132 + 63 : ℕ) = 303 ∧ (85 + 48 + 72 : ℕ) = 205 := ⟨rfl, rfl⟩

theorem deployedCompute_total_width : (303 : ℕ) = ∑ r, deployedComputeSchedule.width r :=
  deployedComputeSchedule.total_width

theorem deployedMemory_total_width : (205 : ℕ) = ∑ r, deployedMemorySchedule.width r :=
  deployedMemorySchedule.total_width

theorem live_widths :
    Thm54Resources.computeColumns 3 = 303 ∧ Thm54Resources.memoryColumns 3 = 205 :=
  ⟨Thm54Resources.computeColumns_deployed, Thm54Resources.memoryColumns_deployed⟩

/-- **The chronology theorem.**  Both deployed chips are staged over `deployedChronology` (by
typing); `λ` is sampled with `αM` after round 1 and `z` after round 0; the pre-seed `atom`
(col 180) and the Form R base certificate are round 0, before `z`; the `z`-bearing memory size
columns `6..8` and the leaf columns `12..14` are round 1; `λ`'s compute helpers `H`, `T` and the
memory `pw` / `counts` are round 2. -/
theorem deployed_chronology_sentence :
    memoryColRound OptimizedMemoryGateBasis.atomCol = 0 ∧
      (memoryColRound 6 = 1 ∧ memoryColRound 7 = 1 ∧ memoryColRound 8 = 1) ∧
      (memoryColRound 12 = 1 ∧ memoryColRound 13 = 1 ∧ memoryColRound 14 = 1) ∧
      (∀ c : Fin 94, computeColRound (202 + c) = 0) ∧
      (∀ c : Fin 6, computeColRound (296 + c) = 2) ∧
      (memoryColRound 15 = 2 ∧ memoryColRound 18 = 2) ∧
      ((deployedChronology.sampledAfter FormRAxisEvent.seedIdx : Fin 3) : ℕ) = 0 ∧
      deployedChronology.sampledAfter FormRAxisEvent.lamIdx =
        deployedChronology.sampledAfter FormRAxisEvent.alphaMIdx := by
  refine ⟨rfl, ⟨rfl, rfl, rfl⟩, ⟨rfl, rfl, rfl⟩, ?_, ?_, ⟨rfl, rfl⟩, rfl, rfl⟩ <;> decide

/-- The memory `reqIdx` (physical
column `181`) and the compute `S` (physical column `302`) are committed in round `0`, before the
NPR seed `z` and before `α`, `λ` (`deployedChronology`): the record pairing they carry is fixed
before the coins the timestamps and the Form R λ-event are taken over. -/
theorem carrier_columns_round_zero :
    memoryColRound OptimizedMemoryGateBasis.reqIdxCol = 0 ∧
      computeColRound OptimizedComputeCorrectedFinal.computeExpCol = 0 ∧
      memoryRoundFin ⟨OptimizedMemoryGateBasis.reqIdxCol, by decide⟩ = 0 ∧
      computeRoundFin ⟨OptimizedComputeCorrectedFinal.computeExpCol, by decide⟩ = 0 ∧
      ((deployedChronology.sampledAfter FormRAxisEvent.seedIdx : Fin 3) : ℕ) = 0 := by
  refine ⟨by decide, by decide, ?_, ?_, rfl⟩ <;> decide

/-- `RAP.Satisfies` is blind to `k` / `wRAP` (`Rev2.satisfies_is_k_and_wRAP_blind`): the map
above is a staging of the deployed RAP, not something the RAP's acceptance enforces. -/
theorem rap_satisfies_ignores_rounds {F : Type*} [Field F] [DecidableEq F] (R : RAP F)
    (k' : ℕ) (w' : Fin k' → ℕ) (hw : R.w = ∑ i, w' i) (P : Fin R.w → Polynomial F) :
    R.Satisfies P ↔ ({R with k := k', wRAP := w', w_eq := hw} : RAP F).Satisfies P :=
  Rev2.satisfies_is_k_and_wRAP_blind R k' w' hw P

end Nock.NockVMROM.Thm54.DeployedStaging

#print axioms Nock.NockVMROM.Thm54.DeployedStaging.compute_core_classes
#print axioms Nock.NockVMROM.Thm54.DeployedStaging.compute_cert_classes
#print axioms Nock.NockVMROM.Thm54.DeployedStaging.memory_mixed_classes
#print axioms Nock.NockVMROM.Thm54.DeployedStaging.deployed_chronology_sentence
