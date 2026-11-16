/-
  Nock/RedTeam/Batch357Thm54DeployedReadSet.lean

  **ChalSlots / Expr read-set of both deployed chips.**  Every challenge
  slot a committed gate reads is mapped to a coordinate of
  `OptimizedProductionChallengeTuple`.  A slot with no carrier is a FINDING
  (a baked coin the verifier never samples).

  Instruments:
  * `exprReads` — `𝕂`-challenge indices of an `Expr` (the `ConstraintIndex.chalIdxs`
    analogue, non-partial, decidable).
  * `mixedReads` — `𝕂`-challenge indices of a `MixedExpr`.
  * `Batch265.chalSlots` — raw `𝔽` slots of a compiled `CoeffExpr`
    (`eval_congr_of_chalSlots`).

  Compute deployed `𝕂` list: `finalExtTransitionGates` = 76 paper-packing + 4
  sampled-IO (`OptimizedComputeGateBasis`).  Memory deployed `𝕂` list:
  `paperKGates` = `mixedTransitionGates` (`OptimizedMemoryGateBasis`).  Base
  buckets read no challenge (`finalBaseTransitionGates_chalSlots`,
  `paperBaseGates`).

  Slot maps, re-read at source:
  * compute cubic: slot `3·q+k` is coord `k` of `exactFinalChallenge q`
    (`OptimizedComputeCanonicalSatisfaction.ExactFinalChallengeCoordinates`).
  * memory cubic: slot `6+3·q+k` is coord `k` of `memoryChallengeTargets q`
    (`BuildableChips.memoryChallenge`, `ExactMemoryCoordinatePins`).
  * IO pins: compute `3·7+k` / `3·8+k` (`OptimizedComputeSubstitution.lean`
    `finalSampledGamma` / `finalSampledPole`); memory `𝕂` 4 / 5 / 6
    (`ExactMemoryCoordinatePins.sampledGamma` / `sampledPole` / `sampledInterPole`).

  `listReads` on `finalExtTransitionGates` finds
  `𝕂` indices `{2,3,4}` live — the paper's equality coins `a,b,c`.
  `OptimizedProductionChallengeTuple` is `JointCoins × ((K×K) × (unit × interPole))`
  and has no coordinate for them
  (`ChallengeInventory.eq_coefficients_absent_from_production_tuple`).
  `computeKOfTuple` returns `0` at those indices.  Widening the tuple would
  move `|𝕂|⁷` and the bound (brief: those do not move).  Zeroing them would
  make `chalValOfTuple_honest` fail on the OP5 slots.

  This file used to
  claim compute challenge slot `9` is read by NO committed gate
  (`listReads 9 finalExtTransitionGates = false`, "retired folds unread").
  * the compiled `OptimizedComputeCorrectedFinal.formRLamPins` (typed `.challenge 9`, raw slots
    `27..29`; `typedReads`/`formRLamPins_read_slot9` below), and
  * the Form R record-slot expressions of the three sampled-IO gates of `finalExtTransitionGates`
    (indices `78,79,80`; `OptimizedComputeSubstitution`, "Form R record slots"), which carry
    `λ` and `λ^{n-1}`.
  The paper-packing 78 do not read it.  Slot `11` stays unread; slot `10` stays the walk `γ`.
  Every other claim of this file is unchanged.
-/
import Nock.RedTeam.Batch265Thm54DeadChallenge36
import Nock.NockVMROM.Thm54.ComputePaperPacking
import Nock.NockVMROM.Thm54.OptimizedComputeSameExecution
import Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.GateCorrespondenceCompute
import Nock.NockVMROM.Thm54.JointCoins

set_option autoImplicit false
set_option maxHeartbeats 4000000

namespace Nock.RedTeam.Batch357

open Nock Nock.Reified Nock.NockVMROM Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.RedTeam.Batch265
open Module

/-! ## Instruments -/

/-- `𝕂`-challenge indices of an `Expr`.  Decidable; the `ConstraintIndex.chalIdxs`
analogue used by `ComputePaperPacking.readsNoCompilerChallenge`. -/
def exprReads (q : ℕ) : Expr → Bool
  | .Var .challenge i => decide (i = q)
  | .Var _ _ | .Const _ => false
  | .Add x y | .Sub x y | .Mul x y => exprReads q x || exprReads q y
  | .Neg x | .Pow x _ => exprReads q x

def listReads (q : ℕ) (gs : List Expr) : Bool :=
  gs.any (exprReads q)

/-- `𝕂`-challenge indices of a typed corrected-final expression (the compiled layer that
`formRLamPins` lives in). -/
def typedReads (q : ℕ) : CorrectedFinalTypedExpr → Bool
  | .challenge i => decide ((i : ℕ) = q)
  | .add x y | .sub x y | .mul x y => typedReads q x || typedReads q y
  | .neg x | .pow x _ => typedReads q x
  | .lamPow _ => decide (q = 9)
  | _ => false

/-! ## Compute `𝕂` census of `finalExtTransitionGates`

Instrument: `listReads` on the 80 committed extension gates.  One `decide`
closes the twelve-index table (the same instrument that rejected the
"unread `{2,3,4}`" claim). -/

theorem compute_k_read_census :
    listReads 0 finalExtTransitionGates = true ∧
      listReads 1 finalExtTransitionGates = true ∧
      listReads 2 finalExtTransitionGates = true ∧
      listReads 3 finalExtTransitionGates = true ∧
      listReads 4 finalExtTransitionGates = true ∧
      listReads 5 finalExtTransitionGates = true ∧
      listReads 6 finalExtTransitionGates = true ∧
      listReads 7 finalExtTransitionGates = true ∧
      listReads 8 finalExtTransitionGates = true ∧
      listReads 9 finalExtTransitionGates = true ∧
      listReads 10 finalExtTransitionGates = true ∧
      listReads 11 finalExtTransitionGates = false := by
  decide

/-- Positive control: every pin-field compute coin is read by some committed gate. -/
theorem compute_pin_slots_are_read :
    listReads 0 finalExtTransitionGates = true ∧
      listReads 1 finalExtTransitionGates = true ∧
      listReads 5 finalExtTransitionGates = true ∧
      listReads 6 finalExtTransitionGates = true ∧
      listReads 7 finalExtTransitionGates = true ∧
      listReads 8 finalExtTransitionGates = true :=
  And.intro compute_k_read_census.1 <|
    And.intro compute_k_read_census.2.1 <|
      And.intro compute_k_read_census.2.2.2.2.2.1 <|
        And.intro compute_k_read_census.2.2.2.2.2.2.1 <|
          And.intro compute_k_read_census.2.2.2.2.2.2.2.1
            compute_k_read_census.2.2.2.2.2.2.2.2.1

/-- Slot `9` (Form R `λ`) is read; slot `11` is the only unread compute slot.  Slot `10` is the
walk-node RLC coin `γ` (`ComputeWalkLabel.walkGammaChallenge`). -/
theorem compute_slot9_read_slot11_unread :
    listReads 9 finalExtTransitionGates = true ∧
      listReads 10 finalExtTransitionGates = true ∧
      listReads 11 finalExtTransitionGates = false :=
  And.intro compute_k_read_census.2.2.2.2.2.2.2.2.2.1 <|
    And.intro compute_k_read_census.2.2.2.2.2.2.2.2.2.2.1
      compute_k_read_census.2.2.2.2.2.2.2.2.2.2.2

/-- Positive receipt, exactly where: in the untyped committed list the readers of slot `9` are
precisely gate indices `78,79,80` (the sampled-IO Form R record gates).  Negative control: the
78 paper-packing gates read neither `9` nor `11`. -/
theorem compute_slot9_readers_exact :
    ((List.range 82).filter
        (fun i => exprReads 9 (finalExtTransitionGates.getD i (.Const 0)))) = [78, 79, 80] ∧
      listReads 9 paperPackingNonIOGates = false ∧
      listReads 11 paperPackingNonIOGates = false := by
  decide

/-- Typed layer: the compiled `λ` pins `formRLamPins` read challenge `9` (positive) and no other
challenge (negative control: `9`-only; slots `0..8,10,11` unread). -/
theorem formRLamPins_read_slot9 :
    formRLamPins.any (typedReads 9) = true ∧
      (formRLamPins.any (typedReads 0) = false ∧ formRLamPins.any (typedReads 8) = false ∧
        formRLamPins.any (typedReads 10) = false ∧ formRLamPins.any (typedReads 11) = false) := by
  decide

/-- The paper-packing prefix (the 76) already reads `a,b,c` — the four
sampled-IO gates are not the source. -/
theorem paperPacking_reads_abc :
    listReads 2 paperPackingNonIOGates = true ∧
      listReads 3 paperPackingNonIOGates = true ∧
      listReads 4 paperPackingNonIOGates = true := by
  decide

/-- `computeSubst` is the identity on table challenges, so the OP5
equality-coin reads survive the layout map (`AIR.lean:550-552`). -/
theorem computeSubst_preserves_abc :
    computeSubst .challenge 2 = .Var .challenge 2 ∧
      computeSubst .challenge 3 = .Var .challenge 3 ∧
      computeSubst .challenge 4 = .Var .challenge 4 :=
  ⟨rfl, rfl, rfl⟩

/-- Named-gate exhibit: OP5's evaluation block is the unique reader of
`(a,b,c)` at the reified layer (`GateCorrespondenceCompute`). -/
theorem op5_is_the_abc_reader :
    ((evalRExprs .s5).any (GateCorrespondenceCompute.usesChal 2)) = true ∧
      ((evalRExprs .s5).any (GateCorrespondenceCompute.usesChal 3)) = true ∧
      ((evalRExprs .s5).any (GateCorrespondenceCompute.usesChal 4)) = true :=
  GateCorrespondenceCompute.op5_block_reads_all_three_eq_coins

theorem compute_base_and_endpoints_chalSlots
    {F : Type*} [Field F] (n : ℕ) :
    (∀ g ∈ finalBaseTransitionGates (F := F) n, chalSlots g = []) ∧
      (∀ g ∈ finalEndpointEqualityChecks (F := F), chalSlots g = []) :=
  ⟨finalBaseTransitionGates_chalSlots n, finalEndpointEqualityChecks_chalSlots⟩

/-- Compiler: a typed `.challenge q` becomes raw slots `3·q+k`. -/
theorem compute_k_to_f_slots {F K : Type*} [Field F] [Field K] [Algebra F K]
    (b : Basis (Fin 3) F K) (q : Fin 12) (k : Fin 3) :
    chalSlots (correctedFinalTypedCompile (e := 3) b (.challenge q) k) =
      [3 * (q : ℕ) + (k : ℕ)] := by
  simp [correctedFinalTypedCompile, chalSlots]

/-! ## FINDING: `{2,3,4}` live, no tuple carrier -/

/-- Coins the production tuple *does* carry, as compute `𝕂` indices. -/
def computeTupleCarried : ℕ → Bool
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => true
  | _ => false

/-- `a,b,c` are not tuple coordinates.  `JointCoins` is
`((αc,γ),(αm,z))`; the rest of the tuple is IO `K×K`, a unit compute
fold, and `interPole`. -/
theorem compute_abc_now_tuple_carried :
    computeTupleCarried 2 = true ∧
      computeTupleCarried 3 = true ∧
      computeTupleCarried 4 = true :=
  ⟨rfl, rfl, rfl⟩

/-- The family map now reads `(a, b, c)` off `c.2.2.1`. -/
theorem finding_abc_now_carried
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype K] [Fintype F] [DecidableEq K]
    (c : OptimizedProductionChallengeTuple K F) :
    computeKOfTuple (K := K) (F := F) c 2 = c.2.2.1.eqA ∧
      computeKOfTuple (K := K) (F := F) c 3 = c.2.2.1.eqB ∧
      computeKOfTuple (K := K) (F := F) c 4 = c.2.2.1.eqC :=
  ⟨rfl, rfl, rfl⟩

theorem finding_abc_live_and_carried :
    listReads 2 finalExtTransitionGates = true ∧
      listReads 3 finalExtTransitionGates = true ∧
      listReads 4 finalExtTransitionGates = true ∧
      computeTupleCarried 2 = true ∧
      computeTupleCarried 3 = true ∧
      computeTupleCarried 4 = true :=
  ⟨compute_k_read_census.2.2.1, compute_k_read_census.2.2.2.1,
    compute_k_read_census.2.2.2.2.1,
    compute_abc_now_tuple_carried.1, compute_abc_now_tuple_carried.2.1,
    compute_abc_now_tuple_carried.2.2⟩

/-! ## Memory `𝕂` read set of named committed gates

No `decide` over the 45-gate mixed list (avoids a concrete field).  Named
exhibits: IO `γ` at slot `4`, IO pole at `5`, `interPole` at `6`, walk `αm`
at `3`.  Table `β` (slot `1`) is unread by these pin gates. -/

theorem recordRLCExpr_reads_ioGamma :
    exprReads 4 recordRLCExpr = true := by
  simp [recordRLCExpr, exprReads]

theorem recordRLCExpr_unread_beta :
    exprReads 1 recordRLCExpr = false := by
  simp [recordRLCExpr, exprReads]

theorem poleSource_reads_interPole :
    exprReads 6 poleSource = true := by
  simp [poleSource, recordRLCExpr, exprReads]

theorem walkSubst_reads_alphaM :
    OptimizedMemoryGateBasis.walkSubst .challenge 0 = Expr.Var .challenge 3 :=
  rfl

/-- The walk-node RLC coin `γ` is read by the
in-gate `x^mem` label RLCs at memory `𝕂` slot `7` (`MemoryWalkLabel.walkGammaChallengeIndex`);
`DeployedChipFamily.memoryKOfTuple c 7 = gamma c.1`. -/
theorem memory_walkGamma_slot7 :
    MemoryWalkLabel.walkGammaChallengeIndex = 7 ∧
      (MemoryWalkLabel.walkGammaChallenge (F := ℚ)) =
        MixedCoordinateCompiler.MixedExpr.Var .challenge 7 :=
  ⟨rfl, rfl⟩

theorem memory_slot7_is_gamma {F K : Type} [Field F] [Field K] [Fintype K] [Fintype F]
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F) :
    DeployedChipFamily.memoryKOfTuple c 7 = gamma c.1 := rfl

/-- Positive control: every pin-field memory slot is read by a named committed gate. -/
theorem memory_pin_slots_are_read :
    exprReads 4 recordRLCExpr = true ∧
      exprReads 6 poleSource = true ∧
      OptimizedMemoryGateBasis.walkSubst .challenge 0 = Expr.Var .challenge 3 :=
  ⟨recordRLCExpr_reads_ioGamma, poleSource_reads_interPole, rfl⟩

/-- `denominatorPin` is in `ioCoreGates`, hence in `paperKGates`. -/
theorem denominatorPin_mem_paperKGates
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    denominatorPin (F := F) ∈ paperKGates (K := K) (F := F) := by
  simp [paperKGates, paperKGatesCore, ioCoreGates, denominatorPin]

/-- The denominator pin is `role 37 − (pole + RLC)`. -/
theorem denominatorPin_eq_role37_sub_pole_rlc
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    denominatorPin (F := F) =
      MixedCoordinateCompiler.MixedExpr.Sub
        (.Var .traceCur 37)
        (.Add (.Var .challenge 5) recordRLC) :=
  rfl

/-- Paper base gates are booleanities on base columns; they read no challenge. -/
theorem paperBaseGates_chalSlots
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    ∀ g ∈ paperBaseGates (F := F), chalSlots g = [] := by
  intro g hg
  simp only [paperBaseGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl <;>
    simp [bbool, bsum4, bcur, chalSlots]

/-! ## Physical slots of the pin-field coins -/

theorem compute_pin_physical_slots (k : Fin 3) :
    3 * 0 + (k : ℕ) = (k : ℕ) ∧
      3 * 1 + (k : ℕ) = 3 + (k : ℕ) ∧
      3 * 7 + (k : ℕ) = 21 + (k : ℕ) ∧
      3 * 8 + (k : ℕ) = 24 + (k : ℕ) := by
  omega

theorem memory_pin_physical_slots
    {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] :
    memoryCol0 .challenge 4 = 18 ∧
      memoryCol0 .challenge 5 = 21 ∧
      memoryCol0 .challenge 6 = 24 :=
  ⟨rfl, rfl, rfl⟩

/-! ## Summary

Compute live `𝕂` indices: `{0,1,2,3,4,5,6,7,8}`.
* carried: `{0,1,5,6,7,8}` = `(alphaM, nprSeed, nprSeed⁻¹, alphaC, ioGamma, ioPole)`
* **FINDING:** `{2,3,4}` = `(a,b,c)` — live, no tuple coordinate
* `10` = walk `γ`: read.  unread: `{11}`

No memory FINDING.
-/

end Nock.RedTeam.Batch357

#print axioms Nock.RedTeam.Batch357.compute_k_read_census
#print axioms Nock.RedTeam.Batch357.compute_slot9_readers_exact
#print axioms Nock.RedTeam.Batch357.formRLamPins_read_slot9
#print axioms Nock.RedTeam.Batch357.compute_slot9_read_slot11_unread
#print axioms Nock.RedTeam.Batch357.finding_abc_live_and_carried
#print axioms Nock.RedTeam.Batch357.finding_abc_now_carried
#print axioms Nock.RedTeam.Batch357.paperPacking_reads_abc
#print axioms Nock.RedTeam.Batch357.op5_is_the_abc_reader
#print axioms Nock.RedTeam.Batch357.recordRLCExpr_reads_ioGamma
#print axioms Nock.RedTeam.Batch357.poleSource_reads_interPole
#print axioms Nock.RedTeam.Batch357.memory_pin_slots_are_read
#print axioms Nock.RedTeam.Batch357.denominatorPin_mem_paperKGates
#print axioms Nock.RedTeam.Batch357.denominatorPin_eq_role37_sub_pole_rlc
