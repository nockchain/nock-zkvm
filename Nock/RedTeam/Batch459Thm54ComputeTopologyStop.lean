/-
  Nock/RedTeam/Batch459Thm54ComputeTopologyStop.lean

  Brief step 3 asked for `WalkSat` at `lblC`/`foC`, then `VecBFT_reconstruct_of_label` and
  `reconForest_ForestReconGoal_of_label → RawComputeTopologyBinding` at `execOfTraces`,
  filling `TracesWalkHyps.sfCompute` / `validCompute`.  The two reconstruction theorems
  take `hSf : Sf fo h + 1 = h` and `hvalid : BFSValid fo h` as HYPOTHESES; so does
  `walk_IOP_soundness_card` (`hlen`).  In this tree they are derived from a committed
  **queue-length gate** only — `Walk.QGate` (`bfsValid_of_qgate`, `Sf_tiling_of_qgate`;
  census #5, "the paper's self-evident step is false without the gate") — and the deployed
  compute chip carries no such gate: `Nock.Walk.QGate` is reached by no constant of
  `DeployedChipFamily.computeChipAt` (constant walk below, positive controls
  `Trans.walkAccInit` reached; `QGate` reached from `Walk.Sf_tiling_of_qgate`).

  Two abstract witnesses at the paper's `WalkSat`, `initial_count = α`
  and the honest seed, `out_walk = 0`:
  * `walkSat_without_bfsValid`: `h = 3`, `fo = (0, 2, 0)` — node 2's children are nodes 2 and
    3 (self-loop), `BFSValid` false, tiling true — census #5's witness, accepted at EVERY `α`;
  * `walkSat_without_tiling`: `h = 2`, `fo = (0, 0)`, `cur 2 = 0` — `Sf fo 2 + 1 = 1 ≠ 2`,
    accepted at every `α`.

  Neither witness is an `(α, γ)` event: the walk gates alone never force the fanout column to tile.
-/
import Lean
import Nock.Walk
import Nock.NockVMROM.Thm54.DeployedChipFamily
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.RedTeam.Batch337Thm54HostileGapAudit
import Nock.RedTeam.Batch398Thm54PublicConjuncts
import Nock.RedTeam.Batch455Thm54ComputeTopology
import Nock.RedTeam.Batch457Thm54RootLabelFromChip
import Nock.NockVMROM.Thm54.WrapFixesVcomp
import Nock.NockVMROM.Thm54.P8Core.Batch459Thm54ComputeTopologyStop
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch459

open Lean Meta Elab Command
open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ComputeWalkSeed
open Nock.NockVMROM.Thm54.ComputeWalkLabel
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeTemplate
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.ComputePaperPacking
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP
open OptimizedComputeHostileAccumulator
open OptimizedHostileTimestamps
open Nock.RedTeam.Batch398
open Nock.RedTeam.Batch438
open Nock.RedTeam.Batch455
open Nock.RedTeam.Batch457

/-! ## A. Constant walk — no queue-length gate on the deployed compute chip -/

/-- Names under `Nock.Walk.QGate` (the structure and its projections). -/
def isQGateName (n : Name) : Bool := (`Nock.Walk.QGate).isPrefixOf n

def CHIP : Name := ``Nock.NockVMROM.Thm54.DeployedChipFamily.computeChipAt
def WALK_INIT : Name := ``Nock.Reified.Trans.walkAccInit
def TILING_THM : Name := ``Nock.Walk.Sf_tiling_of_qgate

/-! Negative: no `QGate` name is reached from the deployed compute chip's definition.
Positive controls: the chip reaches `Trans.walkAccInit` (the instrument sees the walk
gates), and `Walk.Sf_tiling_of_qgate` reaches a `QGate` name (the instrument sees `QGate`
where it is).  Throws on any failed expectation. -/
run_cmd do
  let env ← getEnv
  let rChip := Batch337.reachSet env CHIP
  let rTiling := Batch337.reachSet env TILING_THM
  let chipQ := rChip.toList.filter isQGateName
  let tilingQ := rTiling.toList.filter isQGateName
  logInfo m!"computeChipAt reach={rChip.size}; QGate names reached: {chipQ}"
  logInfo m!"Sf_tiling_of_qgate reach={rTiling.size}; QGate names reached: {tilingQ}"
  unless chipQ.isEmpty do
    throwError "deployed compute chip reaches a QGate name: {chipQ}"
  unless rChip.contains WALK_INIT do
    throwError "positive control failed: computeChipAt does not reach Trans.walkAccInit"
  unless !tilingQ.isEmpty do
    throwError "positive control failed: Sf_tiling_of_qgate reaches no QGate name"

/-! ## B. Abstract witnesses at the paper's `WalkSat` -/

section Witnesses
variable {K : Type} [Field K]

theorem sum_Icc_one_two (f : ℕ → K) : ∑ k ∈ Finset.Icc 1 2, f k = f 1 + f 2 := by
  rw [show (2 : ℕ) = 1 + 1 from rfl, Finset.sum_Icc_succ_top (by norm_num), Finset.Icc_self,
    Finset.sum_singleton]

/-- Census #5's witness at `WalkSat`: `h = 3`, `fo = (0, 2, 0)`, `initial_count = α`,
`seed = α · root`, `out_walk = 0`, for EVERY `α` — and `BFSValid` fails at node 2. -/
theorem walkSat_without_bfsValid (α root c21 c22 : K) :
    ∃ (cur : ℕ → K) (chld' : ℕ → ℕ → K) (ln count acc : ℕ → K),
      WalkSat cur chld' (fun i => if i = 2 then 2 else 0) ln count acc α (α * root) α 3 ∧
        acc 3 = 0 ∧ ¬ BFSValid (fun i => if i = 2 then 2 else 0) 3 := by
  refine ⟨fun i => if i = 1 then root else if i = 2 then c21 else c22,
    fun i l => if i = 2 ∧ l = 1 then c21 else if i = 2 ∧ l = 2 then c22 else 0,
    fun i => α ^ i, fun i => if i = 1 then α else α ^ 3,
    fun i => if i = 2 then α ^ 3 * c22 else 0, ?_, ?_, ?_⟩
  · refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro i hi1 hih
      ring
    · simp
    · intro i hi1 hih
      rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
      · simp; ring
      · simp
    · simp
    · intro i hi1 hih
      rcases (show i = 1 ∨ i = 2 by omega) with rfl | rfl
      · simp only [show (1 : ℕ) + 1 = 2 from rfl]
        simp
        rw [sum_Icc_one_two]
        simp
        ring
      · simp
  · simp
  · intro hv
    have h := hv 2 (by norm_num) (by norm_num)
    simp [Sf, Finset.Icc_self] at h

/-- `h = 2`, `fo = (0, 0)`, `cur 2 = 0`: `WalkSat` + `out_walk = 0` at EVERY `α` with the
honest seed, yet `Sf fo 2 + 1 = 1 ≠ 2` — the tiling is not a consequence of the walk gates. -/
theorem walkSat_without_tiling (α root : K) :
    ∃ (cur : ℕ → K) (chld' : ℕ → ℕ → K) (ln count acc : ℕ → K),
      WalkSat cur chld' (fun _ => 0) ln count acc α (α * root) α 2 ∧
        acc 2 = 0 ∧ Sf (fun _ => 0) 2 + 1 ≠ 2 := by
  refine ⟨fun i => if i = 1 then root else 0, fun _ _ => 0, fun i => α ^ i, fun _ => α,
    fun _ => 0, ?_, rfl, ?_⟩
  · refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp
    · intro i hi1 hih
      ring
    · simp
    · intro i hi1 hih
      simp
    · simp
    · intro i hi1 hih
      have : i = 1 := by omega
      subst this
      simp
  · simp [Sf]

end Witnesses

/-! ## C. Status -/

def topologyPipelineStatus : List (String × String) :=
  [("0 label_rlc_is_decoded_label", "landed (Batch438)"),
    ("1 walk gates vanish from DeployedAcceptanceAt", "landed (Batch454)"),
    ("2 WalkSat at lblC / foC",
      "landed at the committed operands (deployed_walkSat); initial_count = computeWalkAlpha"),
    ("3 VecBFT_reconstruct_of_label", "STOP: hSf/hvalid not gate-forced (no QGate); initial_count"),
    ("4 reconForest_ForestReconGoal_of_label → RawComputeTopologyBinding",
      "STOP: depends on 3")]

theorem topologyPipelineStatus_length : topologyPipelineStatus.length = 5 := by decide

theorem topologyPipelineStatus_names :
    topologyPipelineStatus.map Prod.fst = topologyPipeline := by
  decide

/-- The gate that would close the tiling: `Walk.QGate fo q qinv 1 h` — a committed
queue-length column `q` with inverse witness `qinv`, `q 1 = 1`, `q (i+1) = q i + fo i − 1`,
`q i · qinv i = 1`, `q h + fo h − 1 = 0` (`Walk.lean`, census #5). -/
def MISSING_GATE : String := "Nock.Walk.QGate on the deployed compute chip (queue-length column)"

/-- `computeTopology` stays on the live open list. -/
theorem computeTopology_still_open : "computeTopology" ∈ openConjuncts := by
  decide

theorem openConjuncts_length_unmoved : openConjuncts.length = 10 :=
  openConjuncts_length

/-- `TracesWalkHyps`' compute half stays a named hypothesis. -/
def computeWalkHypsOpen : List String := Batch455.computeWalkHypsOpen

theorem computeWalkHypsOpen_length : computeWalkHypsOpen.length = 2 := by decide

theorem kside_consumers_kept : ksideComputeTopologyConsumers.length = 4 :=
  kside_consumers_length

/-! ## `WalkSat` at the committed operands, decoded per row

`out_walk = acc h = 0` from `finalMaskedWalkOut`.
This is the honest content of the deployed walk gates; steps 3–4 do not follow from it
(sections A–C). -/

section Assembly

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hsat
include hax hbasis hwidth

omit hax hbasis hwidth in
theorem pubAt_state (i : Fin (rows P)) : (pubAt P c Qc hsat i).state = stAt P c Qc hsat i := rfl

/-! ### Row shift: `traceNext` at row `i` is `trace` at row `i+1` (orbit adjacency) -/

/-! ### The successor-row operands, decoded -/

/-! ### Overlay coordinates are `selSum`s: evaluate them by the one-hot collapse -/

/-! ### The first-row operands, decoded (public masks = selectors at row 0) -/

/-! ### The last row: terminal masks = selectors, `out_walk = 0` -/

/-! ### The three packed walk transitions off the last row -/

/-! ### The `ℕ`-indexed walk columns (rows `1..h` read row `i − 1`) -/

/-! ### Decoding at `lblC` / `foC` (honest-width trace through `familyQc`) -/

end Assembly

section AtLblC

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (hsat : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))

include hsat

/-- `foW` is `ExecOfTraces.foC` on `1..rows P`. -/
theorem foW_eq_foC (i : ℕ) (hi1 : 1 ≤ i) (_hih : i ≤ rows P) :
    foW P c (familyQc P c Qc₀) hsat i = ExecOfTraces.foC P Qc₀ c i := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < rows P := by omega
  simp only [foW, ExecOfTraces.foC, rowOf_succ P k hk]
  rw [ExecOfTraces.lblC_succ P Qc₀ c ⟨k, hk⟩, ExecOfTraces.lblCAt_eq_rowEnvAt,
    stAt_eq_computeStateOf P c (familyQc P c Qc₀) hsat]

/-- `curW` is `RLC^γ` of `ExecOfTraces.lblC`'s `Pub` on `1..rows P`. -/
theorem curW_eq_lblC (i : ℕ) (hi1 : 1 ≤ i) (_hih : i ≤ rows P) :
    curW P c (familyQc P c Qc₀) hsat i =
      Walk.rlc (gamma c.1) (labelVecOfPub (ExecOfTraces.lblC P Qc₀ c i).2.2.1) := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  have hk : k < rows P := by omega
  simp only [curW, pubAt, rowOf_succ P k hk]
  rw [ExecOfTraces.lblC_succ P Qc₀ c ⟨k, hk⟩, ExecOfTraces.lblCAt_eq_rowEnvAt,
    stAt_eq_computeStateOf P c (familyQc P c Qc₀) hsat]

end AtLblC

/-! ### Status of step 2 -/

/-- `chldW` is the DECLARED child payload
(`childVecN`, Option A hosted tags), which is what the walk gates read; relating it to
`ExecOfTraces.clabC` is step 3's business and is not attempted (`clabC` sets the child
state to the parent's state, not the hosted tag — noted, not adjudicated). -/
def step2Landed : List String :=
  ["deployed_walkSat", "deployed_walk_out", "foW_eq_foC", "curW_eq_lblC"]

theorem step2Landed_length : step2Landed.length = 4 := by decide

end Nock.RedTeam.Batch459

#print axioms Nock.RedTeam.Batch459.deployed_walkSat
#print axioms Nock.RedTeam.Batch459.deployed_walk_out
#print axioms Nock.RedTeam.Batch459.foW_eq_foC
#print axioms Nock.RedTeam.Batch459.curW_eq_lblC
#print axioms Nock.RedTeam.Batch459.walkSat_without_bfsValid
#print axioms Nock.RedTeam.Batch459.walkSat_without_tiling
#print axioms Nock.RedTeam.Batch459.topologyPipelineStatus_names
