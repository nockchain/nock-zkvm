/-
  Nock/RedTeam/Batch432Thm54WalkHostsUnbound.lean

  **FINDING: walk hosts unbound at the deployed chip.**

  What
  remains true and load-bearing: `WalkSat` with a FREE `cur` is homogeneous (`walkSat_scale`),
  and `DeployedAcceptanceAt` is chip-only.  The rejection receipt for the same trace at the
  in-gate chip is `Batch438`.

  Paper puts `RLC^γ(current_node)` and the selector-gated
  child RLC sum **inside** the accumulator identity; `:1690` fixes the compute
  label as `LT_comp` (state × ((subject, formula), evaluation)).  The deployed
  chip instead hosts `cur` / `cc` / `cm` / `count` / `acc` as free overlay
  columns (`` `OptimizedComputeSubstitution.lean::finalWalkSubst` `` /
  `` `::overlayCoord` ``); honest fill is
  `` `OptimizedComputeSameExecution.lean::exactFinalTransitionEnv_walkOverlay_current` ``
  (`cur = Walk.curCol` of the 87-wide encode).  No committed gate relates those
  hosts to the row's fingerprints or the parent's `sf` triples.

  Receipts:
  * read-set: `finalWalkSubst` maps walk `cur`/`cc` source columns to
    `overlayCoord`; among `paperPackingNonIOGates` only the three
    `finalWalkSubst` walk transitions use that subst (row-local 72 use
    `computeSubst`).  Physical s1 hosts are `ext0+3·2+2` / `ext0+3·3+0`.
  * WalkSat is homogeneous in `(cur, chld', acc, seed)` — scaling by
    `scale ≠ 1` keeps the gates and makes `cur 1 ≠ rlc γ v`.
  * `DeployedAcceptanceAt` is chip RAP only (constant walk: type reaches no
    `TopologyCompressedCheck` / `RawTopologyBindingResidual` / `childLinkComp`).
  * K-side positive control:
    `` `RawTopologyAIR.lean::mutatedComputeChildPayload_rejected` `` —
    `VerifierGeneratedTopologyRAPSatisfyOfCommittedArrays` (hence
    `VerifierGeneratedSegmentedTopologyChecks`) rejects a mutated child
    payload; that binding is absent from the deployed chip.
-/
import Lean
import Nock.AIR
import Nock.Walk
import Nock.ComputeTable
import Nock.NockVMROM.Thm54.DeployedAcceptance
import Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
import Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
import Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.ProductionRawVerifier
import Nock.NockVMROM.Thm54.RawTopologyAIR
import Nock.NockVMROM.Thm54.RawTopologyRAP
import Nock.Framework.FixedPreprocessingRAP
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.overlappingInstances false

namespace Nock.RedTeam.Batch432

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Walk
open Nock.Framework
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTypedLowering
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

/-! ## Walk host layout (overlay coords 0..4)

Production order (`exactFinalTransitionEnv_walkOverlay_current`):
count / acc / current / children / multiplier = overlay coords `0..4`.
`cur` is coord `2`; `cc` is coord `3`. -/

/-- Physical index of `pubFP kind (overlayANat.s1) 2` = cur host under state `s1`. -/
def curHostAtS1 : ℕ := ext0 + 3 * overlayANat .s1 + 2

/-- Physical index of `pubFP kind (overlayBNat.s1) 0` = cc host under state `s1`. -/
def ccHostAtS1 : ℕ := ext0 + 3 * overlayBNat .s1 + 0

theorem curHostAtS1_eq : curHostAtS1 = 21 := rfl

theorem ccHostAtS1_eq : ccHostAtS1 = 22 := rfl

theorem pubFP_s1_cur (kind : VarKind) :
    pubFP kind (overlayANat .s1) 2 = .Var kind curHostAtS1 := rfl

theorem pubFP_s1_cc (kind : VarKind) :
    pubFP kind (overlayBNat .s1) 0 = .Var kind ccHostAtS1 := rfl

/-! ## Read-set: finalWalkSubst interprets cur/cc as overlay hosts -/

/-- Walk source column 3 (cur) becomes overlay coord 2 after `finalWalkSubst`. -/
theorem finalWalkSubst_cur :
    finalWalkSubst .traceCur 3 = overlayCoord .traceCur 2 ∧
      finalWalkSubst .traceNext 3 = overlayCoord .traceNext 2 := by
  constructor <;> rfl

/-- Walk source column 4 (cc) becomes overlay coord 3 after `finalWalkSubst`. -/
theorem finalWalkSubst_cc :
    finalWalkSubst .traceCur 4 = overlayCoord .traceCur 3 ∧
      finalWalkSubst .traceNext 4 = overlayCoord .traceNext 3 := by
  constructor <;> rfl

/-- `overlayCoord` for cur is the one-hot sum over `overlayA` roles (coord 2). -/
theorem overlayCoord_cur_is_oneHot (kind : VarKind) :
    overlayCoord kind 2 =
      Nock.Reified.allStates.foldr
        (fun st acc => .Add (.Mul (.Var kind (Nock.Reified.opCol st))
          (pubFP kind (overlayANat st) 2)) acc) (.Const 0) := by
  simp [overlayCoord]

/-- `overlayCoord` for cc is the one-hot sum over `overlayB` roles (coord 0). -/
theorem overlayCoord_cc_is_oneHot (kind : VarKind) :
    overlayCoord kind 3 =
      Nock.Reified.allStates.foldr
        (fun st acc => .Add (.Mul (.Var kind (Nock.Reified.opCol st))
          (pubFP kind (overlayBNat st) 0)) acc) (.Const 0) := by
  simp [overlayCoord]

/-- The three walk recurrence gates after `finalWalkSubst` sat at the tail of `crossRowSingletons` after `lnChain`.  Since
    `Batch434` the tail is the same three recurrences through
    `ComputeWalkLabel.finalWalkSubstInGate`; the hosted form is kept here as the object the
    finding was about. -/
def historicalCrossRowSingletons : List Expr :=
  [Trans.lnChainExpr.subst computeSubst,
   Trans.walkLnStep.subst finalWalkSubst,
   Trans.walkCountStep.subst finalWalkSubst,
   Trans.walkAccStep.subst finalWalkSubst]

theorem crossRow_eq_lnChain_plus_walk :
    crossRowSingletons =
      [Trans.lnChainExpr.subst computeSubst,
       Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate,
       Trans.walkCountStep.subst ComputeWalkLabel.finalWalkSubstInGate,
       Trans.walkAccStep.subst ComputeWalkLabel.finalWalkSubstInGate] :=
  rfl

/-- Read-set summary (deployed): only the three walk transitions in the packing use the walk
    subst — now `finalWalkSubstInGate`; the 72 row-local gates use `computeSubst`. -/
theorem only_walk_transitions_use_finalWalkSubst_in_packing :
    paperPackingNonIOGates =
      paperPackingRowLocal ++
        [Trans.lnChainExpr.subst computeSubst,
         Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate,
         Trans.walkCountStep.subst ComputeWalkLabel.finalWalkSubstInGate,
         Trans.walkAccStep.subst ComputeWalkLabel.finalWalkSubstInGate] ++
        OptimizedComputeGateBasis.queueWitnessGates :=
  rfl

theorem paperPackingRowLocal_length_receipt :
    paperPackingRowLocal.length = 72 :=
  paperPackingRowLocal_length

theorem walkAccInit_uses_finalWalkInitialSubst :
    finalOptimizedWalkAccInit = Trans.walkAccInit.subst finalWalkInitialSubst :=
  rfl

/-- The deployed gate reads
    `labelRLC nextReader` / `childSumCC nextReader` instead (`Batch433.inGate_subst_uses_label_rlc`). -/
theorem walkAccStep_uses_overlay_cur_cc :
    finalWalkSubst .traceNext 3 = overlayCoord .traceNext 2 ∧
      finalWalkSubst .traceNext 4 = overlayCoord .traceNext 3 ∧
      ComputeWalkLabel.finalWalkSubstInGate .traceNext 3 = ComputeWalkLabel.labelRLC
        ComputeWalkLabel.nextReader :=
  ⟨finalWalkSubst_cur.2, finalWalkSubst_cc.2, rfl⟩

/-! ## WalkSat admits unbound `cur` (scale) — the paper -/

theorem walkSat_scale
    {K : Type} [Field K]
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed ic : K} {h : ℕ}
    (scale : K) (hw : WalkSat cur chld' fo ln count acc α seed ic h) :
    WalkSat (fun i => scale * cur i) (fun i l => scale * chld' i l) fo ln count
      (fun i => scale * acc i) α (scale * seed) ic h where
  hpos := hw.hpos
  ln1 := hw.ln1
  lnInc := hw.lnInc
  count1 := hw.count1
  countInc := hw.countInc
  accInit := by
    have h0 := hw.accInit
    calc
      ln 1 * (scale * cur 1) + scale * acc 1
          = scale * (ln 1 * cur 1 + acc 1) := by ring
      _ = scale * ((∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * ic * chld' 1 l) + seed) := by
          rw [h0]
      _ = (∑ l ∈ Finset.Icc 1 (fo 1), α ^ l * ic * (scale * chld' 1 l)) + scale * seed := by
          simp [Finset.mul_sum, mul_add, mul_assoc, mul_left_comm, mul_comm]
  accStep := by
    intro i hi1 hih
    have h0 := hw.accStep i hi1 hih
    calc
      ln (i + 1) * (scale * cur (i + 1)) + scale * acc (i + 1) - scale * acc i
          = scale * (ln (i + 1) * cur (i + 1) + acc (i + 1) - acc i) := by ring
      _ = scale * ∑ l ∈ Finset.Icc 1 (fo (i + 1)),
            α ^ l * count i * chld' (i + 1) l := by rw [h0]
      _ = ∑ l ∈ Finset.Icc 1 (fo (i + 1)),
            α ^ l * count i * (scale * chld' (i + 1) l) := by
          simp [Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

theorem scale_cur_ne_rlc
    {K : Type} [Field K] {node_size : ℕ}
    {cur1 scale γ : K} {v : Fin node_size → K}
    (hscale : scale ≠ 1) (hcur : cur1 = rlc γ v) (hne0 : cur1 ≠ 0) :
    scale * cur1 ≠ rlc γ v := by
  intro heq
  apply hscale
  refine mul_right_cancel₀ hne0 ?_
  calc
    scale * cur1 = rlc γ v := heq
    _ = cur1 := hcur.symm
    _ = (1 : K) * cur1 := (one_mul _).symm

theorem walkSat_scale_unbound_cur
    {K : Type} [Field K] {node_size : ℕ}
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed ic : K} {h : ℕ}
    {γ : K} {v : Fin node_size → K}
    (scale : K) (hscale : scale ≠ 1) (hcur : cur 1 = rlc γ v) (hne0 : cur 1 ≠ 0)
    (hw : WalkSat cur chld' fo ln count acc α seed ic h) :
    WalkSat (fun i => scale * cur i) (fun i l => scale * chld' i l) fo ln count
        (fun i => scale * acc i) α (scale * seed) ic h ∧
      scale * cur 1 ≠ rlc γ v :=
  ⟨walkSat_scale scale hw, scale_cur_ne_rlc hscale hcur hne0⟩

/-! ## DeployedAcceptanceAt is chip-only (no topology / label bind) -/

theorem deployedAcceptanceAt_is_chip_raps
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (h : DeployedAcceptanceAt P c Qc Qm) :
    RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc ∧
      RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm :=
  ⟨h.compute_satisfies, h.memory_satisfies⟩

section ConstantWalk
open Lean Meta Elab Command

def DEPLOYED_ACC : Name :=
  ``Nock.NockVMROM.Thm54.DeployedAcceptanceAt

def TOPO_CHECK : Name :=
  ``Nock.NockVMROM.Thm54.TopologyCompressedCheck

def TOPO_RESIDUAL : Name :=
  ``Nock.NockVMROM.Thm54.RawTopologyBindingResidual

def CHILD_LINK : Name :=
  ``Nock.ComputeTable.childLinkComp

elab "#batch432_acceptance_topology_blind" : command => do
  let env ← getEnv
  let some ci := env.find? DEPLOYED_ACC
    | throwError "DeployedAcceptanceAt missing"
  let tyConsts := ci.type.getUsedConstants
  if tyConsts.contains TOPO_CHECK then
    throwError "DeployedAcceptanceAt type reaches TopologyCompressedCheck"
  if tyConsts.contains TOPO_RESIDUAL then
    throwError "DeployedAcceptanceAt type reaches RawTopologyBindingResidual"
  if tyConsts.contains CHILD_LINK then
    throwError "DeployedAcceptanceAt type reaches childLinkComp"
  logInfo m!"Batch432: DeployedAcceptanceAt type is topology-blind \
    ({tyConsts.size} constants)"

#batch432_acceptance_topology_blind

end ConstantWalk

/-! ## K-side positive control — VerifierGeneratedSegmentedTopologyChecks -/

theorem kside_rejects_mutated_compute_child_payload
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {p : ℕ} [CharP K p]
    (R : RawPlusIOSegmentedFamily F K) (A : RawTopologyArrays R)
    (i : Fin R.cfg.compRows) (slot : Fin 3)
    (hi : (slot : ℕ) <
      ComputeTable.fanoutComp (computeTopologyNodeAt R i).label.1)
    (hne : A.compute.childPayload i slot ≠ computeLookupPayload R i slot) :
    ¬ VerifierGeneratedTopologyRAPSatisfyOfCommittedArrays R A :=
  mutatedComputeChildPayload_rejected R A i slot hi hne

open ProductionRawVerifier

/-- K-side: mutated child payload fails the verifier-generated topology RAP
    (the content of `Message.VerifierGeneratedSegmentedTopologyChecks`). -/
theorem kside_segmented_rejects_mutated_compute_child_payload
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [FiniteDimensional F K] {p : ℕ} [CharP K p]
    (R : RawPlusIOSegmentedFamily F K) (M : Message R p)
    (i : Fin R.cfg.compRows) (slot : Fin 3)
    (hi : (slot : ℕ) <
      ComputeTable.fanoutComp (computeTopologyNodeAt R i).label.1)
    (hne : M.topology.compute.childPayload i slot ≠
      computeLookupPayload R i slot) :
    ¬ M.VerifierGeneratedSegmentedTopologyChecks := by
  intro h
  -- `VerifierGeneratedSegmentedTopologyChecks` is defeq to the arrays RAP form
  change VerifierGeneratedTopologyRAPSatisfyOfCommittedArrays R M.topology at h
  exact kside_rejects_mutated_compute_child_payload R M.topology i slot hi hne h

/-! ## Named FINDING -/

/-- 1. Any `DeployedAcceptanceAt` is only the two chip RAPs (no topology /
     `childLinkComp` / label RLC bind) — `#batch432_acceptance_topology_blind`.
  2. Walk bookkeeping with a FREE `cur` is homogeneous: scale
     `(cur, chld', acc, seed)` by `scale ≠ 1` and the gates still hold while
     `cur 1 ≠ rlc γ v`.  This is why hosting `cur` binds nothing.
  3. The deployed packing now takes the walk
     transitions through `finalWalkSubstInGate` (conjunct 3 below states the deployed list).
  4. K-side positive control: the same unbound child / `sf` mismatch is rejected
     by `VerifierGeneratedSegmentedTopologyChecks`
     (`mutatedComputeChildPayload_rejected`). -/
theorem walk_hosts_unbound_at_deployed_chip
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)] [FiniteDimensional F K] {hOrb : ℕ}
    (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
    (c : OptimizedProductionChallengeTuple K F)
    (Qc : Fin (P.computeChipAt c).rap.w → F[X])
    (Qm : Fin (P.memoryChipAt c).rap.w → F[X])
    (hAcc : DeployedAcceptanceAt P c Qc Qm)
    {cur : ℕ → K} {chld' : ℕ → ℕ → K} {fo : ℕ → ℕ}
    {ln count acc : ℕ → K} {α seed ic : K} {hRows : ℕ}
    {γ : K} {node_size : ℕ} {v : Fin node_size → K} {scale : K}
    (hw : WalkSat cur chld' fo ln count acc α seed ic hRows)
    (hscale : scale ≠ 1) (hcur : cur 1 = rlc γ v) (hne0 : cur 1 ≠ 0) :
    (RAP.SatisfiesWithPreprocessing (P.computeChipAt c) Qc ∧
      RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm) ∧
    (WalkSat (fun i => scale * cur i) (fun i l => scale * chld' i l) fo ln count
        (fun i => scale * acc i) α (scale * seed) ic hRows ∧
      scale * cur 1 ≠ rlc γ v) ∧
    (paperPackingNonIOGates =
      paperPackingRowLocal ++
        [Trans.lnChainExpr.subst computeSubst,
         Trans.walkLnStep.subst ComputeWalkLabel.finalWalkSubstInGate,
         Trans.walkCountStep.subst ComputeWalkLabel.finalWalkSubstInGate,
         Trans.walkAccStep.subst ComputeWalkLabel.finalWalkSubstInGate] ++
        OptimizedComputeGateBasis.queueWitnessGates) ∧
    (finalWalkSubst .traceNext 3 = overlayCoord .traceNext 2 ∧
      finalWalkSubst .traceNext 4 = overlayCoord .traceNext 3 ∧
      curHostAtS1 = 21 ∧ ccHostAtS1 = 22) :=
  ⟨deployedAcceptanceAt_is_chip_raps P c Qc Qm hAcc,
    walkSat_scale_unbound_cur scale hscale hcur hne0 hw,
    only_walk_transitions_use_finalWalkSubst_in_packing,
    finalWalkSubst_cur.2, finalWalkSubst_cc.2, curHostAtS1_eq, ccHostAtS1_eq⟩

end Nock.RedTeam.Batch432

#print axioms Nock.RedTeam.Batch432.curHostAtS1_eq
#print axioms Nock.RedTeam.Batch432.ccHostAtS1_eq
#print axioms Nock.RedTeam.Batch432.finalWalkSubst_cur
#print axioms Nock.RedTeam.Batch432.finalWalkSubst_cc
#print axioms Nock.RedTeam.Batch432.only_walk_transitions_use_finalWalkSubst_in_packing
#print axioms Nock.RedTeam.Batch432.walkSat_scale
#print axioms Nock.RedTeam.Batch432.scale_cur_ne_rlc
#print axioms Nock.RedTeam.Batch432.walkSat_scale_unbound_cur
#print axioms Nock.RedTeam.Batch432.deployedAcceptanceAt_is_chip_raps
#print axioms Nock.RedTeam.Batch432.kside_segmented_rejects_mutated_compute_child_payload
#print axioms Nock.RedTeam.Batch432.walk_hosts_unbound_at_deployed_chip
