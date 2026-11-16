import Nock.NockVMROM.Thm54.ServedForestCommitment
import Nock.NockVMROM.Thm54.ServedForestParams
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
# `ServedForestOp4` — the OP₄ instantiation of the generic honest-commitment module (stage 7)

**Regression discipline.**  Every seam field is discharged from an *existing* concrete lemma, and at
`op4Params` the generic objects reduce *definitionally* to their concrete `MultiRootHonestCommitment`
counterparts (`parentSkeletonRowG op4Exec` ≡ `parentSkeletonRow`, `skelMG op4Exec` ≡ `skelM`,
`computeNodesMG op4Exec` ≡ `computeNodesM`, …).  Consequently `op0Statement` (`TraceGen.Op0Gen`) is
**untouched**: it still routes through the concrete `multiRootExecution`/`dataM`, so its statement and
its axiom set are unchanged.  This file only *adds* the generic OP₄ route as feasibility evidence.
-/

namespace Nock.NockVMROM.Thm54.ServedForestModule

open Nock Nock.Noun
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.OptimizedStrictNonterminalConcrete
open Nock.NockVMROM.Thm54.NonterminalServedRow
open Nock.NockVMROM.Thm54.MultiRootServedFixture
open Nock.NockVMROM.Thm54.MultiRootHonestCommitment
open Nock.NockVMROM.Thm54.ServedForest
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

noncomputable section

local instance : Fact (Nat.Prime 97) := ⟨by norm_num⟩
noncomputable local instance : Fintype K97cubic := Fintype.ofFinite K97cubic
noncomputable local instance : DecidableEq K97cubic := Classical.decEq K97cubic
local instance : CharP K97cubic 97 := inferInstance
local instance : CharP K97cubic (ringChar K97cubic) := ringChar.charP K97cubic

/-! ## A. `op4Exec` — `op4Params` bundled with the concrete compute parent-row seam -/

/-- **The OP₄ served-forest execution.** -/
def op4Exec : ServedForestExec where
  toServedForestParams := op4Params
  parentPub := parentPubS
  parentDec := parentDecS
  parentAccepts := parentS_accepts
  parentWf := parentS_wf
  parentActiveReq := by
    show NockVM.activeRequestRecords parentPubS = [parentRecordS]
    simp [NockVM.activeRequestRecords, parentPubS]
  parentLineHandoff := compute_line_handoffS
  parentLineOrigin := rfl
  parentRowData := NonterminalServedRow.parentRowData
  parentRowServed := rfl
  parentRowNoun := parentRow_nounRealization
  semParentRec := semParentRec
  semParentTs := rfl
  semParentBridge := semParentRec_bridge
  parentRowFcomp := parentRowS_accepts
  parentFanout := rfl

/-! ## B. `op4Commit` — the six skeleton obligations + the two parent-compute-seam proofs

At `op4Exec` the committed skeleton is *definitionally* the concrete `skelM`, so each obligation is
discharged by its `MultiRootHonestCommitment` counterpart. -/

/-! ## B'. The committed objects at OP₄ reproduce the concrete `MultiRootHonestCommitment` objects

The parent compute skeleton's `decomposition` field is the *only* non-definitional coincidence: it
carries the opcode head (`op4Exec.parentHead ≡ parentHeadS`) inside an anonymous `match`, whose
matcher does not reduce under the slot binder, so equality needs one `funext`/`cases`.  Everything
else (state, subject, formula, evaluation, subformula, memory record; the timestamp and the row) is
definitional.  This lifts to the committed node trees and hence the whole skeleton. -/

theorem parentSkeletonRowG_eq_op4 : parentSkeletonRowG op4Exec = parentSkeletonRow := by
  have hdec : (parentSkeletonRowG op4Exec).decomposition = parentSkeletonRow.decomposition := by
    funext slot h; cases slot <;> rfl
  -- Every field but `decomposition` is definitional; structure eta closes the outer steps.
  calc parentSkeletonRowG op4Exec
      = { parentSkeletonRow with decomposition := (parentSkeletonRowG op4Exec).decomposition } := rfl
    _ = { parentSkeletonRow with decomposition := parentSkeletonRow.decomposition } := by rw [hdec]
    _ = parentSkeletonRow := rfl

theorem parentNodeG_eq_op4 : parentNodeG op4Exec = parentNode := by
  calc parentNodeG op4Exec
      = { parentNode with skel := parentSkeletonRowG op4Exec } := rfl
    _ = { parentNode with skel := parentSkeletonRow } := by rw [parentSkeletonRowG_eq_op4]
    _ = parentNode := rfl

/-- The committed compute node tree at OP₄ reproduces the concrete `computeNodesM`. -/
theorem computeNodesMG_eq_op4 : computeNodesMG op4Exec = computeNodesM := by
  calc computeNodesMG op4Exec
      = .node (parentNodeG op4Exec) [.node servedNode []] := rfl
    _ = .node parentNode [.node servedNode []] := by rw [parentNodeG_eq_op4]
    _ = computeNodesM := rfl

/-- The committed memory node forest at OP₄ is *definitionally* the concrete `memoryNodesM`. -/
theorem memoryNodesMG_eq_op4 : memoryNodesMG op4Exec = memoryNodesM := rfl

/-- The committed skeleton at OP₄ reproduces the concrete `skelM`. -/
theorem skelMG_eq_op4 : skelMG op4Exec = skelM := by
  calc skelMG op4Exec
      = skeletonOfNodes (computeNodesMG op4Exec) (memoryNodesMG op4Exec) := rfl
    _ = skeletonOfNodes computeNodesM memoryNodesM := by
        rw [computeNodesMG_eq_op4, memoryNodesMG_eq_op4]
    _ = skelM := rfl

/-! ## C. `op4Commit` — the six skeleton obligations + the two parent-compute-seam proofs

Each obligation is discharged by its `MultiRootHonestCommitment` counterpart after transporting
along `skelMG_eq_op4` / `parentSkeletonRowG_eq_op4`. -/

/-- **The OP₄ honest commitment.** -/
def op4Commit : ServedForestCommit where
  toServedForestExec := op4Exec
  parentComputeBind := by rw [parentSkeletonRowG_eq_op4]; exact bind_parentRow
  parentComputeStamp := stamp_parentRow
  slotSem := by rw [skelMG_eq_op4]; exact slotSemanticsM
  recordEq := by rw [skelMG_eq_op4]; exact recordEquationsM
  censusC := by rw [skelMG_eq_op4]; exact censusM
  sizeWindowB := by rw [skelMG_eq_op4]; exact sizeWindowBoundM
  skelBounded := by rw [skelMG_eq_op4]; exact skeletonBoundedM
  combinedB := by rw [skelMG_eq_op4]; exact combinedBoundedM
  pairedRecordLayout := pairedRecordLayoutSG _
  honestVer := honestVerSG _
  generatedC := by rw [skelMG_eq_op4]; exact residualM_generated

/-! ## C'. The generic honest commitment at OP₄ carries the concrete committed node trees. -/

theorem dataMG_op4_computeNodes : (dataMG op4Commit).computeNodes = computeNodesM :=
  computeNodesMG_eq_op4

theorem dataMG_op4_memoryNodes : (dataMG op4Commit).memoryNodes = memoryNodesM :=
  memoryNodesMG_eq_op4

/-! ## D. The generic OP₄ release: the fourteen-conjunct statement, instantiated at `op4Commit` -/

/-- **The released fourteen-conjunct Theorem-5.4 statement over the generic OP₄ package.**  This is
`statementMG` at the OP₄ instantiation; the consumed capstone
`optimizedFullStrictNockVMROM_of_package` is unchanged. -/
theorem op4Statement_generic
    (hmoreMG : BuildableAxisWitness.LaterSeedZeros
      (servedForestModule op4Commit.toServedForestExec))
    (hax : FormRAxisBound (packageMG op4Commit hmoreMG).optimized.sampled
      (packageMG op4Commit hmoreMG).optimized.basis)
    (hbasis : FormRBasis (packageMG op4Commit hmoreMG).optimized.basis)
    (hwidth : FormRWidth F97) :
    OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageMG op4Commit hmoreMG) :=
  statementMG op4Commit hmoreMG hax hbasis hwidth

theorem op4Statement_generic_nonvacuous
    (hmoreMG : BuildableAxisWitness.LaterSeedZeros
      (servedForestModule op4Commit.toServedForestExec))
    (hax : FormRAxisBound (packageMG op4Commit hmoreMG).optimized.sampled
      (packageMG op4Commit hmoreMG).optimized.basis)
    (hbasis : FormRBasis (packageMG op4Commit hmoreMG).optimized.basis)
    (hwidth : FormRWidth F97) :
    Nonempty
      (OptimizedStrictFullPackage.OptimizedFullStrictThm54Statement (packageMG op4Commit hmoreMG)) :=
  ⟨op4Statement_generic hmoreMG hax hbasis hwidth⟩

end

end Nock.NockVMROM.Thm54.ServedForestModule

#print axioms Nock.NockVMROM.Thm54.ServedForestModule.op4Exec
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.op4Commit
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.skelMG_eq_op4
#print axioms Nock.NockVMROM.Thm54.ServedForestModule.op4Statement_generic
