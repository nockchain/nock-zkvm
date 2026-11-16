/-
  Nock/NockVMROM/Thm54/AxisAtomsOp9.lean

  Designed C5 inhabitant at an OP9 reconstruction: `ExactExecutionLocalCertificates`
  on `(Op9Execution hfirst).semanticData`. Buys the named `ResidualPremises.axisAtoms`
  extra at this written scope (already inhabited independently in
  `SlotSemanticsOp9.residualPremises`; C5 is the licensed object, not a
  `BuildableNockExecution` field).

  Scope (in force for this module; nothing wider is claimed).
  * Execution: `Op9Execution` / `K3`, parent `.s9` + two `.s1` children, `Λ = 7`.
  * Certificates: `LocalOpcodeCertificate.s9` on `parentRowData` (axis atom 2,
    arm-fetch served lookup, two recursive `evalFBy`s) and `.s1` on each child.
    Transported along `castRowData` onto `semanticData.rows`.
  * Not done: no fifteenth field; statement-layer `op9ParentCertificate_nonempty`
    is a different row; capstone untouched; `Gen.lean` / `BFSAssign.lean` not
    touched. Generic `∀ E` axisAtoms still requires C5 (or the extra) as input.
-/
import Nock.NockVMROM.Thm54.SlotSemanticsOp9
import Nock.NockVMROM.Thm54.TraceGen.Op9BuildablePartsK3

namespace Nock.NockVMROM.Thm54.AxisAtomsOp9

open scoped Classical
open Nock Nock.Walk Nock.ComputeTable Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.TraceGen
  (op9Subject op9ParentFormula op9ParentTail op9Result op9AxisAtom
    op9CoreNoun op9CoreFormula op9Arm)
open Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3
open Nock.NockVMROM.Thm54.SlotSemanticsOp9
  (rows_zero rows_one rows_two)

noncomputable section

variable (hfirst :
  ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.counts = 0 ∧
    ((exec seedZ alphaA).memoryPubAt ⟨0, by norm_num [cfg]⟩).pt.indicator = 0)


private theorem one_lt_comp : (1 : ℕ) < (cfg seedZ alphaA).compRows := by decide
private theorem two_lt_comp : (2 : ℕ) < (cfg seedZ alphaA).compRows := by decide

private theorem op9_one : (1 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  change (1 : ℕ) < (cfg seedZ alphaA).compRows
  exact one_lt_comp

private theorem op9_two : (2 : ℕ) < (Op9Execution hfirst).cfg.compRows := by
  change (2 : ℕ) < (cfg seedZ alphaA).compRows
  exact two_lt_comp

theorem cast_injOn_97 :
    Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio 97) := by
  intro m hm n hn h
  exact CharP.natCast_injOn_Iio K 97 hm hn h

theorem seedZ_ne : (compInputs seedZ alphaA).z ≠ 0 := by
  simpa [compInputs] using seedZ_ne_zero

/-- Recast a local certificate along a row-identity. `castRowData` is
`h.symm ▸ d`; this is the matching transport on `LocalOpcodeCertificate`. -/
def recastCertificate
    {row₁ row₂ : ComputeTable.State × ComputeTable.DTcomp K}
    (h : row₁ = row₂) {d : ComputeRowSemanticData 97 7 row₂}
    (c : LocalOpcodeCertificate 97 7 d) :
    LocalOpcodeCertificate 97 7 (castRowData h d) := by
  subst h
  exact c

/-- Parent `.s9` production certificate on the execution-layer row data.
Axis atom is `2`; arm-fetch is `parentServedLookup` -/
def parentCertificate : LocalOpcodeCertificate 97 7 parentRowData :=
  .s9 parentRowData 3 2 parentTailR parentCall1 parentCall2 rfl seedZ_ne
    cast_injOn_97
    (by simp [ComparisonListed, parentRowData, parentComparisons, parentRoot, op9Head])
    (by simp [ComparisonListed, parentRowData, parentComparisons, parentRoot,
        op9ParentFormula, op9Head])
    (by simp [ComparisonListed, parentRowData, parentComparisons, parentRoot,
        parentTailR, op9ParentTail])
    (by simp [ComparisonListed, parentRowData, parentComparisons, parentTailR,
        op9AxisAtom])
    (by simp [ComparisonListed, parentRowData, parentComparisons, parentRoot,
        parentCall1, op9Subject])
    (by simp [ComparisonListed, parentRowData, parentComparisons, parentTailR,
        parentCall1, op9CoreFormula])
    (by simp [ComparisonListed, parentRowData, parentComparisons, parentCall1,
        parentCall2, op9CoreNoun])
    (by simp [ComparisonListed, parentRowData, parentComparisons, parentRoot,
        parentCall2, op9Result])
    parentServedLookup.realization
    parentServedLookup.served
    (by rfl)
    (by rfl)
    parent_accepts

/-- Child `.s1` (core evaluation) production certificate. Axis clauses vacuous. -/
def child1Certificate : LocalOpcodeCertificate 97 7 child1RowData :=
  .s1 child1RowData 0 rfl seedZ_ne cast_injOn_97
    (by simp [ComparisonListed, child1RowData, child1Comparisons, child1Root, op1Head])
    (by simp [ComparisonListed, child1RowData, child1Comparisons, child1Root, op1Head])
    (by simp [ComparisonListed, child1RowData, child1Comparisons, child1Root])
    child1_accepts

/-- Child `.s1` (arm evaluation) production certificate. Axis clauses vacuous. -/
def child2Certificate : LocalOpcodeCertificate 97 7 child2RowData :=
  .s1 child2RowData 0 rfl seedZ_ne cast_injOn_97
    (by simp [ComparisonListed, child2RowData, child2Comparisons, child2Root, op1Head])
    (by simp [ComparisonListed, child2RowData, child2Comparisons, child2Root, op1Head])
    (by simp [ComparisonListed, child2RowData, child2Comparisons, child2Root])
    child2_accepts

/-- Designed C5 at `(Op9Execution hfirst).semanticData`. Not a carrier field. -/
def localCertificates :
    ExactExecutionLocalCertificates (Op9Execution hfirst).semanticData where
  rows := fun i =>
    if h0 : (i : ℕ) = 0 then
      have hi : i = ⟨0, (Op9Execution hfirst).cfg.compRows_pos⟩ := Fin.ext h0
      hi ▸ ((rows_zero hfirst) ▸ recastCertificate
        Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_zero
        parentCertificate)
    else if h1 : (i : ℕ) = 1 then
      have hi : i = ⟨1, op9_one hfirst⟩ := Fin.ext h1
      hi ▸ ((rows_one hfirst) ▸ recastCertificate
        Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_one
        child1Certificate)
    else
      have h2 : (i : ℕ) = 2 := by
        have hrows : (Op9Execution hfirst).cfg.compRows = 3 := rfl
        have hi : (i : ℕ) < 3 := by
          rw [← hrows]
          exact i.isLt
        omega
      have hi : i = ⟨2, op9_two hfirst⟩ := Fin.ext h2
      hi ▸ ((rows_two hfirst) ▸ recastCertificate
        Nock.NockVMROM.Thm54.TraceGen.Op9ConfigK3.computeRowAt_two
        child2Certificate)

/-- Non-vacuity: C5 is inhabited at a live honest execution. -/
theorem localCertificates_nonempty :
    Nonempty (ExactExecutionLocalCertificates (Op9Execution hfirst).semanticData) :=
  ⟨localCertificates hfirst⟩

/-- Named `axisAtoms` at this written scope, from the C5 inhabitant.
The extra is the production atom-shape consequence of C5, not a fixture
case-split on `Op9Execution` rows -/
theorem named_axisAtoms :
    ∀ i : Fin (Op9Execution hfirst).cfg.compRows,
      AxisAtomPremises ((Op9Execution hfirst).semanticData.rows i) :=
  axisAtoms_of_localCertificates (localCertificates hfirst)

end

end Nock.NockVMROM.Thm54.AxisAtomsOp9

#print axioms Nock.NockVMROM.Thm54.AxisAtomsOp9.parentCertificate
#print axioms Nock.NockVMROM.Thm54.AxisAtomsOp9.child1Certificate
#print axioms Nock.NockVMROM.Thm54.AxisAtomsOp9.child2Certificate
#print axioms Nock.NockVMROM.Thm54.AxisAtomsOp9.localCertificates
#print axioms Nock.NockVMROM.Thm54.AxisAtomsOp9.named_axisAtoms
