import Nock.NockVMROM.Thm54.CensusExtraClosure

/-!
# Fingerprint `C4` (`ConsDecomposedFP`) measured BEFORE any field is added

**Scope.  This module adds no field to any structure.**  `ComputeRowSemanticData` still has
the same named fields, `CensusRecordPremises` still has five, `ResidualPremises` still has
four, and `skeletonBounded` is still named.  Nothing here ticks a `§J` checkbox.

The paper's three
`cons` constraints are between `K³` NPR evaluations, with `Lem:NPR_decomp` (`1218-1225`) the fingerprint→noun bridge.

## Verdict recorded here: DECLINE as a carrier field

The three fingerprint equations are already what `Vcomp` / `memBlk` check.  `of_vcomp` is a projection of accepted-row conjuncts, so adding
`ConsDecomposedFP` as a `ComputeRowSemanticData` field would fail the equivalence gate
(rename of accepted-row content) — the same pattern as `C6` (`FirstLineCarrier.lean`).

Reflection to nouns still needs `OpcodeSemantics.PairFaithful`, whose `right_bounded` *is*
`BoundedBy q` of the cell (`CensusExtraClosure.consReflection_is_circular_without_a_bound`).
`skeletonBounded` therefore stays named.

The dummy `.s1` row has the three fingerprint equations (the two gated ones vacuously) and
fails `Vcomp` on `SVhead` / `headAtom.leaf` (`0 = 1` in every field).  Discriminator is
`SVhead`, not `mr1.axis` (the latter is `0 = 3`, which holds in characteristic 3).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54

open scoped Classical
open Nock
open ComputeTable
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTrace
open Nock.NockVMROM.Thm54.OpcodeSemantics
open Nock.NockVMROM.Thm54.ExactExecution
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.CensusExtraClosure

noncomputable section


variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The three fingerprint `cons` constraints of Algorithm `NockCompute`, gated by `decActive` on the BFS label state `row.1`.  Production name is
`FP.cons`, not the draft `ComputeTable.consFP`. -/
structure ConsDecomposedFP (row : State × DTcomp K) : Prop where
  formula_cons : row.2.2.1.f = FP.cons row.2.1.z row.2.2.2.f_h row.2.2.2.f_t
  tail_cons :
    decActive row.1 .f_th = true →
      row.2.2.2.f_t = FP.cons row.2.1.z row.2.2.2.f_th row.2.2.2.f_tt
  branchTail_cons :
    decActive row.1 .f_tth = true →
      row.2.2.2.f_tt = FP.cons row.2.1.z row.2.2.2.f_tth row.2.2.2.f_ttt

namespace ConsDecomposedFP

/-- Tail `cons` is the first `memBlk` conjunct after `mr2` on every state that lives
`f_th`.  Reads `pub.state` so `of_vcomp` only rewrites activity. -/
theorem memBlk_tail_cons {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hmem : memBlk inp pub dec)
    (hact : decActive pub.state .f_th = true) :
    dec.f_t = FP.cons inp.z dec.f_th dec.f_tt := by
  have hlive := ((decActive_cases pub.state).2.2.1).mp hact
  rcases hlive with h | h | h | h | h | h
  all_goals
    simp [memBlk, h] at hmem
    exact hmem.2.1.symm

/-- Branch-tail `cons` is the second `memBlk` cons on `.s6` only. -/
theorem memBlk_branchTail_cons {inp : Inputs K} {pub : Pub K} {dec : Dec K}
    (hmem : memBlk inp pub dec)
    (hact : decActive pub.state .f_tth = true) :
    dec.f_tt = FP.cons inp.z dec.f_tth dec.f_ttt := by
  have hs6 : pub.state = .s6 := ((decActive_cases pub.state).2.2.2.2.1).mp hact
  simp [memBlk, hs6] at hmem
  exact hmem.2.2.2.1.symm

/-- Projection of `Vcomp` once the BFS label agrees with `pub.state`
(`ComputeRowAccepted.1`).  `formula_cons` is `Vcomp.1`; the gated equations are `memBlk`. -/
theorem of_vcomp {row : State × DTcomp K}
    (hst : row.1 = row.2.2.1.state) (hv : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    ConsDecomposedFP row where
  formula_cons := hv.1
  tail_cons hact := memBlk_tail_cons hv.2.2.2.1 (by rw [← hst]; exact hact)
  branchTail_cons hact := memBlk_branchTail_cons hv.2.2.2.1 (by rw [← hst]; exact hact)

/-- `formula_cons` is definitionally the first `Vcomp` conjunct. -/
theorem formula_cons_eq_vcomp_cons {row : State × DTcomp K}
    (hst : row.1 = row.2.2.1.state) (hv : Vcomp row.2.1 row.2.2.1 row.2.2.2) :
    (of_vcomp hst hv).formula_cons = hv.1 :=
  rfl

/-- Every accepted compute row already satisfies the fingerprint equations. -/
theorem of_computeRowAccepted {cfg : ExactConfig F K} {row : State × DTcomp K}
    (h : ComputeRowAccepted cfg row) : ConsDecomposedFP row :=
  of_vcomp h.1 h.2.2

/-- Every indexed compute row of a buildable execution already has the fingerprint equations. -/
theorem of_buildable (E : BuildableNockExecution F K) (i : Fin E.cfg.compRows) :
    ConsDecomposedFP (E.exec.computeRowAt i) :=
  of_computeRowAccepted (computeRowAt_accepted E.chained.semantic.1 i)

/-- Local copy of `TraceGen.Gen.zeroComputeRow` at `.s1`.  Do not import `TraceGen.Gen`. -/
def dummyS1Row : State × DTcomp K :=
  (.s1, ⟨0, 0, 0, 0, 0⟩,
    { state := .s1, s := 0, f := 0, e := 0
      sf1_s := 0, sf1_f := 0, sf1_e := 0, sf2_s := 0, sf2_f := 0, sf2_e := 0
      sf3_s := 0, sf3_f := 0, sf3_e := 0, ln_prev := 0, ln := 0
      mr1 := MemRec.zero, mr2 := MemRec.zero, mr3 := MemRec.zero },
    ⟨0, 0, 0, 0, 0, 0⟩)

/-- `FP.cons 0 0 0 = 0` (field inverse at zero is zero). -/
theorem cons_zero : FP.cons (0 : K) 0 0 = 0 := by
  ext <;> simp [FP.cons]

/-- The dummy `.s1` row satisfies the three fingerprint equations (two vacuously). -/
theorem dummyS1_holds : ConsDecomposedFP (dummyS1Row (K := K)) where
  formula_cons := by
    change (0 : FP K) = FP.cons (0 : K) 0 0
    exact cons_zero.symm
  tail_cons hact := by
    simp [dummyS1Row, decActive, hasTailDecomposition] at hact
  branchTail_cons hact := by
    simp [dummyS1Row, decActive] at hact

/-- Discriminator is `SVhead` / `headAtom.leaf`: dummy zeros give `0 = 1`.
Characteristic-independent (`NeZero 1`).  Do not use `mr1.axis` (`0` vs `3`). -/
theorem dummyS1_not_vcomp :
    ¬ Vcomp (dummyS1Row (K := K)).2.1 (dummyS1Row (K := K)).2.2.1
        (dummyS1Row (K := K)).2.2.2 := by
  intro hv
  have hsv : SVhead (dummyS1Row (K := K)).2.1 (dummyS1Row (K := K)).2.2.1
      (dummyS1Row (K := K)).2.2.2 := hv.2.2.1
  simp [dummyS1Row, SVhead, headAtom, State.toNat] at hsv

/-- Fingerprint `C4` is strictly weaker than `Vcomp`: the dummy has the cons equations
and fails the verifier on `SVhead`. -/
theorem dummyS1_cons_without_vcomp :
    ConsDecomposedFP (dummyS1Row (K := K)) ∧
      ¬ Vcomp (dummyS1Row (K := K)).2.1 (dummyS1Row (K := K)).2.2.1
          (dummyS1Row (K := K)).2.2.2 :=
  ⟨dummyS1_holds, dummyS1_not_vcomp⟩

/-- Reflection of the always-operative formula `cons` (`Lem:NPR_decomp`).
Does not smuggle `BoundedBy`; `PairFaithful.right_bounded` is the bound. -/
theorem formula_is_cell_of_cons {q : ℕ} {row : State × DTcomp K}
    {formula head tail : Noun} (hc : ConsDecomposedFP row) (hz : row.2.1.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (hform : Realizes row.2.1.z row.2.2.1.f formula)
    (hhead : Realizes row.2.1.z row.2.2.2.f_h head)
    (htail : Realizes row.2.1.z row.2.2.2.f_t tail)
    (hfaith : PairFaithful row.2.1.z q formula (.cell head tail)) :
    formula = .cell head tail :=
  cell_eq_of_cons_encoding hz hcast formula head tail hfaith <| by
    calc
      FP.cons row.2.1.z (enc row.2.1.z head) (enc row.2.1.z tail)
          = FP.cons row.2.1.z row.2.2.2.f_h row.2.2.2.f_t := by
            rw [← hhead, ← htail]
        _ = row.2.2.1.f := hc.formula_cons.symm
        _ = enc row.2.1.z formula := hform

/-- Reflection of the gated tail `cons`. -/
theorem tail_is_cell_of_cons {q : ℕ} {row : State × DTcomp K}
    {tail th tt : Noun} (hc : ConsDecomposedFP row) (hact : decActive row.1 .f_th = true)
    (hz : row.2.1.z ≠ 0) (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htail : Realizes row.2.1.z row.2.2.2.f_t tail)
    (hth : Realizes row.2.1.z row.2.2.2.f_th th)
    (htt : Realizes row.2.1.z row.2.2.2.f_tt tt)
    (hfaith : PairFaithful row.2.1.z q tail (.cell th tt)) :
    tail = .cell th tt :=
  cell_eq_of_cons_encoding hz hcast tail th tt hfaith <| by
    calc
      FP.cons row.2.1.z (enc row.2.1.z th) (enc row.2.1.z tt)
          = FP.cons row.2.1.z row.2.2.2.f_th row.2.2.2.f_tt := by
            rw [← hth, ← htt]
        _ = row.2.2.2.f_t := (hc.tail_cons hact).symm
        _ = enc row.2.1.z tail := htail

/-- Reflection of the gated branch-tail `cons`. -/
theorem branchTail_is_cell_of_cons {q : ℕ} {row : State × DTcomp K}
    {tt tth ttt : Noun} (hc : ConsDecomposedFP row)
    (hact : decActive row.1 .f_tth = true) (hz : row.2.1.z ≠ 0)
    (hcast : Set.InjOn (fun k : ℕ => (k : K)) (Set.Iio q))
    (htt : Realizes row.2.1.z row.2.2.2.f_tt tt)
    (htth : Realizes row.2.1.z row.2.2.2.f_tth tth)
    (httt : Realizes row.2.1.z row.2.2.2.f_ttt ttt)
    (hfaith : PairFaithful row.2.1.z q tt (.cell tth ttt)) :
    tt = .cell tth ttt :=
  cell_eq_of_cons_encoding hz hcast tt tth ttt hfaith <| by
    calc
      FP.cons row.2.1.z (enc row.2.1.z tth) (enc row.2.1.z ttt)
          = FP.cons row.2.1.z row.2.2.2.f_tth row.2.2.2.f_ttt := by
            rw [← htth, ← httt]
        _ = row.2.2.2.f_tt := (hc.branchTail_cons hact).symm
        _ = enc row.2.1.z tt := htt

/-- Re-cite: fingerprint cons does not yield a noun bound without `PairFaithful`. -/
theorem consReflection_still_needs_PairFaithful {z : K} {q : ℕ} {f h t : Noun}
    (hpf : PairFaithful z q f (.cell h t)) :
    FieldEmbedding.BoundedBy q h ∧ FieldEmbedding.BoundedBy q t :=
  consReflection_is_circular_without_a_bound hpf

/-- `ComputeRowSemanticData` still has no cons-decomposition field. -/
theorem computeRowSemanticData_still_no_cons_field {q Λ : ℕ}
    {row : State × DTcomp K} (d : ComputeRowSemanticData q Λ row) :
    d =
      { root := d.root
        tails := d.tails
        branchTails := d.branchTails
        calls := d.calls
        windows := d.windows
        axisGates := d.axisGates
        tails_count := d.tails_count
        branchTails_count := d.branchTails_count
        calls_count := d.calls_count
        windows_count := d.windows_count
        axisGates_count := d.axisGates_count
        realizedNouns := d.realizedNouns
        subject_mem := d.subject_mem
        formula_mem := d.formula_mem
        result_mem := d.result_mem
        bounded := d.bounded
        comparisons := d.comparisons
        comparison_faithful := d.comparison_faithful
        comparison_leaves := d.comparison_leaves
        comparison_roles := d.comparison_roles
        axisGate_listed := d.axisGate_listed
        axisGate_tail_mem := d.axisGate_tail_mem
        needs := d.needs } := by
  cases d
  rfl

/-- Census extras are still five named fields; `skeletonBounded` is still one of them. -/
theorem censusRecordPremises_still_five {E : BuildableNockExecution F K}
    {P : ResidualPremises E} {M : MemoryRecordPremises E}
    (C : CensusRecordPremises E P M) :
    C =
      { slotSemantics := C.slotSemantics
        census := C.census
        sizeWindowBound := C.sizeWindowBound
        skeletonBounded := C.skeletonBounded
        combinedBounded := C.combinedBounded } :=
  censusRecordPremises_still_five_here C

/-- Residual premises are still four. -/
theorem residualPremises_still_four_here {E : BuildableNockExecution F K}
    (P : ResidualPremises E) :
    InactiveDecPaddingExec E.exec ∧
      (∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i)) ∧
        E.q = ringChar K :=
  GenericHonestCommitment.residualPremises_still_four P

end ConsDecomposedFP

#print axioms ConsDecomposedFP.memBlk_tail_cons
#print axioms ConsDecomposedFP.memBlk_branchTail_cons
#print axioms ConsDecomposedFP.of_vcomp
#print axioms ConsDecomposedFP.formula_cons_eq_vcomp_cons
#print axioms ConsDecomposedFP.of_computeRowAccepted
#print axioms ConsDecomposedFP.of_buildable
#print axioms ConsDecomposedFP.cons_zero
#print axioms ConsDecomposedFP.dummyS1_holds
#print axioms ConsDecomposedFP.dummyS1_not_vcomp
#print axioms ConsDecomposedFP.dummyS1_cons_without_vcomp
#print axioms ConsDecomposedFP.formula_is_cell_of_cons
#print axioms ConsDecomposedFP.tail_is_cell_of_cons
#print axioms ConsDecomposedFP.branchTail_is_cell_of_cons
#print axioms ConsDecomposedFP.consReflection_still_needs_PairFaithful
#print axioms ConsDecomposedFP.computeRowSemanticData_still_no_cons_field
#print axioms ConsDecomposedFP.censusRecordPremises_still_five
#print axioms ConsDecomposedFP.residualPremises_still_four_here

end

end Nock.NockVMROM.Thm54
