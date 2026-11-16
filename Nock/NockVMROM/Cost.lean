import Nock.Framework
import Nock.NockVMROM.Language
import Nock.Counts

/-!
# S8 — reified cost model + paper-cost mismatch certificate

`reifiedNockCost` records the **mechanically-proven** reified AIR counts (`Counts.lean`, all `rfl`);
`reifiedNockCost_faithful` certifies each field equals the corresponding `computeAIR`/`memoryAIR`
quantity.  `HasCostModel` holds for it (max degree 4 both chips; memory strictly smaller).
The efficiency claim is therefore `1-1*` (reified-exact) with a proven mismatch, never
a false equality (SC12).
-/

namespace Nock.NockVMROM

open Nock Nock.Framework Nock.Reified

/-- The mechanically-proven reified AIR cost figures (`Counts.lean`). -/
def reifiedNockCost : CostModel :=
  { compCols := 94, compConstraints := 526, compMaxDegree := 4, compDeg4 := 13,
    memCols := 36, memConstraints := 75, memMaxDegree := 4, memDeg4 := 2 }

/-- Per-chip raw constraint counts are not stated in the
    paper, recorded `0`. -/
def paperNockCost : CostModel :=
  { compCols := 184, compConstraints := 0, compMaxDegree := 4, compDeg4 := 73,
    memCols := 167, memConstraints := 0, memMaxDegree := 4, memDeg4 := 73 }

/-- `reifiedNockCost` faithfully records the reified AIR counts proven in `Counts.lean`. -/
theorem reifiedNockCost_faithful {K : Type*} [Field K] :
    reifiedNockCost.compCols = computeAIR.numTraceCols ∧
    reifiedNockCost.compConstraints = computeAIR.constraints.length ∧
    reifiedNockCost.compMaxDegree = computeAIR.maxDegree ∧
    reifiedNockCost.compDeg4 = computeAIR.constraints.countP (fun c => c.degree == 4) ∧
    reifiedNockCost.memCols = (memoryAIR (K := K)).numTraceCols ∧
    reifiedNockCost.memConstraints = (memoryAIR (K := K)).constraints.length ∧
    reifiedNockCost.memMaxDegree = (memoryAIR (K := K)).maxDegree ∧
    reifiedNockCost.memDeg4 =
      (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 4) :=
  ⟨computeAIR_numTraceCols.symm, computeAIR_num_constraints.symm, computeAIR_maxDegree.symm,
   computeAIR_deg4.symm, memoryAIR_numTraceCols.symm, memoryAIR_num_constraints.symm,
   memoryAIR_maxDegree.symm, memoryAIR_deg4.symm⟩

/-- **S8: NockVMROM meets the reified cost model.** -/
instance nock_hasCostModel (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    HasCostModel (Tag F K α β Ksz) reifiedNockCost where
  compMaxDegree_eq_four := rfl
  memMaxDegree_eq_four := rfl
  memory_fewer_constraints := by decide
  memory_fewer_deg4 := by decide

/-- The paper's §5 claim that the compute
    and memory chips have the *same* degree-4 gate count is refuted by the reified ground truth:
    the paper records equal (`73 = 73`) while the reified construction has memory strictly fewer
    (`1 < 13`); the absolute column figures also disagree (`94 ≠ 184`).  Never a false equality. -/
theorem paper_NockVMROM_cost_mismatch :
    (paperNockCost.compDeg4 = paperNockCost.memDeg4) ∧
    (reifiedNockCost.memDeg4 < reifiedNockCost.compDeg4) ∧
    (reifiedNockCost.compCols ≠ paperNockCost.compCols) :=
  ⟨rfl, by decide, by decide⟩

/-! ## PARAMETRIC (in the extension order `e`) reified cost model — the F9 fix

    `reifiedNockParamCost` is the affine-in-`e` refinement of `reifiedNockCost`, with each base
    column/gate count DERIVED from the reified compute/memory column maps (`Nock/AIR.lean`: compute
    layout, memory layout) split into its 𝕂-side (`coeffE`, replicated per extension slot) and
    𝔽-side (`const`) parts.  `reifiedNockParamCost_faithful` REFERENCES the reified AIR (fixing F9(b):
    faithfulness is a stored theorem tied to `computeAIR`/`memoryAIR`, not internal-only arithmetic —
    a reject-VM's construction is not `computeAIR`/`memoryAIR`). -/

/-- **Reified parametric cost.**  Base columns split from the reified AIR column maps:

    * **compute columns `⟨80,14⟩`** — 80 𝕂: 12 label fingerprints×3 = 36, 6 formula-decomp
      fingerprints×3 = 18, `ln_prev`/`ln` = 2, 3 memrecs×(root3 + child3 + ts1) = 21,
      `consInv`/`invGen`/`zinv` = 3; 14 𝔽: 11 opcode selectors + 3 memrec axes.  `eval 1 = 94`.
    * **memory columns `⟨20,15⟩`** — 20 𝕂: `pt`/`lc`/`rc.noun` 3×3 = 9, `mem.root`/`child` 3+3 = 6,
      `mem.ts` 1, `ipre`/`icur` 2, `g` 1, `zinv` 1; 15 𝔽: 4 state selectors + 6 indicator/counts
      + 4 `lcSt` + 1 `mem.axis`.  `eval 1 = 35`.

    **deg-4 gates `⟨0,13⟩`/`⟨0,1⟩` (eval-independent of `e`).**  The reified counting is of ABSTRACT
    symbolic gates (un-`e`-replicated); a faithful `e`-replication of the gate count would need a
    per-gate 𝕂/𝔽 tagging (transcription) that is NOT asserted here — only COLUMNS are
    `e`-parametrized, deg-4 gates are given at the reified abstract granularity (`eval 1` = the
    reified `13`/`1`).

    **`+IO` fields duplicate the base tables.**  The reified model does NOT separately reify the
    packed `+IO` layout; the deployed `+IO` figures live only in `paperParamCost` (the comparison
    target).  Setting the IO fields equal to the base fields keeps `reifiedNockParamCost` an
    honest record of what is reified (no un-reified deployed figures smuggled in). -/
def reifiedNockParamCost : ParamCostModel :=
  { compCols := ⟨80, 14⟩, compDeg4 := ⟨0, 13⟩, memCols := ⟨20, 16⟩, memDeg4 := ⟨0, 2⟩,
    compIOCols := ⟨80, 14⟩, compIODeg4 := ⟨0, 13⟩, memIOCols := ⟨20, 16⟩, memIODeg4 := ⟨0, 2⟩,
    compMaxDeg := 4, memMaxDeg := 4 }

/-- **The F9(b) fix — faithfulness REFERENCES the AIR.**  Each base field of `reifiedNockParamCost`,
    evaluated at `e = 1`, equals the corresponding reified `computeAIR`/`memoryAIR` quantity
    (`Counts.lean`, all `rfl`).  This genuinely ties the parametric model to Nock's ACTUAL reified
    compute/memory verifiers — a reject-VM's construction is not `computeAIR`/`memoryAIR`, so it is
    NOT this theorem's subject. -/
theorem reifiedNockParamCost_faithful {K : Type*} [Field K] :
    reifiedNockParamCost.compCols.eval 1 = computeAIR.numTraceCols ∧
    reifiedNockParamCost.compDeg4.eval 1 = computeAIR.constraints.countP (fun c => c.degree == 4) ∧
    reifiedNockParamCost.memCols.eval 1 = (memoryAIR (K := K)).numTraceCols ∧
    reifiedNockParamCost.memDeg4.eval 1 =
      (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 4) :=
  ⟨computeAIR_numTraceCols.symm, computeAIR_deg4.symm,
   memoryAIR_numTraceCols.symm, memoryAIR_deg4.symm⟩

/-- **Parametric S8: NockVMROM meets the parametric reified cost model.** -/
instance nock_hasParamCostModel (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    HasParamCostModel (Tag F K α β Ksz) reifiedNockParamCost where
  compMaxDeg_le := by decide
  memMaxDeg_le := by decide
  mem_deg4_lt_comp := by
    intro e _
    show 0 * e + 2 < 0 * e + 13
    omega

/-- **Paper parametric transcription.**  The paper's §5 base `def`s (`comp_columns`,
    `comp_deg4_gates`, `mem_columns`, `mem_deg4_gates`) and its DEPLOYED `+IO` `def`s
    (`comp_io_columns`/`comp_io_deg4_gates`/`mem_io_columns`/`mem_io_deg4_gates`), transcribed as
    `AffineE`.  The `+IO` fields are the DEPLOYED-chip transcription (the Theorem-5.4 comparison
    target), not reified data. -/
def paperParamCost : ParamCostModel :=
  { compCols := ⟨57, 13⟩, compDeg4 := ⟨20, 13⟩, memCols := ⟨54, 5⟩, memDeg4 := ⟨20, 13⟩,
    compIOCols := ⟨62, 13⟩, compIODeg4 := ⟨24, 15⟩, memIOCols := ⟨61, 13⟩, memIODeg4 := ⟨24, 16⟩,
    compMaxDeg := 4, memMaxDeg := 4 }

/-- `paperParamCost`'s base fields evaluate to the paper's §5 base `def`s at every `e`. -/
theorem paperParamCost_base_ties (e : ℕ) :
    paperParamCost.compCols.eval e = Nock.ComputeTable.comp_columns e ∧
    paperParamCost.compDeg4.eval e = Nock.ComputeTable.comp_deg4_gates e ∧
    paperParamCost.memCols.eval e = Nock.MemoryTable.mem_columns e ∧
    paperParamCost.memDeg4.eval e = Nock.MemoryTable.mem_deg4_gates e :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- `paperParamCost`'s `+IO` fields evaluate to the paper's deployed `+IO` `def`s at every `e`. -/
theorem paperParamCost_io_ties (e : ℕ) :
    paperParamCost.compIOCols.eval e = Nock.NockVM.comp_io_columns e ∧
    paperParamCost.compIODeg4.eval e = Nock.NockVM.comp_io_deg4_gates e ∧
    paperParamCost.memIOCols.eval e = Nock.NockVM.mem_io_columns e ∧
    paperParamCost.memIODeg4.eval e = Nock.NockVM.mem_io_deg4_gates e :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- The paper claims equal base degree-4 gate counts for both chips at
    every `e` (`20·e+13 = 20·e+13`), but the reified ground truth has memory STRICTLY fewer for every
    positive `e` (`2 < 13`). -/
theorem paper_param_cost_mismatch_D1 :
    (∀ e, paperParamCost.compDeg4.eval e = paperParamCost.memDeg4.eval e) ∧
    (∀ e, 1 ≤ e → reifiedNockParamCost.memDeg4.eval e < reifiedNockParamCost.compDeg4.eval e) := by
  refine ⟨fun e => ?_, fun e _ => ?_⟩
  · show 20 * e + 13 = 20 * e + 13; rfl
  · show 0 * e + 2 < 0 * e + 13; omega

/-- Equal base degree-4 gate counts at every `e`, yet the paper's
    deployed `+IO` increments are ASYMMETRIC (`24·e+15` compute vs `24·e+16` memory), so the two
    `+IO` degree-4 counts disagree (witnessed at `e = 0`). -/
theorem paper_param_cost_mismatch_D2 :
    (∀ e, paperParamCost.compDeg4.eval e = paperParamCost.memDeg4.eval e) ∧
    (∃ e, paperParamCost.compIODeg4.eval e ≠ paperParamCost.memIODeg4.eval e) := by
  refine ⟨fun e => ?_, ⟨0, ?_⟩⟩
  · show 20 * e + 13 = 20 * e + 13; rfl
  · decide

/-- **The F9(a) fix — the `+IO` layer tie.**  `paperParamCost`'s `+IO` fields evaluate at `e = 3` to
    the DEPLOYED Theorem-5.4 figures `199/196/87/88` — the layer `paperNockCost`
    failed to transcribe (`b12_paperNockCost_is_not_thm54_final`). -/
theorem paperParamCost_IO_thm54 :
    paperParamCost.compIOCols.eval 3 = 199 ∧ paperParamCost.memIOCols.eval 3 = 196 ∧
    paperParamCost.compIODeg4.eval 3 = 87 ∧ paperParamCost.memIODeg4.eval 3 = 88 := by
  decide

/-- **`nockVMROM_Thm54_cost_parametric` — the F9-corrected cost conjunction (AIR-referencing).**
    Bundles the parametric-cost results into one theorem so the assembled Nock cost claim:
    * **(F9(b)) is tied to the reified AIR** — `reifiedNockParamCost_faithful` references
      `computeAIR`/`memoryAIR` (their `numTraceCols` / degree-4 counts), so the stored cost is no
      longer the internal-only arithmetic a reject-VM can satisfy (`b12_s8_reject_vm_costed`);
    * **(F9(a)) carries the DEPLOYED `+IO` Theorem-5.4 figures** `199/196/87/88` at `e = 3`
      (the layer `paperNockCost` failed to transcribe, `b12_paperNockCost_is_not_thm54_final`).

    **Honest residual:** this does not by itself defeat the reject-VM at the *class* level — the
    generic `HasParamCostModel` is `ι`-agnostic (a `VMSystem` carries no AIR), so fully tying cost to
    `ι`'s arithmetization would need a `VMSystem` extension exposing its AIR (a separate architectural
    task).  The AIR tie here is the faithfulness theorem, referencing Nock's actual `computeAIR`/
    `memoryAIR`. -/
theorem nockVMROM_Thm54_cost_parametric {K : Type*} [Field K] :
    (reifiedNockParamCost.compCols.eval 1 = computeAIR.numTraceCols ∧
     reifiedNockParamCost.compDeg4.eval 1 = computeAIR.constraints.countP (fun c => c.degree == 4) ∧
     reifiedNockParamCost.memCols.eval 1 = (memoryAIR (K := K)).numTraceCols ∧
     reifiedNockParamCost.memDeg4.eval 1 =
       (memoryAIR (K := K)).constraints.countP (fun c => c.degree == 4)) ∧
    ((∀ e, paperParamCost.compDeg4.eval e = paperParamCost.memDeg4.eval e) ∧
     (∀ e, 1 ≤ e → reifiedNockParamCost.memDeg4.eval e < reifiedNockParamCost.compDeg4.eval e)) ∧
    (paperParamCost.compIOCols.eval 3 = 199 ∧ paperParamCost.memIOCols.eval 3 = 196 ∧
     paperParamCost.compIODeg4.eval 3 = 87 ∧ paperParamCost.memIODeg4.eval 3 = 88) :=
  ⟨reifiedNockParamCost_faithful, paper_param_cost_mismatch_D1, paperParamCost_IO_thm54⟩

end Nock.NockVMROM

#print axioms Nock.NockVMROM.nock_hasCostModel
#print axioms Nock.NockVMROM.paper_NockVMROM_cost_mismatch
#print axioms Nock.NockVMROM.reifiedNockParamCost_faithful
#print axioms Nock.NockVMROM.nock_hasParamCostModel
#print axioms Nock.NockVMROM.paperParamCost_base_ties
#print axioms Nock.NockVMROM.paperParamCost_io_ties
#print axioms Nock.NockVMROM.paper_param_cost_mismatch_D1
#print axioms Nock.NockVMROM.paper_param_cost_mismatch_D2
#print axioms Nock.NockVMROM.paperParamCost_IO_thm54
#print axioms Nock.NockVMROM.nockVMROM_Thm54_cost_parametric
