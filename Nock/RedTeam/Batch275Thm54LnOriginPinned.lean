/-
  Nock/RedTeam/Batch275Thm54LnOriginPinned.lean

  The paper's uniqueness argument needs the origin: the paper says
  the timestamp "has the closed form `z^i` where `i` is the compute table line number", `:1884`
  calls `ln` "the total number of memory accesses requested until that row".

  The repair (`OptimizedComputeCorrectedFinal.finalLnInit`): one degree-two typed endpoint
  `isFirst · (ln_prev − 1)` joins `correctedEndpoint2` (`4 → 5`), `C.rap.s = 124 → 127`,
  `Thm54Resources.computeDegreeOneGates 4·e → 5·e`.  `w = 199` unchanged.

  **HONESTY (the `JU` §3 point, not retracted):** `V_comp` reads
  `ln_prev` in every clause and pins it **nowhere**, and `Lem:equiv_compute` (`:1697-1699`) is an
  iff against that `V_comp`.  So the deployed chip is now **strictly stronger** than the paper's
  compute verifier: `GenericHonestCommitment.vcomp_s1_ignores_first_ln_prev` shows `V_comp`
  accepts a row whose `ln_prev` (and `ln`, `mr1.ts` with it) is rescaled by any `lnPrev'`, while
  `rescaled_ln_rejected` below shows the deployed chip rejects the uniformly rescaled trace for
  every `c ≠ 1`.  This is a paper gap the tree closes on the compute side only — `JU` §1's
  memory-side objection (no pin on the response side, no ordering of responses) is untouched.
  The shadow AIR's whole-trace iff `computeSegmentedRAP_wholeTrace_iff` (`TraceEncoding.lean`) is
  about `Trans.computeAIRchained`, not the deployed chip, and is unchanged.

  This file is the receipt at the consumed chip `P.computeChip`, for **any** accepted trace:

  * `lnInit_mem_endpoint2` — the origin gate is a committed degree-two endpoint;
  * `ln_prev_starts_at_one` — the gathered role `54` at the first row is `1`
    (`= OptimizedHostileTimestamps.hostile_ln0_eq_one`);
  * `rescaled_ln_rejected` — for any accepted trace, multiplying the six `ln_prev`/`ln` columns
    (roles `54`, `55`; columns `175..180`) by a constant `c ≠ 1` is **rejected**.  At `c = 0` this
    is the `MA` §2 `ln₀ = 0` witness; at the honest trace it is exactly the rescaling
    `vcomp_s1_ignores_first_ln_prev` shows `V_comp` would accept;
  * `honest_trace_accepted` — the honest trace still passes (the package's `computeLineOrigin`);
  * `computeDegreeOneGates_reads_back` — the resource counter reads `5·e`, `15` at `e = 3`, and
    the capstone's numerals are `199/127`, `s − 40 = 87`.

  Not claimed: anything about the memory chip; any change to a capstone theorem's *type*.
-/
import Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch275

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedHostileTimestamps
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Module
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## A. The gate -/

/-- The origin gate is a committed degree-two endpoint of the deployed compute chip. -/
theorem lnInit_mem_endpoint2 : lnInitTyped ∈ correctedEndpoint2 :=
  OptimizedHostileTimestamps.lnInit_mem_endpoint2

/-- What it says on any typed row: `isFirst · (ln_prev − 1)`. -/
theorem lnInit_eval (env : CorrectedFinalTypedEnv F K) :
    lnInitTyped.eval env = algebraMap F K (env.baseTrace 11) * (lnPrevAt env - 1) :=
  OptimizedHostileTimestamps.lnInit_eval env

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## B. At the consumed chip -/

/-- **`ln_prev` starts at `1`**: for any accepted trace, the gathered role `54` at the first row
is `1`. -/
theorem ln_prev_starts_at_one (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc) :
    lnPrevAt (rowEnv P Qc (firstRow P)) = 1 :=
  hostile_ln0_eq_one P Qc hsat

/-! ## C. The rescaled trace is rejected -/

/-- The six `ln_prev`/`ln` columns: roles `54`, `55`, columns `175..180`. -/
def IsLnCol (i : ℕ) : Prop := 175 ≤ i ∧ i < 181

instance (i : ℕ) : Decidable (IsLnCol i) := by unfold IsLnCol; infer_instance

/-- `Q` with the `ln_prev`/`ln` columns multiplied by the constant `c` — the uniform rescaling of
`W_comp`'s two line columns, which `V_comp` (`:1728-1742`) cannot see
(`vcomp_s1_ignores_first_ln_prev`: every clause reads `ln_prev` only through
`ln = ln_prev · z^k` and `ts = ln_prev · z^k`; the decoded timestamps rescale with it). -/
def rescaleLn (c : F) {w : ℕ} (Q : Fin w → F[X]) : Fin w → F[X] :=
  fun col => if IsLnCol (col : ℕ) then Polynomial.C c * Q col else Q col

theorem rescaleLn_lnPrev (c : F) {w : ℕ} (hw : 178 ≤ w) (Q : Fin w → F[X]) (k : Fin 3) (x : F) :
    (rescaleLn c Q ⟨175 + (k : ℕ), by omega⟩).eval x = c * (Q ⟨175 + (k : ℕ), by omega⟩).eval x := by
  have hc : IsLnCol (175 + (k : ℕ)) := by unfold IsLnCol; omega
  simp [rescaleLn, hc]

/-- The rescaled trace's gathered `ln_prev` at any row is `c • ` the original's. -/
theorem rescaled_lnPrev (Qc : Fin P.computeChip.rap.w → F[X]) (c : F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    lnPrevAt (rowEnv P (rescaleLn c Qc) i) = algebraMap F K c * lnPrevAt (rowEnv P Qc i) := by
  simp only [lnPrevAt, rowEnv, gatherCorrectedFinalTypedEnv, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw : 178 ≤ P.computeChip.rap.w := by change 178 ≤ 303; norm_num
  have hidx : correctedFinalExtCoordIndex (e := 3) (54 : Fin 63) k = 175 + (k : ℕ) := by
    simp [correctedFinalExtCoordIndex]
  have hlt : 175 + (k : ℕ) < P.computeChip.rap.w := by change _ < 303; omega
  rw [hidx]
  simp only [envOfTrace, dif_pos hlt]
  rw [rescaleLn_lnPrev c hw Qc k, Algebra.smul_def, Algebra.smul_def, map_mul, mul_assoc]

/-- **The rescaled `ln` trace is REJECTED.**  For any trace the deployed chip accepts and any
`c ≠ 1`, `rescaleLn c Qc` is not accepted: its first-row `ln_prev` is `c ≠ 1`, and
`isFirst · (ln_prev − 1) = 0` refuses it. -/
theorem rescaled_ln_rejected (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc) (c : F) (hc : c ≠ 1) :
    ¬ RAP.SatisfiesWithPreprocessing P.computeChip (rescaleLn c Qc) := by
  intro hsat'
  have h1 := ln_prev_starts_at_one P Qc hsat
  have h2 := ln_prev_starts_at_one P (rescaleLn c Qc) hsat'
  rw [rescaled_lnPrev, h1, mul_one] at h2
  exact hc ((algebraMap F K).injective (by rw [h2, map_one]))

theorem zero_origin_rejected (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc) :
    ¬ RAP.SatisfiesWithPreprocessing P.computeChip (rescaleLn 0 Qc) :=
  rescaled_ln_rejected P Qc hsat 0 zero_ne_one

/-! ## D. Completeness and the resource read-back -/

/-- The honest trace is still accepted: the gate is discharged by the package's
`computeLineOrigin` (`OptimizedStrictNockVMROMPackage`), i.e. the honest execution's
`ln_prev(0) = 1`. -/
theorem honest_trace_accepted [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    RAP.SatisfiesWithPreprocessing P.computeChip (canonicalComputeTrace P) :=
  canonicalComputeTrace_satisfies P hax hbasis hwidth

/-- The counter reads back `5·e`, and the capstone's compute numerals are `199/127`, `s − 40 = 87`
(`Thm54Resources.computeDegreeOneGates`, `released_capstone_deployed_numerals`). -/
theorem computeDegreeOneGates_reads_back [Fintype F] [DecidableEq F] :
    Thm54Resources.computeDegreeOneGates 3 = 19 ∧
      (∀ e, Thm54Resources.computeDegreeOneGates e = 6 * e + 1) ∧
      P.computeChip.rap.w = 303 ∧ P.computeChip.rap.s = 418 ∧ P.computeChip.rap.s - 44 = 374 := by
  have h := released_capstone_deployed_numerals P
  exact ⟨rfl, fun _ => rfl, h.1.1, h.1.2.1, h.2.2.1⟩

end Deployed

end

end Nock.RedTeam.Batch275

#print axioms Nock.RedTeam.Batch275.lnInit_mem_endpoint2
#print axioms Nock.RedTeam.Batch275.ln_prev_starts_at_one
#print axioms Nock.RedTeam.Batch275.rescaled_ln_rejected
#print axioms Nock.RedTeam.Batch275.zero_origin_rejected
#print axioms Nock.RedTeam.Batch275.honest_trace_accepted
#print axioms Nock.RedTeam.Batch275.computeDegreeOneGates_reads_back
