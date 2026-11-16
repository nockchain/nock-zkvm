/-
  Nock/RedTeam/Batch269Thm54ComputeAccumulatorAnchored.lean

  **The compute chip's IO accumulator is anchored: it starts at `0` and ends at the public
  `requests`.**

  The paper has both ends: `acc_prog` is a running sum from `0` whose final
  value is the RAP output `requests = acc_prog(h₁)` (`:534-537`), equated with the memory side by
  the IO consistency check `requests = responses` (`:597`).

  The repair (`OptimizedComputeCorrectedFinal`, `OptimizedComputeFiniteIOGates`):

  `w = 199` is unchanged (a column was re-purposed, none added); `C.rap.s = 118 → 124`.

  This file is the receipt at the consumed chip `P.computeChip`, for **any** accepted trace:

  * `acc_starts_at_zero` — at the first row the gathered accumulator is `0`;
  * `accAfter_ends_at_requests` — at the last row the gathered `acc_after` equals the gathered
    public `requests` (= `Σ computePublic (6+k) • b k`, `gathered_requests`);
  * `step_at_every_row` — the anchored step vanishes at every row, the last included;
  * `chain_off_last_row` — off the last row `acc_after(i) = acc(i+1)`;
  * `moved_accumulator_rejected` — bumping the three accumulator columns by any constant `c ≠ 0`
    (the `Batch267` attack) is now **rejected**, at `isFirst · acc`;
  * `canonical_trace_accepted` — the honest trace still passes, so the anchors cost no
    completeness.

  With `LL`/`LN` on the memory side, both LogUp accumulators now telescope hostilely from `0` to
  the one shared public `requests`.
-/
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
import Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.RedTeam.Batch269

open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.CoordinateBasis
open Nock.NockVMROM.Thm54.CoordinateCompiler
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeBaseGates
open Nock.NockVMROM.Thm54.OptimizedComputeFinal
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeGateBasis
open Nock.NockVMROM.Thm54.OptimizedComputeSubstitution
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.StrictExtension
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.MultiRootOptimizedAcceptance
open Module
open scoped Polynomial

noncomputable section

open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace

variable {F K : Type} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K]

/-! ## A. The two anchors, as typed gates of the committed degree-two endpoint bucket -/

/-- Typed form of `isFirst · acc`. -/
def accInitTyped : CorrectedFinalTypedExpr := (correctedLowerFinal finalAccInit).getD (.const 0)

/-- Typed form of `isLast · (acc_after − requests)`. -/
def accTerminalTyped : CorrectedFinalTypedExpr :=
  (correctedLowerFinal finalAccTerminal).getD (.const 0)

theorem lower_accInit : correctedLowerFinal finalAccInit = some accInitTyped := by decide

theorem lower_accTerminal : correctedLowerFinal finalAccTerminal = some accTerminalTyped := by
  decide

/-- Both anchors are members of the committed degree-two endpoint bucket. -/
theorem anchors_mem_endpoint2 :
    accInitTyped ∈ correctedEndpoint2 ∧ accTerminalTyped ∈ correctedEndpoint2 := by
  constructor <;>
  · rw [correctedEndpoint2, List.mem_filterMap]
    first
    | exact ⟨finalAccInit, by simp, lower_accInit⟩
    | exact ⟨finalAccTerminal, by simp, lower_accTerminal⟩

/-- What the anchors say on any typed environment. -/
theorem accInit_eval (env : CorrectedFinalTypedEnv F K) :
    accInitTyped.eval env = algebraMap F K (env.baseTrace 11) * env.extTrace 32 := by
  rw [← correctedLowerFinal_eval env _ _ lower_accInit]
  simp [finalAccInit, OptimizedComputeTemplate.fixedIsFirst, Expr.eval,
    CorrectedFinalTypedEnv.toSourceEnv]

theorem accTerminal_eval (env : CorrectedFinalTypedEnv F K) :
    accTerminalTyped.eval env =
      algebraMap F K (env.baseTrace 12) * (env.extTrace 60 - env.extensionPublic 2) := by
  rw [← correctedLowerFinal_eval env _ _ lower_accTerminal]
  simp [finalAccTerminal, OptimizedComputeTemplate.fixedIsLast, Expr.eval,
    CorrectedFinalTypedEnv.toSourceEnv, accAfterIndex]

/-! ## B. At the consumed chip -/

section Deployed

variable [Fintype K] [DecidableEq K] [CharP K (ringChar K)] {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- The gathered typed environment of `Qc` at row `i`. -/
abbrev rowEnv (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) : CorrectedFinalTypedEnv F K :=
  gatherCorrectedFinalTypedEnv P.optimized.basis
    (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      P.optimized.computeChallenge P.optimized.computePublic)

abbrev firstRow : Fin P.optimized.family.problem.cfg.compRows :=
  ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩

abbrev lastRow : Fin P.optimized.family.problem.cfg.compRows :=
  ⟨P.optimized.family.problem.cfg.compRows - 1,
    Nat.sub_lt P.optimized.family.problem.cfg.compRows_pos (by omega)⟩

/-- The source obligations at every row of an accepted trace. -/
theorem row_obligations (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    CorrectedComputeSourceObligations P.optimized.family.problem.cfg.compRows (rowEnv P Qc i)
      (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
        P.optimized.computeChallenge P.optimized.computePublic) := by
  have h := (productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit Qc).1 hsat
  exact h.2 _ (by simp [rowNodeSet])

/-- The preprocessing binding read at row `i`: base slot `11` is the first-row mask and slot
`12` the last-row mask. -/
theorem masks_at_row (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (rowEnv P Qc i).baseTrace 11 = (if (i : ℕ) = 0 then 1 else 0) ∧
      (rowEnv P Qc i).baseTrace 12 = (if i = lastRow P then 1 else 0) := by
  have hbind := ((productionNamedComputeRAP_satisfies_iff_sourceLanguage
    P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes P.optimized.basis
    P.optimized.computeChallenge P.optimized.computePublic P.optimized.orbit Qc).1 hsat).1
  have hinj := (P.optimized.computeRealization hax hbasis hwidth).nodes_injective
  have h0 := hbind ⟨0, by change 0 < 2; norm_num⟩
  have h1 := hbind ⟨1, by change 1 < 2; norm_num⟩
  have h11 : 11 < P.computeChip.rap.w := by change 11 < 303; norm_num
  have h12 : 12 < P.computeChip.rap.w := by change 12 < 303; norm_num
  have hc0 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
      P.optimized.computePublic P.optimized.orbit).preprocessingColumn
        ⟨0, by change 0 < 2; norm_num⟩ = ⟨11, h11⟩ := rfl
  have hc1 : (ProductionNamedComputeRAP P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes P.optimized.basis P.optimized.computeChallenge
      P.optimized.computePublic P.optimized.orbit).preprocessingColumn
        ⟨1, by change 1 < 2; norm_num⟩ = ⟨12, h12⟩ := rfl
  rw [hc0] at h0
  rw [hc1] at h1
  constructor
  · show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      P.optimized.computeChallenge P.optimized.computePublic).trace 11 = _
    simp only [envOfTrace, dif_pos h11]
    rw [show (Qc ⟨11, h11⟩) = Nock.Framework.firstRowMask P.optimized.computeNodes from h0,
      Nock.Framework.firstRowMask_eval _ hinj]
  · show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
      P.optimized.computeChallenge P.optimized.computePublic).trace 12 = _
    simp only [envOfTrace, dif_pos h12]
    rw [show (Qc ⟨12, h12⟩) = Nock.Framework.lastRowMask
      P.optimized.family.problem.cfg.compRows_pos P.optimized.computeNodes from h1,
      Nock.Framework.lastRowMask_eval _ _ hinj]

/-- **The accumulator starts at zero.**  For any accepted trace, the gathered role `32` at the
first row is `0`. -/
theorem acc_starts_at_zero (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    (rowEnv P Qc (firstRow P)).extTrace 32 = 0 := by
  have hgate := (row_obligations P Qc hsat (firstRow P)).endpointDegreeTwo2 _
    anchors_mem_endpoint2.1
  rw [accInit_eval, (masks_at_row P Qc hsat hax hbasis hwidth (firstRow P)).1] at hgate
  simpa using hgate

/-- The public `requests` gathered at a row is the package's `computePublic` block `6..8`. -/
theorem gathered_requests (Qc : Fin P.computeChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (rowEnv P Qc i).extensionPublic 2 =
      ∑ k : Fin 3, P.optimized.computePublic (6 + (k : ℕ)) • P.optimized.basis k := by
  simp only [rowEnv, gatherCorrectedFinalTypedEnv, envOfTrace]
  rfl

/-- **`acc_after` ends at `requests`.**  For any accepted trace, the gathered role `60` at the
last row is the gathered public `requests`. -/
theorem accAfter_ends_at_requests (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    (rowEnv P Qc (lastRow P)).extTrace 60 = (rowEnv P Qc (lastRow P)).extensionPublic 2 := by
  have hgate := (row_obligations P Qc hsat (lastRow P)).endpointDegreeTwo2 _
    anchors_mem_endpoint2.2
  rw [accTerminal_eval, (masks_at_row P Qc hsat hax hbasis hwidth (lastRow P)).2, if_pos rfl] at hgate
  simpa [sub_eq_zero] using hgate

/-- **The anchored step holds at every row**, the last included: the unmasked
`FoldedProgStep3` relation between `acc` (role `32`), `acc_after` (role `60`), the three
inactive-safe denominator witnesses (roles `33..35`) and the selector-derived activity masks. -/
theorem step_at_every_row (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    correctedAccAfterStep.eval (rowEnv P Qc i) = 0 := by
  have h := (row_obligations P Qc hsat i).residualAux3 2
  simpa [correctedAuxSemanticValue] using h

/-- **Off the last row `acc_after(i)` is the next row's accumulator.** -/
theorem chain_off_last_row (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (i : Fin P.optimized.family.problem.cfg.compRows)
    (hi : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows) :
    (rowEnv P Qc i).extTrace 60 = (rowEnv P Qc i).extTraceNext 32 := by
  have h := (row_obligations P Qc hsat i).extensionCore21 packedChainId
  have hnl : (rowEnv P Qc i).baseTrace 12 = 0 := by
    rw [(masks_at_row P Qc hsat hax hbasis hwidth i).2, if_neg]
    intro heq
    have hv : (i : ℕ) = P.optimized.family.problem.cfg.compRows - 1 := congrArg Fin.val heq
    omega
  simpa [correctedCoreSemanticValue, packedChainId, packedWalkCountId, packedWalkAccId,
    packedLnChainId, packedWalkLnId, accAfterChain, CorrectedFinalTypedExpr.eval, hnl,
    sub_eq_zero] using h

/-! ## C. The `Batch267` attack is rejected -/

/-- The three accumulator columns: role `32`, columns `109..111`. -/
def IsAccCol (i : ℕ) : Prop := 109 ≤ i ∧ i < 112

instance (i : ℕ) : Decidable (IsAccCol i) := by unfold IsAccCol; infer_instance

/-- `Q` with the constant `c k` added to column `109 + k` — `Batch267`'s `constShift`. -/
def bumpAcc (c : Fin 3 → F) {w : ℕ} (Q : Fin w → F[X]) : Fin w → F[X] :=
  fun col => if h : IsAccCol (col : ℕ) then
    Q col + Polynomial.C (c ⟨(col : ℕ) - 109, by unfold IsAccCol at h; omega⟩)
  else Q col

theorem bumpAcc_off (c : Fin 3 → F) {w : ℕ} (Q : Fin w → F[X]) (col : Fin w)
    (hc : ¬ IsAccCol (col : ℕ)) : bumpAcc c Q col = Q col := by
  simp [bumpAcc, hc]

theorem bumpAcc_acc (c : Fin 3 → F) {w : ℕ} (hw : 112 ≤ w) (Q : Fin w → F[X]) (k : Fin 3)
    (x : F) :
    (bumpAcc c Q ⟨109 + (k : ℕ), by omega⟩).eval x = (Q ⟨109 + (k : ℕ), by omega⟩).eval x + c k := by
  have hc : IsAccCol (109 + (k : ℕ)) := by unfold IsAccCol; omega
  simp only [bumpAcc, dif_pos hc, Polynomial.eval_add, Polynomial.eval_C]
  congr 2
  apply Fin.ext; simp

omit [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)] in
theorem gather_ne_zero (b : Basis (Fin 3) F K) (c : Fin 3 → F) (hc : c ≠ 0) :
    (∑ k, c k • b k) ≠ 0 := by
  intro h0
  apply hc
  funext k
  have := congrArg (fun x => coord b x k) h0
  simpa [coord_sum_smul, coord_zero] using this

/-- The bumped trace's gathered accumulator at any row is the original's plus `Σ c_k b_k`. -/
theorem bumped_acc (Qc : Fin P.computeChip.rap.w → F[X]) (c : Fin 3 → F)
    (i : Fin P.optimized.family.problem.cfg.compRows) :
    (rowEnv P (bumpAcc c Qc) i).extTrace 32 =
      (rowEnv P Qc i).extTrace 32 + ∑ k, c k • P.optimized.basis k := by
  simp only [rowEnv, gatherCorrectedFinalTypedEnv]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hw : 112 ≤ P.computeChip.rap.w := by change 112 ≤ 303; norm_num
  have hidx : correctedFinalExtCoordIndex (e := 3) (32 : Fin 63) k = 109 + (k : ℕ) := by
    simp [correctedFinalExtCoordIndex]
  have hlt : 109 + (k : ℕ) < P.computeChip.rap.w := by change _ < 303; omega
  rw [hidx]
  simp only [envOfTrace, dif_pos hlt]
  rw [bumpAcc_acc c hw Qc k, add_smul]

/-- **The constant shift of the accumulator is rejected.** -/
theorem moved_accumulator_rejected (Qc : Fin P.computeChip.rap.w → F[X])
    (hsat : RAP.SatisfiesWithPreprocessing P.computeChip Qc)
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F)
    (c : Fin 3 → F) (hc : c ≠ 0) :
    ¬ RAP.SatisfiesWithPreprocessing P.computeChip (bumpAcc c Qc) := by
  intro hsat'
  have h1 := acc_starts_at_zero P Qc hsat hax hbasis hwidth
  have h2 := acc_starts_at_zero P (bumpAcc c Qc) hsat' hax hbasis hwidth
  rw [bumped_acc, h1, zero_add] at h2
  exact gather_ne_zero P.optimized.basis c hc h2

/-- The honest trace is still accepted: the anchors are discharged by the package's
`computeRequestsPins` and the co-resident accumulator's own identities. -/
theorem canonical_trace_accepted [Fintype F] [DecidableEq F]
    (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : FormRBasis P.optimized.basis)
    (hwidth : FormRWidth F) :
    RAP.SatisfiesWithPreprocessing P.computeChip (canonicalComputeTrace P) :=
  canonicalComputeTrace_satisfies P hax hbasis hwidth

end Deployed

end

end Nock.RedTeam.Batch269

#print axioms Nock.RedTeam.Batch269.anchors_mem_endpoint2
#print axioms Nock.RedTeam.Batch269.acc_starts_at_zero
#print axioms Nock.RedTeam.Batch269.accAfter_ends_at_requests
#print axioms Nock.RedTeam.Batch269.step_at_every_row
#print axioms Nock.RedTeam.Batch269.chain_off_last_row
#print axioms Nock.RedTeam.Batch269.moved_accumulator_rejected
#print axioms Nock.RedTeam.Batch269.canonical_trace_accepted
