import Nock.NockVMROM.Thm54.SampledIOSameExecution
import Nock.NockVMROM.Thm54.MemoryMplus2L

/-!
# Sampled program-IO co-resident with compute rows

The program-side accumulator is updated once per compute row by the reciprocals of that row's
zero-to-three emitted request records.  Thus the sampled `requestInv` / `requestAcc` witness is
represented on the existing `N` compute rows; there is no appended record-indexed phase.

The sampled `gamma` and `pole` are read only from `FiniteIO.IOCoins`.  They are not the walk RLC
challenge and are not the RAP coset shift.
-/

namespace Nock.NockVMROM.Thm54
namespace ComputeSampledIO

open Nock
open scoped BigOperators

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]

def rowRequests (lam : K) (row : ComputeTable.State × ComputeTable.DTcomp K) :
    List (Fin 9 → K) :=
  (NockVM.activeRequestRecords row.2.2.1).map
    (fun r => NockVM.encRecFormR r lam)

/-- The sampled reciprocal attached to one emitted request. -/
def requestInv (coins : FiniteIO.IOCoins K) (v : Fin 9 → K) : K :=
  (FiniteIO.compress coins v)⁻¹

/-- One compute row's complete request-side log-derivative contribution. -/
def rowTerm (coins : FiniteIO.IOCoins K) (lam : K)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : K :=
  ((rowRequests lam row).map (requestInv coins)).sum

/-- Co-resident request accumulator at the boundary before row `i`. -/
def coResidentAcc (coins : FiniteIO.IOCoins K) (lam : K)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) (i : ℕ) : K :=
  ((rows.take i).map (rowTerm coins lam)).sum

omit [Fintype K] [DecidableEq K] in
@[simp] theorem coResidentAcc_zero (coins : FiniteIO.IOCoins K) (lam : K)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) :
    coResidentAcc coins lam rows 0 = 0 := by
  simp [coResidentAcc]

omit [Fintype K] [DecidableEq K] in
/-- A single local transition consumes all requests of the current opcode row. -/
theorem coResidentAcc_succ (coins : FiniteIO.IOCoins K) (lam : K)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K))
    {i : ℕ} (hi : i < rows.length) :
    coResidentAcc coins lam rows (i + 1) =
      coResidentAcc coins lam rows i + rowTerm coins lam rows[i] := by
  unfold coResidentAcc
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

omit [Fintype K] [DecidableEq K] in
/-- Row-wise accumulation is exactly accumulation over the flattened request list. -/
theorem sum_rowTerm_eq_flattened (coins : FiniteIO.IOCoins K) (lam : K)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) :
    (rows.map (rowTerm coins lam)).sum =
      (((rows.flatMap (rowRequests lam)).map (requestInv coins)).sum) := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp [rowTerm, rowRequests, ih, List.map_append, List.sum_append]

omit [Fintype K] [DecidableEq K] in
/-- The terminal co-resident value is the reciprocal sum over the execution's exact derived
request records. -/
theorem coResidentAcc_last {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (coins : FiniteIO.IOCoins K) :
    coResidentAcc coins cfg.challenges.lam exec.computeRows exec.computeRows.length =
      ((exec.derivedRequestIO.map (requestInv coins)).sum) := by
  unfold coResidentAcc
  rw [List.take_of_length_le (le_refl _), sum_rowTerm_eq_flattened]
  simp [rowRequests, ExactExecution.derivedRequestIO, ExactExecution.rawRequests,
    List.map_flatMap, List.map_map, Function.comp_def]

/-- Every row-local emitted request is one of the exact sampled request records. -/
theorem rowRequest_mem_sampled
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hrow : row ∈ R.problem.exec.computeRows)
    {v : Fin 9 → K} (hv : v ∈ rowRequests R.problem.cfg.challenges.lam row) :
    v ∈ A.sampled.records.requests := by
  rw [A.requests_eq, R.problem.exec.derivedRequestIO_eq_computeRows]
  simp only [rowRequests, List.mem_map] at hv
  obtain ⟨mr, hmr, rfl⟩ := hv
  rw [List.mem_map]
  exact ⟨mr, List.mem_flatMap.mpr ⟨row, hrow, hmr⟩, rfl⟩

/-- The explicit bad-pole exclusion makes every row-local reciprocal genuine. -/
theorem requestInv_pin
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (hrow : row ∈ R.problem.exec.computeRows)
    {v : Fin 9 → K} (hv : v ∈ rowRequests R.problem.cfg.challenges.lam row) :
    FiniteIO.compress A.sampled.coins v *
        requestInv A.sampled.coins v = 1 := by
  apply mul_inv_cancel₀
  intro hzero
  exact A.poleHitGood (by
    simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨v, List.mem_append_left _ (rowRequest_mem_sampled A hrow hv), hzero⟩)

/-- The co-resident terminal is exactly the accepted sampled witness's final request accumulator. -/
theorem coResidentAcc_terminal_eq_witness
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p) :
    coResidentAcc A.sampled.coins R.problem.cfg.challenges.lam R.problem.exec.computeRows
        R.problem.exec.computeRows.length =
      A.sampled.witness.requestAcc (Fin.last _) := by
  rw [coResidentAcc_last R.problem.exec A.sampled.coins]
  rw [← A.requests_eq]
  rw [← FiniteIO.sum_fin_get A.sampled.records.requests
    (fun v => requestInv A.sampled.coins v)]
  calc
    (∑ i, requestInv A.sampled.coins (A.sampled.records.requests.get i))
        = ∑ i, A.sampled.witness.requestInv i := by
            exact Finset.sum_congr rfl (fun i _ =>
              (FiniteIO.requestInv_eq A.sampled.accepts i).symm)
    _ = A.sampled.witness.terminal := (FiniteIO.requestAcc_last A.sampled.accepts).symm
    _ = A.sampled.witness.requestAcc (Fin.last _) := A.sampled.accepts.requestTerm.symm

/-- No appended program-IO phase: all inverse pins and accumulator updates occur on the exact
compute rows and the accepted terminal is reached at row boundary `N`. -/
structure NoAppendedComputeIOPhase
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p) : Prop where
  /-- The active compute prefix fits the exact orbit capacity. -/
  capacity : R.problem.cfg.compRows ≤ 2 ^ R.problem.cfg.orbit.h
  /-- Sampled records are the execution-derived request/response records. -/
  sameRequests : A.sampled.records.requests = R.problem.exec.derivedRequestIO
  sameResponses : A.sampled.records.responses = R.problem.exec.derivedResponseIO
  /-- Initial empty accumulator. -/
  init :
    coResidentAcc A.sampled.coins R.problem.cfg.challenges.lam R.problem.exec.computeRows 0 = 0
  /-- One row-local transition per exact compute row. -/
  rowLocal : ∀ i, ∀ hi : i < R.problem.exec.computeRows.length,
    coResidentAcc A.sampled.coins R.problem.cfg.challenges.lam R.problem.exec.computeRows (i + 1) =
      coResidentAcc A.sampled.coins R.problem.cfg.challenges.lam R.problem.exec.computeRows i +
        rowTerm A.sampled.coins R.problem.cfg.challenges.lam R.problem.exec.computeRows[i]
  inversePins :
    ∀ row ∈ R.problem.exec.computeRows, ∀ v ∈ rowRequests R.problem.cfg.challenges.lam row,
      FiniteIO.compress A.sampled.coins v * requestInv A.sampled.coins v = 1
  /-- The final compute-row boundary is already the finite-IO terminal. -/
  terminalOnTable :
    coResidentAcc A.sampled.coins R.problem.cfg.challenges.lam R.problem.exec.computeRows
        R.problem.exec.computeRows.length =
      A.sampled.witness.requestAcc (Fin.last _)

/-- Construct co-residence from the exact capacity premise and sampled same-execution assignment. -/
theorem noAppendedComputeIOPhase
    {R : PlusIOSegmentedFamily F K}
    (A : SampledIOSameExecutionAssignment R p)
    (hcap : R.problem.cfg.compRows ≤ 2 ^ R.problem.cfg.orbit.h) :
    NoAppendedComputeIOPhase A where
  capacity := hcap
  sameRequests := A.requests_eq
  sameResponses := A.responses_eq
  init := coResidentAcc_zero _ _ _
  rowLocal := fun _ hi => coResidentAcc_succ _ _ _ hi
  inversePins := fun _row hrow _v hv => requestInv_pin A hrow hv
  terminalOnTable := coResidentAcc_terminal_eq_witness A

omit [Fintype K] [DecidableEq K] in
/-- A wrong reciprocal is rejected by the sampled inverse equation. -/
theorem wrong_inverse_rejected (coins : FiniteIO.IOCoins K) (v : Fin 9 → K) (bad : K)
    (hden : FiniteIO.compress coins v ≠ 0)
    (hbad : bad ≠ requestInv coins v) :
    FiniteIO.compress coins v * bad ≠ 1 := by
  intro h
  apply hbad
  exact mul_left_cancel₀ hden
    (h.trans (mul_inv_cancel₀ hden).symm)

omit [Fintype K] [DecidableEq K] in
/-- A malformed accumulator step is rejected by the exact row transition equation. -/
theorem wrong_step_rejected (acc accNext contribution : K)
    (hbad : accNext ≠ acc + contribution) :
    accNext - acc - contribution ≠ 0 := by
  intro h
  apply hbad
  rw [sub_sub, sub_eq_zero] at h
  exact h

omit [Fintype K] [DecidableEq K] in
/-- A malformed terminal is rejected by endpoint equality. -/
theorem wrong_terminal_rejected (acc terminal : K) (hbad : acc ≠ terminal) :
    terminal - acc ≠ 0 := by
  intro h
  exact hbad (sub_eq_zero.mp h).symm

/-! The honest ten-slot records are `RecordCarrier.extRec L` of the nine-slot ones, so the honest
accumulator compresses with `fun v => compress coins (extRec L v)`.  The definitions below are the
ones above with `compress coins` abstracted to `comp`. -/

/-- One compute row's request-side contribution at the compression `comp`. -/
def rowTermC (comp : (Fin 9 → K) → K) (lam : K)
    (row : ComputeTable.State × ComputeTable.DTcomp K) : K :=
  ((rowRequests lam row).map (fun v => (comp v)⁻¹)).sum

/-- The co-resident request accumulator at the compression `comp`. -/
def coResidentAccC (comp : (Fin 9 → K) → K) (lam : K)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) (i : ℕ) : K :=
  ((rows.take i).map (rowTermC comp lam)).sum

omit [Fintype K] [DecidableEq K] in
@[simp] theorem coResidentAccC_zero (comp : (Fin 9 → K) → K) (lam : K)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) :
    coResidentAccC comp lam rows 0 = 0 := by
  simp [coResidentAccC]

omit [Fintype K] [DecidableEq K] in
theorem coResidentAccC_succ (comp : (Fin 9 → K) → K) (lam : K)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K))
    {i : ℕ} (hi : i < rows.length) :
    coResidentAccC comp lam rows (i + 1) =
      coResidentAccC comp lam rows i + rowTermC comp lam rows[i] := by
  unfold coResidentAccC
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList_some, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

omit [Fintype K] [DecidableEq K] in
theorem sum_rowTermC_eq_flattened (comp : (Fin 9 → K) → K) (lam : K)
    (rows : List (ComputeTable.State × ComputeTable.DTcomp K)) :
    (rows.map (rowTermC comp lam)).sum =
      (((rows.flatMap (rowRequests lam)).map (fun v => (comp v)⁻¹)).sum) := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
      simp [rowTermC, rowRequests, ih, List.map_append, List.sum_append]

omit [Fintype K] [DecidableEq K] in
theorem coResidentAccC_last {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (comp : (Fin 9 → K) → K) :
    coResidentAccC comp cfg.challenges.lam exec.computeRows exec.computeRows.length =
      ((exec.derivedRequestIO.map (fun v => (comp v)⁻¹)).sum) := by
  unfold coResidentAccC
  rw [List.take_of_length_le (le_refl _), sum_rowTermC_eq_flattened]
  simp [rowRequests, ExactExecution.derivedRequestIO, ExactExecution.rawRequests,
    List.map_flatMap, List.map_map, Function.comp_def]

omit [Fintype K] [DecidableEq K] in
/-- The terminal at the compression `compress coins ∘ f` is the request accumulator of any
accepted witness over the records `derivedRequestIO.map f`. -/
theorem coResidentAccC_terminal_eq_requestAcc {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) {m : ℕ} {coins : FiniteIO.IOCoins K}
    {records : FiniteIO.PreChallengeRecords K m}
    {w : FiniteIO.PostChallengeIOWitness records coins}
    (hacc : FiniteIO.FiniteIOAccepts records coins w)
    (f : (Fin 9 → K) → (Fin m → K))
    (hrec : records.requests = exec.derivedRequestIO.map f) :
    coResidentAccC (fun v => FiniteIO.compress coins (f v)) cfg.challenges.lam
        exec.computeRows exec.computeRows.length =
      w.requestAcc (Fin.last _) := by
  rw [coResidentAccC_last exec]
  have hsum : (exec.derivedRequestIO.map (fun v => (FiniteIO.compress coins (f v))⁻¹)).sum
      = (records.requests.map (fun v => (FiniteIO.compress coins v)⁻¹)).sum := by
    rw [hrec, List.map_map]; rfl
  rw [hsum, ← FiniteIO.sum_fin_get records.requests (fun v => (FiniteIO.compress coins v)⁻¹)]
  calc
    (∑ i, (FiniteIO.compress coins (records.requests.get i))⁻¹)
        = ∑ i, w.requestInv i := by
            exact Finset.sum_congr rfl (fun i _ => (FiniteIO.requestInv_eq hacc i).symm)
    _ = w.terminal := (FiniteIO.requestAcc_last hacc).symm
    _ = w.requestAcc (Fin.last _) := hacc.requestTerm.symm

#print axioms coResidentAcc_succ
#print axioms sum_rowTerm_eq_flattened
#print axioms requestInv_pin
#print axioms coResidentAcc_terminal_eq_witness
#print axioms noAppendedComputeIOPhase
#print axioms wrong_inverse_rejected
#print axioms wrong_step_rejected
#print axioms wrong_terminal_rejected

end
end ComputeSampledIO
end Nock.NockVMROM.Thm54
