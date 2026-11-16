import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.TraceEncoding

/-!
# Exact chained Theorem 5.4 execution language
-/

namespace Nock.NockVMROM.Thm54

open scoped Classical
open Nock.Reified

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

namespace ExactExecution

/-! ## Canonical indexed access to the derived BFS rows -/

/-- The canonical compute row at an active index.  This is `List.get` on `computeRows`, transported
along the carrier's proved length equality; no row function is stored in `ExactExecution`. -/
def computeRowAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin cfg.compRows) : ComputeTable.State × ComputeTable.DTcomp K :=
  exec.computeRows.get (Fin.cast exec.computeRows_length.symm i)

/-- The canonical memory row at an active index.  This is `List.get` on `memoryRows`, transported
along the carrier's proved length equality; no row function is stored in `ExactExecution`. -/
def memoryRowAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin cfg.memRows) : MemoryTable.MState × MemoryTable.DTmem K :=
  exec.memoryRows.get (Fin.cast exec.memoryRows_length.symm i)

/-- Every canonical indexed compute row belongs to the authoritative derived BFS list. -/
theorem computeRowAt_mem {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin cfg.compRows) :
    exec.computeRowAt i ∈ exec.computeRows :=
  List.get_mem _ _

/-- Every canonical indexed memory row belongs to the authoritative derived BFS list. -/
theorem memoryRowAt_mem {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin cfg.memRows) :
    exec.memoryRowAt i ∈ exec.memoryRows :=
  List.get_mem _ _

/-- Reading through the configured-length cast gives the same compute-row value as `List.get`. -/
@[simp]
theorem computeRowAt_cast {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin exec.computeRows.length) :
    exec.computeRowAt (Fin.cast exec.computeRows_length i) = exec.computeRows.get i := by
  simp [computeRowAt]

/-- Reading through the configured-length cast gives the same memory-row value as `List.get`. -/
@[simp]
theorem memoryRowAt_cast {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin exec.memoryRows.length) :
    exec.memoryRowAt (Fin.cast exec.memoryRows_length i) = exec.memoryRows.get i := by
  simp [memoryRowAt]

/-- The indexed compute accessor reconstructs exactly the authoritative derived BFS list. -/
theorem computeRows_eq_ofFn_computeRowAt {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    exec.computeRows = List.ofFn exec.computeRowAt := by
  apply List.ext_get
  · simp
  · intro n hleft hright
    simp [computeRowAt]

/-- The indexed memory accessor reconstructs exactly the authoritative derived BFS list. -/
theorem memoryRows_eq_ofFn_memoryRowAt {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) :
    exec.memoryRows = List.ofFn exec.memoryRowAt := by
  apply List.ext_get
  · simp
  · intro n hleft hright
    simp [memoryRowAt]

/-! ## Table projections from the exact indexed rows -/

/-- The compute public row projected from the canonical indexed compute row. -/
def computePubAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin cfg.compRows) : ComputeTable.Pub K :=
  (exec.computeRowAt i).2.2.1

/-- The compute decomposition row projected from the canonical indexed compute row. -/
def computeDecAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin cfg.compRows) : ComputeTable.Dec K :=
  (exec.computeRowAt i).2.2.2

/-- The memory public row projected from the canonical indexed memory row. -/
def memoryPubAt {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (i : Fin cfg.memRows) : MemoryTable.Pub K :=
  (exec.memoryRowAt i).2.2

theorem computeRowAt_accepted {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : exec.ComputeRowsAccepted) (i : Fin cfg.compRows) :
    ComputeRowAccepted cfg (exec.computeRowAt i) :=
  (computeRowsAccepted_iff exec).1 h _ (exec.computeRowAt_mem i)

/-- Every row stores the same `lambda?` (e.g. the package `λ` written by specialization). -/
theorem memory_same_lambda_of_const {cfg : ExactConfig F K}
    (exec : ExactExecution cfg) (l : Option K)
    (hlam : ∀ i, (exec.memoryPubAt i).lambda? = l) :
    ∀ i, (exec.memoryPubAt i).lambda =
      (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).lambda := by
  intro i
  simp [MemoryTable.Pub.lambda, hlam i, hlam ⟨0, cfg.memRows_pos⟩]

/-- Rows that leave form-R `λ` unset (`none`, hence the default) agree with each other. -/
theorem memory_same_lambda_rfl {cfg : ExactConfig F K}
    (exec : ExactExecution cfg)
    (hlam : ∀ i, (exec.memoryPubAt i).lambda? = none) :
    ∀ i, (exec.memoryPubAt i).lambda =
      (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).lambda := by
  intro i
  simp [MemoryTable.Pub.lambda, hlam i, hlam ⟨0, cfg.memRows_pos⟩]

theorem memory_same_lambda_of_all_one {cfg : ExactConfig F K}
    (exec : ExactExecution cfg)
    (h : ∀ i, (exec.memoryPubAt i).lambda = 1) :
    ∀ i, (exec.memoryPubAt i).lambda =
      (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).lambda :=
  fun i => (h i).trans (h ⟨0, cfg.memRows_pos⟩).symm

theorem memoryRowAt_accepted {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : exec.MemoryRowsAccepted) (i : Fin cfg.memRows) :
    MemoryRowAccepted cfg (exec.memoryRowAt i) :=
  (memoryRowsAccepted_iff exec).1 h _ (exec.memoryRowAt_mem i)

end ExactExecution

namespace SemanticExactLanguage

theorem computeVcompAt {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : SemanticExactLanguage cfg exec) (i : Fin cfg.compRows) :
    ComputeTable.Vcomp cfg.challenges.computeInputs
      (exec.computePubAt i) (exec.computeDecAt i) := by
  have hr := ExactExecution.computeRowAt_accepted h.1 i
  have hv := hr.2.2
  rw [hr.2.1] at hv
  exact hv

theorem memoryVmemAt {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : SemanticExactLanguage cfg exec) (i : Fin cfg.memRows) :
    MemoryTable.Vmem cfg.challenges.memoryInputs (exec.memoryPubAt i) := by
  have hr := ExactExecution.memoryRowAt_accepted h.2.1 i
  have hv := hr.2.2.1
  rw [hr.2.1] at hv
  exact hv

end SemanticExactLanguage


/-- Every row expression is a projection of the unique canonical
indexed BFS rows of `exec`; there are no free row lists or row predicates. -/
structure ChainedSemanticExactLanguage (cfg : ExactConfig F K)
    (exec : ExactExecution cfg) : Prop where
  semantic : SemanticExactLanguage cfg exec
  /-- NPR's shared seed is nonzero, as required by the compute and memory reifiers. -/
  z_ne_zero : cfg.challenges.z ≠ 0
  /-- Compute genericity holds on every exact indexed row. -/
  compute_wf :
    ∀ i, ComputeTable.WF cfg.challenges.computeInputs (exec.computePubAt i)
  /-- Memory LogUp genericity holds on every exact indexed row. -/
  memory_wf :
    ∀ i, MemoryTable.WF cfg.challenges.memoryInputs (exec.memoryPubAt i)
  /-- Adjacent compute rows hand off the line accumulator. -/
  compute_chain :
    ∀ i : Fin cfg.compRows, ∀ hi : (i : ℕ) + 1 < cfg.compRows,
      (exec.computePubAt i).ln =
        (exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev
  /-- Adjacent memory rows hand off the LogUp accumulator. -/
  memory_chain :
    ∀ i : Fin cfg.memRows, ∀ hi : (i : ℕ) + 1 < cfg.memRows,
      (exec.memoryPubAt i).icur =
        (exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre
  /-- The first memory row starts with zero axis counts. -/
  memory_first_counts :
    (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).pt.counts = 0
  /-- The first memory row starts with zero axis indicator. -/
  memory_first_indicator :
    (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).pt.indicator = 0
  /-- The first memory row starts with zero prior LogUp accumulator. -/
  memory_first_ipre :
    (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).ipre = 0
  /-- The last memory row closes the LogUp accumulator. -/
  memory_last_icur :
    (exec.memoryPubAt
      (cfg.orbit.lastIndex cfg.memRows cfg.memRows_pos)).icur = 0
  /-- Form R `λ` is a sampled coin, copied onto every memory row (`Pub.lambda`).
      RAP `Satisfies` uses one global `chalVal`, so the copies agree. -/
  memory_same_lambda :
    ∀ i, (exec.memoryPubAt i).lambda =
      (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).lambda

/-- A proof-carrying member of the stronger exact chained execution language. -/
abbrev ChainedAcceptedExecution (cfg : ExactConfig F K) :=
  { exec : ExactExecution cfg // ChainedSemanticExactLanguage cfg exec }

/-! ## Exact segmented-RAP satisfaction attached to an execution -/

/-- One compute auxiliary family makes all four ordinary compute RAP kinds hold on the exact
configuration, exact domains, exact node map, and canonical indexed execution rows. -/
def ComputeExecutionSegmentedRAPSatisfies (cfg : ExactConfig F K)
    (exec : ExactExecution cfg) : Prop :=
  ∃ ex : Fin cfg.compRows → ComputeTable.Extra K,
    ComputeSegmentedRAPSatisfies cfg
      (encodeComputeTrace
        (fun i => computeEnvFull cfg.challenges.computeInputs
          (ComputeTable.opSel (exec.computePubAt i).state)
          (exec.computePubAt i) (exec.computeDecAt i) (ex i))
        cfg.compNodes)

/-- One memory LogUp-witness family makes all four ordinary memory RAP kinds hold on the exact
configuration, exact domains, exact node map, and canonical indexed execution rows. -/
def MemoryExecutionSegmentedRAPSatisfies (cfg : ExactConfig F K)
    (exec : ExactExecution cfg) : Prop :=
  ∃ g : Fin cfg.memRows → K,
    MemorySegmentedRAPSatisfies cfg
      (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).lambda
      (encodeMemoryTrace
        (fun i => memoryEnvFull cfg.challenges.memoryInputs
          (MemoryTable.opSel (exec.memoryPubAt i).st)
          (exec.memoryPubAt i) (g i))
        cfg.memNodes)

/-- A chained accepted execution produces one shared compute auxiliary family satisfying all four
ordinary compute RAPs on the exact segmented domains. -/
theorem ChainedSemanticExactLanguage.computeSegmentedRAP
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    ComputeExecutionSegmentedRAPSatisfies cfg exec := by
  unfold ComputeExecutionSegmentedRAPSatisfies
  exact
    (computeSegmentedRAP_wholeTrace_iff cfg exec.computePubAt exec.computeDecAt
      h.compute_wf h.z_ne_zero).2
        ⟨h.semantic.computeVcompAt, h.compute_chain⟩

/-- A chained accepted execution produces one shared memory LogUp-witness family satisfying all
four ordinary memory RAPs on the exact segmented domains. -/
theorem ChainedSemanticExactLanguage.memorySegmentedRAP
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    MemoryExecutionSegmentedRAPSatisfies cfg exec := by
  unfold MemoryExecutionSegmentedRAPSatisfies
  exact
    (memorySegmentedRAP_wholeTrace_iff cfg exec.memoryPubAt
      h.memory_wf h.z_ne_zero h.memory_same_lambda).2
        ⟨h.semantic.memoryVmemAt, h.memory_chain,
          h.memory_first_counts, h.memory_first_indicator,
          h.memory_first_ipre, h.memory_last_icur⟩

/-- Both exact whole-trace adapters, with one auxiliary family per table and all four ordinary RAP
kinds per family. -/
theorem ChainedSemanticExactLanguage.segmentedRAP
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    ComputeExecutionSegmentedRAPSatisfies cfg exec ∧
      MemoryExecutionSegmentedRAPSatisfies cfg exec :=
  ⟨h.computeSegmentedRAP, h.memorySegmentedRAP⟩

theorem chainedSemanticExactLanguage_of_segmentedRAP
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hsemantic : SemanticExactLanguage cfg exec)
    (hz : cfg.challenges.z ≠ 0)
    (hcomputeWF :
      ∀ i, ComputeTable.WF cfg.challenges.computeInputs (exec.computePubAt i))
    (hmemoryWF :
      ∀ i, MemoryTable.WF cfg.challenges.memoryInputs (exec.memoryPubAt i))
    (hlambda :
      ∀ i, (exec.memoryPubAt i).lambda =
        (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).lambda)
    (hcompute : ComputeExecutionSegmentedRAPSatisfies cfg exec)
    (hmemory : MemoryExecutionSegmentedRAPSatisfies cfg exec) :
    ChainedSemanticExactLanguage cfg exec := by
  unfold ComputeExecutionSegmentedRAPSatisfies at hcompute
  unfold MemoryExecutionSegmentedRAPSatisfies at hmemory
  obtain ⟨_, hcomputeChain⟩ :=
    (computeSegmentedRAP_wholeTrace_iff cfg exec.computePubAt exec.computeDecAt
      hcomputeWF hz).1 hcompute
  obtain ⟨_, hmemoryChain, hcounts, hindicator, hipre, hicur⟩ :=
    (memorySegmentedRAP_wholeTrace_iff cfg exec.memoryPubAt
      hmemoryWF hz hlambda).1 hmemory
  exact
    { semantic := hsemantic
      z_ne_zero := hz
      compute_wf := hcomputeWF
      memory_wf := hmemoryWF
      compute_chain := hcomputeChain
      memory_chain := hmemoryChain
      memory_first_counts := hcounts
      memory_first_indicator := hindicator
      memory_first_ipre := hipre
      memory_last_icur := hicur
      memory_same_lambda := hlambda }

theorem chainedSemanticExactLanguage_iff_segmentedRAP
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hsemantic : SemanticExactLanguage cfg exec)
    (hz : cfg.challenges.z ≠ 0)
    (hcomputeWF :
      ∀ i, ComputeTable.WF cfg.challenges.computeInputs (exec.computePubAt i))
    (hmemoryWF :
      ∀ i, MemoryTable.WF cfg.challenges.memoryInputs (exec.memoryPubAt i)) :
    ChainedSemanticExactLanguage cfg exec ↔
      (∀ i, (exec.memoryPubAt i).lambda =
          (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).lambda) ∧
      ComputeExecutionSegmentedRAPSatisfies cfg exec ∧
        MemoryExecutionSegmentedRAPSatisfies cfg exec := by
  constructor
  · intro h
    exact ⟨h.memory_same_lambda, h.computeSegmentedRAP, h.memorySegmentedRAP⟩
  · rintro ⟨hlambda, hcompute, hmemory⟩
    exact chainedSemanticExactLanguage_of_segmentedRAP
      hsemantic hz hcomputeWF hmemoryWF hlambda hcompute hmemory


/-- A concrete failed compute handoff is incompatible with the stronger language. -/
theorem semanticExactLanguage_and_not_chained_of_compute_chain_failure
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hsemantic : SemanticExactLanguage cfg exec)
    (i : Fin cfg.compRows) (hi : (i : ℕ) + 1 < cfg.compRows)
    (hfail :
      (exec.computePubAt i).ln ≠
        (exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev) :
    SemanticExactLanguage cfg exec ∧
      ¬ ChainedSemanticExactLanguage cfg exec :=
  ⟨hsemantic, fun h => hfail (h.compute_chain i hi)⟩

/-- A concrete failed memory handoff is incompatible with the stronger language.  The theorem does
not assume the missing chain equation; it turns its failure into a rejection certificate. -/
theorem semanticExactLanguage_and_not_chained_of_memory_chain_failure
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (hsemantic : SemanticExactLanguage cfg exec)
    (i : Fin cfg.memRows) (hi : (i : ℕ) + 1 < cfg.memRows)
    (hfail :
      (exec.memoryPubAt i).icur ≠
        (exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre) :
    SemanticExactLanguage cfg exec ∧
      ¬ ChainedSemanticExactLanguage cfg exec :=
  ⟨hsemantic, fun h => hfail (h.memory_chain i hi)⟩

/-- Chained accepted executions have no hidden row, IO, auxiliary, or chain payload: equality of
the exact forest-first carriers determines the proof-carrying subtype. -/
theorem ChainedAcceptedExecution.ext
    {cfg : ExactConfig F K} (x y : ChainedAcceptedExecution cfg)
    (hcompute : x.1.computeTree = y.1.computeTree)
    (hmemory : x.1.memoryForest = y.1.memoryForest) :
    x = y := by
  apply Subtype.ext
  exact ExactExecution.ext x.1 y.1 hcompute hmemory

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.ExactExecution.computeRows_eq_ofFn_computeRowAt
#print axioms Nock.NockVMROM.Thm54.ExactExecution.memoryRows_eq_ofFn_memoryRowAt
#print axioms Nock.NockVMROM.Thm54.SemanticExactLanguage.computeVcompAt
#print axioms Nock.NockVMROM.Thm54.SemanticExactLanguage.memoryVmemAt
#print axioms Nock.NockVMROM.Thm54.ChainedSemanticExactLanguage.segmentedRAP
#print axioms Nock.NockVMROM.Thm54.chainedSemanticExactLanguage_of_segmentedRAP
#print axioms Nock.NockVMROM.Thm54.chainedSemanticExactLanguage_iff_segmentedRAP
#print axioms Nock.NockVMROM.Thm54.semanticExactLanguage_and_not_chained_of_compute_chain_failure
#print axioms Nock.NockVMROM.Thm54.semanticExactLanguage_and_not_chained_of_memory_chain_failure
#print axioms Nock.NockVMROM.Thm54.ChainedAcceptedExecution.ext
