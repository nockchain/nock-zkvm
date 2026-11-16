import Mathlib.LinearAlgebra.Lagrange
import Nock.NockVMROM.Thm54.TemplateRawJointSoundness

/-!
# Template-fixed regenerated memory-walk counting

This file records why regenerated-memory counting is redundant on the topology-enabled production
path.  The memory labels come from the seed-fixed execution template and are specialized only at
`alphaM`.  The remaining `(alphaC, gamma)` choices are quantified in the failure predicate.
Outside the separately counted topology collision set, raw acceptance plus the compressed topology
check already proves the exact memory-forest relation, so the residual memory failure set is empty.
Accordingly this receipt is correspondence evidence only and contributes no production workload.

The coordinate receipt is nevertheless concrete.  Every one of the canonical `32` memory-label
coordinates is represented by its full-field Lagrange interpolant, with degree strictly below
`|K|`.  This uses neither a fixed-label substitution nor an independence assumption.
-/

open scoped BigOperators Classical

namespace Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting

open Nock Nock.Walk
open SemanticTimestampStrategy
open TemplateRawJointSoundness

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable {p : ℕ} [CharP K p]
variable [Fintype K] [DecidableEq K]

abbrev Strategy := TemplateRawJointSoundness.Strategy

/-- Reassemble the four public coins with the production chronology made explicit. -/
def coins (alphaC gamma alphaM z : K) : JointCoins K :=
  ((alphaC, gamma), (alphaM, z))

omit [Field K] [Fintype K] [DecidableEq K] in
@[simp] theorem coins_nprSeed (alphaC gamma alphaM z : K) :
    nprSeed (coins alphaC gamma alphaM z) = z :=
  rfl

omit [Field K] [Fintype K] [DecidableEq K] in
@[simp] theorem coins_alphaM (alphaC gamma alphaM z : K) :
    Thm54.alphaM (coins alphaC gamma alphaM z) = alphaM :=
  rfl

omit [Field K] [Fintype K] [DecidableEq K] in
@[simp] theorem coins_gamma (alphaC gamma alphaM z : K) :
    Thm54.gamma (coins alphaC gamma alphaM z) = gamma :=
  rfl

/-- The desired memory-forest label relation on the exact `(z, alphaM)` specialization.

This is a conclusion, not a verifier gate: no `RVT`, semantic target, or proof object is placed in
the raw message or in `AcceptsWithTopology`. -/
def MemoryForestLabelRelation
    (T : Strategy F K p) (z : K) (hz : z ≠ 0) (alphaM lmb : K) : Prop :=
  let problem := specializedProblem T.timestamp z hz alphaM lmb
  ∃ forest : List (NTree (MemoryTable.MState × MemoryTable.DTmem K)),
    forest = problem.exec.memoryForest ∧
      forest.length = problem.cfg.kMem ∧
      (∀ root ∈ forest,
        RVTWithArity (MemoryTable.Fmem (K := K)) root) ∧
      (bfsForest forest).map NTree.label = problem.exec.memoryRows

omit [Fintype K] [DecidableEq K] in
/-- Exact topology on the specialized authoritative forest supplies the literal recovered forest
and its aggregate BFS labels. -/
theorem memoryForestLabelRelation_of_exactTopology
    (T : Strategy F K p) (z : K) (hz : z ≠ 0) (alphaM lmb : K)
    (htop :
      MemoryExactTopology (specializedProblem T.timestamp z hz alphaM lmb).exec) :
    MemoryForestLabelRelation T z hz alphaM lmb := by
  let problem := specializedProblem T.timestamp z hz alphaM lmb
  refine ⟨problem.exec.memoryForest, rfl, problem.exec.memory_root_count, htop, ?_⟩
  rfl

/-- Exact residual memory-walk failure after separating the already-counted topology collision
fiber.  Both still-later choices are quantified. -/
def specializedMemoryWalkFails
    (T : Strategy F K p) (z : K) (hz : z ≠ 0) (alphaM lmb : K) : Prop :=
  ∃ alphaC gamma : K,
    T.AcceptsWithTopology (coins alphaC gamma alphaM z) lmb ∧
      gamma ∉ topologyBadGammas
        (T.afterAlphaM z hz alphaM lmb).familyData.base ∧
      ¬ MemoryForestLabelRelation T z hz alphaM lmb

theorem specializedMemoryWalkFails_iff
    (T : Strategy F K p) (z : K) (hz : z ≠ 0) (alphaM lmb : K) :
    specializedMemoryWalkFails T z hz alphaM lmb ↔
      ∃ alphaC gamma : K,
        T.AcceptsWithTopology (coins alphaC gamma alphaM z) lmb ∧
          gamma ∉ topologyBadGammas
            (T.afterAlphaM z hz alphaM lmb).familyData.base ∧
          ¬ MemoryForestLabelRelation T z hz alphaM lmb :=
  Iff.rfl

/-- Outside the separately counted compressed-topology collision fiber, the exact specialized
memory-walk failure predicate is impossible. -/
theorem not_specializedMemoryWalkFails
    (T : Strategy F K p) (hchar : NodeEncoding.StateTagChar K)
    (z : K) (hz : z ≠ 0) (alphaM lmb : K)
    (hlam : ∀ i,
      ((specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam) :
    ¬ specializedMemoryWalkFails T z hz alphaM lmb := by
  rintro ⟨alphaCValue, gammaValue, haccept, hgamma, hnotRelation⟩
  let ω := coins alphaCValue gammaValue alphaM z
  have hω : nprSeed ω ≠ 0 := by
    simpa [ω] using hz
  have hout : ω ∉ specializedTopologyFailureEvent T lmb := by
    intro hbad
    obtain ⟨hω', hbadGamma⟩ :=
      (mem_specializedTopologyFailureEvent_iff T lmb ω).1 hbad
    apply hgamma
    simpa [ω, proof_irrel_heq] using hbadGamma
  have htop :=
    T.exactTopology_of_acceptsWithTopology ω lmb hω hchar hlam haccept hout
  apply hnotRelation
  have hmemoryTop := htop.2
  change MemoryExactTopology
    (specializedProblem T.timestamp z hω alphaM lmb).exec at hmemoryTop
  exact memoryForestLabelRelation_of_exactTopology T z hz alphaM lmb
    (by simpa only [proof_irrel_heq] using hmemoryTop)

/-! ## Canonical 32-coordinate polynomial receipt -/

/-- The full-field interpolant of one canonical coordinate of one seed-fixed memory row. -/
def memoryCoordinatePolynomial
    (hchar : NodeEncoding.StateTagChar K)
    {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (lmb : K)
    (row : MemoryRowTemplate (K := K))
    (_hrow : row ∈ E.memoryRows)
    (j : Fin NodeEncoding.memoryNodeWidth) : Polynomial K :=
  Lagrange.interpolate (Finset.univ : Finset K) id
    (fun alphaM => NodeEncoding.memoryNodeEncode hchar (row.specialize alphaM lmb) j)

theorem memoryCoordinatePolynomial_eval
    (hchar : NodeEncoding.StateTagChar K)
    {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (lmb : K)
    (row : MemoryRowTemplate (K := K))
    (hrow : row ∈ E.memoryRows)
    (j : Fin NodeEncoding.memoryNodeWidth) (alphaM : K) :
    (memoryCoordinatePolynomial hchar E lmb row hrow j).eval alphaM =
      NodeEncoding.memoryNodeEncode hchar (row.specialize alphaM lmb) j := by
  unfold memoryCoordinatePolynomial
  exact Lagrange.eval_interpolate_at_node
    (fun alphaM => NodeEncoding.memoryNodeEncode hchar (row.specialize alphaM lmb) j)
    (by
      intro x _ y _ hxy
      exact hxy)
    (Finset.mem_univ alphaM)

/-- Every canonical coordinate interpolant has degree at most `|K| - 1`. -/
theorem memoryCoordinatePolynomial_degree
    (hchar : NodeEncoding.StateTagChar K)
    {T : ExactConfigTemplate F K}
    (E : ExactExecutionTemplate T) (lmb : K)
    (row : MemoryRowTemplate (K := K))
    (hrow : row ∈ E.memoryRows)
    (j : Fin NodeEncoding.memoryNodeWidth) :
    (memoryCoordinatePolynomial hchar E lmb row hrow j).natDegree ≤
      Fintype.card K - 1 := by
  let P := memoryCoordinatePolynomial hchar E lmb row hrow j
  change P.natDegree ≤ Fintype.card K - 1
  by_cases hP : P = 0
  · simp [P, hP]
  · have hdeg :
        P.natDegree < Fintype.card K :=
      (Polynomial.natDegree_lt_iff_degree_lt hP).2
        (Lagrange.degree_interpolate_lt (s := (Finset.univ : Finset K))
          (v := id)
          (r := fun alphaM =>
            NodeEncoding.memoryNodeEncode hchar (row.specialize alphaM lmb) j)
          (by
            intro x _ y _ hxy
            exact hxy))
    exact Nat.le_sub_one_of_lt hdeg

/-- Concrete regenerated-label receipt for one nonzero seed.  Its residual bad-alpha set is empty
because topology collisions were separated before defining `specializedMemoryWalkFails`. -/
def receipt
    (T : Strategy F K p) (lmb : K) (hchar : NodeEncoding.StateTagChar K)
    (z : K) (hz : z ≠ 0)
    (hlam : ∀ alphaM i,
      ((specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam) :
    RegeneratedMemoryLabelCountingObligation
      (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate hchar lmb
      (fun alphaM => specializedMemoryWalkFails T z hz alphaM lmb) where
  coordinateDegreeBound := Fintype.card K - 1
  coordinatePolynomial :=
    memoryCoordinatePolynomial hchar
      (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate lmb
  coordinatePolynomial_eval := by
    intro row hrow j alphaM
    exact memoryCoordinatePolynomial_eval hchar
      (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate lmb row hrow j alphaM
  coordinatePolynomial_degree := by
    intro row hrow j
    exact memoryCoordinatePolynomial_degree hchar
      (T.timestamp.afterSeed ⟨z, hz⟩).executionTemplate lmb row hrow j
  composedDegreeBound := 0
  badAlphas := ∅
  failure_mem_badAlphas := by
    intro alphaM hfail
    exact (not_specializedMemoryWalkFails T hchar z hz alphaM lmb (hlam alphaM) hfail).elim
  badAlphas_card := by simp

/-- The requested concrete strategy-wide counting data; no receipt is supplied as an input. -/
def countingData
    (T : Strategy F K p) (lmb : K) (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ z (hz : z ≠ 0) alphaM i,
      ((specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam) :
    RegeneratedMemoryCountingData T hchar lmb where
  fails := fun z hz alphaM => specializedMemoryWalkFails T z hz alphaM lmb
  receipt := fun z hz => receipt T lmb hchar z hz (hlam z hz)

@[simp] theorem countingData_fails
    (T : Strategy F K p) (lmb : K) (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ z (hz : z ≠ 0) alphaM i,
      ((specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam)
    (z : K) (hz : z ≠ 0) (alphaM : K) :
    (countingData T lmb hchar hlam).fails z hz alphaM ↔
      specializedMemoryWalkFails T z hz alphaM lmb :=
  Iff.rfl

@[simp] theorem receipt_badAlphas
    (T : Strategy F K p) (lmb : K) (hchar : NodeEncoding.StateTagChar K)
    (z : K) (hz : z ≠ 0)
    (hlam : ∀ alphaM i,
      ((specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam) :
    (receipt T lmb hchar z hz hlam).badAlphas = ∅ :=
  rfl

/-- The regenerated-memory event contributes zero workload once topology collisions are kept in
their own event. -/
theorem countingFailureEvent_card_le
    (T : Strategy F K p) (lmb : K) (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ z (hz : z ≠ 0) alphaM i,
      ((specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam) :
    (countingData T lmb hchar hlam).failureEvent.card ≤
      0 * Fintype.card K ^ 3 := by
  apply (countingData T lmb hchar hlam).failureEvent_card_le 0
  intro z hz
  rfl

/-! ## Combined exact event and outside-event recovery -/

/-- Explicit maximum specialized topology workload over all `(z, alphaM)` fibers. -/
def memoryWalkTopologyWorkload (T : Strategy F K p) : ℕ :=
  (Finset.univ : Finset (K × K × K)).sup fun za =>
    if hz : za.1 ≠ 0 then
      topologyWorkload (T.afterAlphaM za.1 hz za.2.1 za.2.2).familyData.base
    else 0

theorem topologyWorkload_le_memoryWalkTopologyWorkload
    (T : Strategy F K p) (z : K) (hz : z ≠ 0) (alphaM lmb : K) :
    topologyWorkload (T.afterAlphaM z hz alphaM lmb).familyData.base ≤
      memoryWalkTopologyWorkload T := by
  have hle := Finset.le_sup
    (f := fun za : K × K × K =>
      if hz' : za.1 ≠ 0 then
        topologyWorkload (T.afterAlphaM za.1 hz' za.2.1 za.2.2).familyData.base
      else 0)
    (Finset.mem_univ (z, alphaM, lmb))
  simpa [memoryWalkTopologyWorkload, hz, proof_irrel_heq] using hle

/-- The exact JointCoins event used by the final theorem. -/
def failureEvent
    (T : Strategy F K p) (lmb : K) (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ z (hz : z ≠ 0) alphaM i,
      ((specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam) :
    Finset (JointCoins K) :=
  (countingData T lmb hchar hlam).failureEvent ∪ specializedTopologyFailureEvent T lmb

/-- JointCoins cardinality is at most the explicit maximum workload times `|K|^3`. -/
theorem failureEvent_card_le
    (T : Strategy F K p) (lmb : K) (hchar : NodeEncoding.StateTagChar K)
    (hlam : ∀ z (hz : z ≠ 0) alphaM i,
      ((specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam) :
    (failureEvent T lmb hchar hlam).card ≤
      memoryWalkTopologyWorkload T * Fintype.card K ^ 3 := by
  have hmemory := countingFailureEvent_card_le T lmb hchar hlam
  have htopology :
      (specializedTopologyFailureEvent T lmb).card ≤
        memoryWalkTopologyWorkload T * Fintype.card K ^ 3 :=
    specializedTopologyFailureEvent_card_le T lmb (memoryWalkTopologyWorkload T)
      (fun z hz alphaM => topologyWorkload_le_memoryWalkTopologyWorkload T z hz alphaM lmb)
  calc
    (failureEvent T lmb hchar hlam).card ≤
        (countingData T lmb hchar hlam).failureEvent.card +
          (specializedTopologyFailureEvent T lmb).card := by
      exact Finset.card_union_le _ _
    _ ≤ 0 * Fintype.card K ^ 3 +
        memoryWalkTopologyWorkload T * Fintype.card K ^ 3 :=
      Nat.add_le_add hmemory htopology
    _ = memoryWalkTopologyWorkload T * Fintype.card K ^ 3 := by simp

/-- Outside the concrete event, raw memory-walk acceptance and the compressed topology check
recover the exact memory-forest label relation.  The theorem takes no receipt/counting structure,
fixed-label premise, independence premise, or target gate. -/
theorem memoryWalkCertificate_and_forestRelation_of_acceptsWithTopology
    (T : Strategy F K p) (hchar : NodeEncoding.StateTagChar K)
    (ω : JointCoins K) (lmb : K) (hz : nprSeed ω ≠ 0)
    (haccept : T.AcceptsWithTopology ω lmb)
    (hlam : ∀ i,
      ((specializedProblem T.timestamp (nprSeed ω) hz (Thm54.alphaM ω) lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp (nprSeed ω) hz (Thm54.alphaM ω) lmb).cfg.challenges.lam)
    (hlamAll : ∀ z (hz : z ≠ 0) alphaM i,
      ((specializedProblem T.timestamp z hz alphaM lmb).exec.memoryPubAt i).lambda = (specializedProblem T.timestamp z hz alphaM lmb).cfg.challenges.lam)
    (hout : ω ∉ failureEvent T lmb hchar hlamAll) :
    (T.messageAt ω lmb hz).MemoryWalkCertificate ∧
      MemoryForestLabelRelation T (nprSeed ω) hz (Thm54.alphaM ω) lmb := by
  have hparts := (T.acceptsWithTopology_iff_raw_checks ω lmb hz).1 haccept
  have hmemory :
      (T.messageAt ω lmb hz).MemoryWalkCertificate :=
    (T.messageAt ω lmb hz).memoryWalkRAP_wholeTrace_iff.mp hparts.2.1.2.2.2.1
  have houtTopology : ω ∉ specializedTopologyFailureEvent T lmb := by
    intro hbad
    exact hout (Finset.mem_union_right _ hbad)
  have htop :=
    T.exactTopology_of_acceptsWithTopology ω lmb hz hchar hlam haccept houtTopology
  refine ⟨hmemory, ?_⟩
  have hmemoryTop := htop.2
  change MemoryExactTopology
    (specializedProblem T.timestamp (nprSeed ω) hz (Thm54.alphaM ω) lmb).exec
      at hmemoryTop
  exact memoryForestLabelRelation_of_exactTopology T
    (nprSeed ω) hz (Thm54.alphaM ω) lmb hmemoryTop

end

end Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting

#print axioms Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting.not_specializedMemoryWalkFails
#print axioms Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting.memoryCoordinatePolynomial_eval
#print axioms Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting.memoryCoordinatePolynomial_degree
#print axioms Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting.receipt
#print axioms Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting.countingFailureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting.failureEvent_card_le
#print axioms Nock.NockVMROM.Thm54.TemplateMemoryWalkCounting.memoryWalkCertificate_and_forestRelation_of_acceptsWithTopology
