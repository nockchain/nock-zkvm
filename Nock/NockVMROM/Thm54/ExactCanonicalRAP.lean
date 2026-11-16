import Nock.NockVMROM.Thm54.CanonicalRAP
import Nock.NockVMROM.Thm54.ChainedLanguage

/-!
The compute and memory sides therefore cannot silently select different configurations or
different executions.

The accepted predicates below are only the explicit table-row, adjacency, and memory-endpoint
predicates characterized by the chained AIRs.  They are not free class fields, and they do not
duplicate `SemanticExactLanguage`'s semantic IO predicate.

This remains the table-chained, segmented, **minus-IO** layer: its trace widths are 94 and 36.
It does not assemble the paper's named `+IO` 199/196-column composition and exposes no final
Theorem 5.4 alias.
-/

namespace Nock.NockVMROM.Thm54

open Classical
open Nock Framework Framework.Reify Framework.Thm54
open Nock.Reified
open scoped Polynomial

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The precise external problem index used on both sides of the exact canonical-RAP instance.

The proof fields are exactly the common nonzero NPR seed and the per-table genericity assumptions
required by `computeSegmentedRAP_wholeTrace_iff` and
`memorySegmentedRAP_wholeTrace_iff`.  All acceptance-bearing data remain projections of `exec`.
-/
structure ExactCanonicalRAPProblem (F K : Type) [Field F] [Field K] [Algebra F K] where
  cfg : ExactConfig F K
  exec : ExactExecution cfg
  z_ne_zero : cfg.challenges.z ≠ 0
  compute_wf :
    ∀ i, ComputeTable.WF cfg.challenges.computeInputs (exec.computePubAt i)
  memory_wf :
    ∀ i, MemoryTable.WF cfg.challenges.memoryInputs (exec.memoryPubAt i)
  memory_same_lambda :
    ∀ i, (exec.memoryPubAt i).lambda =
      (exec.memoryPubAt ⟨0, cfg.memRows_pos⟩).lambda

namespace ExactCanonicalRAPProblem

def ofChained {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    ExactCanonicalRAPProblem F K where
  cfg := cfg
  exec := exec
  z_ne_zero := h.z_ne_zero
  compute_wf := h.compute_wf
  memory_wf := h.memory_wf
  memory_same_lambda := h.memory_same_lambda

end ExactCanonicalRAPProblem

/-! ## Fixed acceptance, parameter, auxiliary, and encoder indices -/

/-- The explicit compute predicates characterized by the exact chained compute AIR:
all canonical rows satisfy `Vcomp`, and adjacent rows hand off `ln`. -/
def exactComputeChainedAccepts (p : ExactCanonicalRAPProblem F K) : Prop :=
  (∀ i, ComputeTable.Vcomp p.cfg.challenges.computeInputs
      (p.exec.computePubAt i) (p.exec.computeDecAt i)) ∧
    ∀ i : Fin p.cfg.compRows, ∀ hi : (i : ℕ) + 1 < p.cfg.compRows,
      (p.exec.computePubAt i).ln =
        (p.exec.computePubAt ⟨(i : ℕ) + 1, hi⟩).ln_prev

/-- The explicit memory predicates characterized by the exact chained memory AIR:
all canonical rows satisfy `Vmem`, adjacent rows hand off `icur`, and the canonical first/last
rows obey the three initial conditions and one terminal condition. -/
def exactMemoryChainedAccepts (p : ExactCanonicalRAPProblem F K) : Prop :=
  (∀ i, MemoryTable.Vmem p.cfg.challenges.memoryInputs
      (p.exec.memoryPubAt i)) ∧
    (∀ i : Fin p.cfg.memRows, ∀ hi : (i : ℕ) + 1 < p.cfg.memRows,
      (p.exec.memoryPubAt i).icur =
        (p.exec.memoryPubAt ⟨(i : ℕ) + 1, hi⟩).ipre) ∧
    (p.exec.memoryPubAt ⟨0, p.cfg.memRows_pos⟩).pt.counts = 0 ∧
    (p.exec.memoryPubAt ⟨0, p.cfg.memRows_pos⟩).pt.indicator = 0 ∧
    (p.exec.memoryPubAt ⟨0, p.cfg.memRows_pos⟩).ipre = 0 ∧
    (p.exec.memoryPubAt
      (p.cfg.orbit.lastIndex p.cfg.memRows p.cfg.memRows_pos)).icur = 0

/-- One canonical compute auxiliary value per exact compute row. -/
abbrev ExactCanonicalProgAux (p : ExactCanonicalRAPProblem F K) :=
  Fin p.cfg.compRows → ComputeTable.Extra K

/-- One canonical memory LogUp witness per exact memory row. -/
abbrev ExactCanonicalMemAux (p : ExactCanonicalRAPProblem F K) :=
  Fin p.cfg.memRows → K

/-- Compute RAP parameters derived only from the problem's one exact configuration. -/
noncomputable def exactCanonicalProgParams (p : ExactCanonicalRAPProblem F K) :
    SegmentedRAPParams K :=
  SegmentedRAPParams.ofComputeConfig p.cfg (fun _ => 0)

/-- Memory RAP parameters derived only from the same problem's exact configuration. -/
noncomputable def exactCanonicalMemParams (p : ExactCanonicalRAPProblem F K) :
    SegmentedRAPParams K :=
  SegmentedRAPParams.ofMemoryConfig p.cfg
    (p.exec.memoryPubAt ⟨0, p.cfg.memRows_pos⟩).lambda (fun _ => 0)

/-- The canonical exact compute encoder: canonical public/decomposition projections, one auxiliary
family, and the configuration's certified compute orbit-prefix nodes. -/
noncomputable def exactCanonicalEncodeProg
    (p : ExactCanonicalRAPProblem F K) (ex : ExactCanonicalProgAux p) :
    Fin Trans.computeAIRchained.numTraceCols → K[X] :=
  encodeComputeTrace
    (fun i => computeEnvFull p.cfg.challenges.computeInputs
      (ComputeTable.opSel (p.exec.computePubAt i).state)
      (p.exec.computePubAt i) (p.exec.computeDecAt i) (ex i))
    p.cfg.compNodes

/-- The canonical exact memory encoder: canonical memory projections, one LogUp witness family,
and the same configuration's certified memory orbit-prefix nodes. -/
noncomputable def exactCanonicalEncodeMem
    (p : ExactCanonicalRAPProblem F K) (g : ExactCanonicalMemAux p) :
    Fin (Trans.memoryAIRchained (K := K)).numTraceCols → K[X] :=
  encodeMemoryTrace
    (fun i => memoryEnvFull p.cfg.challenges.memoryInputs
      (MemoryTable.opSel (p.exec.memoryPubAt i).st)
      (p.exec.memoryPubAt i) (g i))
    p.cfg.memNodes

/-- Both problem indices use the same precise problem type, while
the two chained AIRs, dependent auxiliary types, exact-config parameter functions, and canonical
encoders all occur in the proposition's type indices. -/
abbrev ExactChainedHasCanonicalRAP2 (F K : Type)
    [Field F] [Field K] [Algebra F K] : Prop :=
  HasCanonicalRAP2 K
    (ExactCanonicalRAPProblem F K) (ExactCanonicalRAPProblem F K)
    (exactComputeChainedAccepts (F := F) (K := K))
    (exactMemoryChainedAccepts (F := F) (K := K))
    Trans.computeAIRchained (Trans.memoryAIRchained (K := K))
    (ExactCanonicalProgAux (F := F) (K := K))
    (ExactCanonicalMemAux (F := F) (K := K))
    (exactCanonicalProgParams (F := F) (K := K))
    (exactCanonicalMemParams (F := F) (K := K))
    (exactCanonicalEncodeProg (F := F) (K := K))
    (exactCanonicalEncodeMem (F := F) (K := K))

noncomputable instance exactChainedHasCanonicalRAP2 (F K : Type)
    [Field F] [Field K] [Algebra F K] :
    ExactChainedHasCanonicalRAP2 F K where
  compute_iff p := by
    simpa [exactComputeChainedAccepts, exactCanonicalProgParams,
      exactCanonicalEncodeProg, ComputeSegmentedRAPSatisfies,
      SegmentedRAPParams.rap, SegmentedRAPParams.ofComputeConfig] using
      (computeSegmentedRAP_wholeTrace_iff p.cfg
        p.exec.computePubAt p.exec.computeDecAt p.compute_wf p.z_ne_zero).symm
  memory_iff p := by
    simpa [exactMemoryChainedAccepts, exactCanonicalMemParams,
      exactCanonicalEncodeMem, MemorySegmentedRAPSatisfies,
      SegmentedRAPParams.rap, SegmentedRAPParams.ofMemoryConfig] using
      (memorySegmentedRAP_wholeTrace_iff p.cfg
        p.exec.memoryPubAt p.memory_wf p.z_ne_zero
        p.memory_same_lambda).symm

/-! ## Type exposure and same-execution certificate -/

theorem exactChainedHasCanonicalRAP2_type_indices (F K : Type)
    [Field F] [Field K] [Algebra F K] :
    ExactChainedHasCanonicalRAP2 F K =
      HasCanonicalRAP2 K
        (ExactCanonicalRAPProblem F K) (ExactCanonicalRAPProblem F K)
        (exactComputeChainedAccepts (F := F) (K := K))
        (exactMemoryChainedAccepts (F := F) (K := K))
        Trans.computeAIRchained (Trans.memoryAIRchained (K := K))
        (ExactCanonicalProgAux (F := F) (K := K))
        (ExactCanonicalMemAux (F := F) (K := K))
        (exactCanonicalProgParams (F := F) (K := K))
        (exactCanonicalMemParams (F := F) (K := K))
        (exactCanonicalEncodeProg (F := F) (K := K))
        (exactCanonicalEncodeMem (F := F) (K := K)) :=
  rfl

/-- Both official, indexed `RAP.Satisfies` families for one and the same exact problem. -/
def ExactCanonicalRAPSameExecutionCertificate
    (p : ExactCanonicalRAPProblem F K) : Prop :=
  (∃ ex : ExactCanonicalProgAux p, ∀ kind,
      ((exactCanonicalProgParams p).rap Trans.computeAIRchained kind).Satisfies
        (exactCanonicalEncodeProg p ex)) ∧
    (∃ g : ExactCanonicalMemAux p, ∀ kind,
      ((exactCanonicalMemParams p).rap (Trans.memoryAIRchained (K := K)) kind).Satisfies
        (exactCanonicalEncodeMem p g))

theorem ChainedSemanticExactLanguage.exactCanonicalRAP_sameExecution
    {cfg : ExactConfig F K} {exec : ExactExecution cfg}
    (h : ChainedSemanticExactLanguage cfg exec) :
    ExactCanonicalRAPSameExecutionCertificate
      (ExactCanonicalRAPProblem.ofChained h) := by
  simpa [ExactCanonicalRAPSameExecutionCertificate,
    ExactCanonicalRAPProblem.ofChained,
    exactCanonicalProgParams, exactCanonicalMemParams,
    exactCanonicalEncodeProg, exactCanonicalEncodeMem,
    ComputeExecutionSegmentedRAPSatisfies,
    MemoryExecutionSegmentedRAPSatisfies,
    ComputeSegmentedRAPSatisfies, MemorySegmentedRAPSatisfies,
    SegmentedRAPParams.rap,
    SegmentedRAPParams.ofComputeConfig,
    SegmentedRAPParams.ofMemoryConfig] using h.segmentedRAP

/-! ## Discrimination and negative regressions -/

/-- The exact compute row domain in the official parameter index is genuinely nonempty. -/
theorem exactCanonicalProgRowDomain_nonempty
    (p : ExactCanonicalRAPProblem F K) :
    (exactCanonicalProgParams p).domain .row ≠ ∅ := by
  intro hempty
  let first : Fin p.cfg.compRows := ⟨0, p.cfg.compRows_pos⟩
  have hnode : p.cfg.compNodes first ∈ p.cfg.computeDomain .row := by
    rw [p.cfg.computeRowDomain_eq_nodes]
    exact Finset.mem_image.mpr ⟨first, Finset.mem_univ first, rfl⟩
  have hindexed :
      p.cfg.compNodes first ∈ (exactCanonicalProgParams p).domain .row := by
    simpa [exactCanonicalProgParams, SegmentedRAPParams.ofComputeConfig] using hnode
  rw [hempty] at hindexed
  simp at hindexed

/-- The exact memory row domain in the official parameter index is genuinely nonempty. -/
theorem exactCanonicalMemRowDomain_nonempty
    (p : ExactCanonicalRAPProblem F K) :
    (exactCanonicalMemParams p).domain .row ≠ ∅ := by
  intro hempty
  let first : Fin p.cfg.memRows := ⟨0, p.cfg.memRows_pos⟩
  have hnode : p.cfg.memNodes first ∈ p.cfg.memoryDomain .row := by
    rw [p.cfg.memoryRowDomain_eq_nodes]
    exact Finset.mem_image.mpr ⟨first, Finset.mem_univ first, rfl⟩
  have hindexed :
      p.cfg.memNodes first ∈ (exactCanonicalMemParams p).domain .row := by
    simpa [exactCanonicalMemParams, SegmentedRAPParams.ofMemoryConfig] using hnode
  rw [hempty] at hindexed
  simp at hindexed

/-- An arbitrary replacement parameter tuple with an empty compute row domain is not the official
compute parameter index. -/
theorem exactCanonicalProgParams_ne_emptyDomain
    (p : ExactCanonicalRAPProblem F K) (q : SegmentedRAPParams K)
    (hq : q.domain .row = ∅) :
    exactCanonicalProgParams p ≠ q := by
  intro h
  apply exactCanonicalProgRowDomain_nonempty p
  exact (congrArg (fun r : SegmentedRAPParams K => r.domain .row) h).trans hq

/-- An arbitrary replacement parameter tuple with an empty memory row domain is not the official
memory parameter index. -/
theorem exactCanonicalMemParams_ne_emptyDomain
    (p : ExactCanonicalRAPProblem F K) (q : SegmentedRAPParams K)
    (hq : q.domain .row = ∅) :
    exactCanonicalMemParams p ≠ q := by
  intro h
  apply exactCanonicalMemRowDomain_nonempty p
  exact (congrArg (fun r : SegmentedRAPParams K => r.domain .row) h).trans hq

/-- Equality with an arbitrary compute RAP forces both the chained-AIR width and exact
kind-specific domain.  Thus an arbitrary replacement cannot preserve the official indices. -/
theorem exactCanonicalProgRAP_equality_forces_indices
    (p : ExactCanonicalRAPProblem F K) (kind : ConstraintKind) (R : RAP K)
    (hR : (exactCanonicalProgParams p).rap Trans.computeAIRchained kind = R) :
    R.w = Trans.computeAIRchained.numTraceCols ∧
      R.H = p.cfg.computeDomain kind := by
  subst R
  exact ⟨rfl, rfl⟩

/-- Equality with an arbitrary memory RAP forces both the chained-AIR width and exact
kind-specific domain. -/
theorem exactCanonicalMemRAP_equality_forces_indices
    (p : ExactCanonicalRAPProblem F K) (kind : ConstraintKind) (R : RAP K)
    (hR : (exactCanonicalMemParams p).rap (Trans.memoryAIRchained (K := K)) kind = R) :
    R.w = (Trans.memoryAIRchained (K := K)).numTraceCols ∧
      R.H = p.cfg.memoryDomain kind := by
  subst R
  exact ⟨rfl, rfl⟩

/-- In particular, no arbitrary empty-domain compute RAP is the official indexed row RAP. -/
theorem exactCanonicalProgRowRAP_ne_emptyDomain
    (p : ExactCanonicalRAPProblem F K) (R : RAP K) (hR : R.H = ∅) :
    (exactCanonicalProgParams p).rap Trans.computeAIRchained .row ≠ R := by
  intro h
  have hindices := exactCanonicalProgRAP_equality_forces_indices p .row R h
  apply exactCanonicalProgRowDomain_nonempty p
  exact hindices.2.symm.trans hR

/-- In particular, no arbitrary empty-domain memory RAP is the official indexed row RAP. -/
theorem exactCanonicalMemRowRAP_ne_emptyDomain
    (p : ExactCanonicalRAPProblem F K) (R : RAP K) (hR : R.H = ∅) :
    (exactCanonicalMemParams p).rap (Trans.memoryAIRchained (K := K)) ConstraintKind.row ≠ R := by
  intro h
  have hindices := exactCanonicalMemRAP_equality_forces_indices p .row R h
  apply exactCanonicalMemRowDomain_nonempty p
  exact hindices.2.symm.trans hR

theorem legacyEmptyRprog_ne_exactCanonicalProgRowRAP
    (p : ExactCanonicalRAPProblem F K) (α β : K) (Ksz : ℕ) :
    (exactCanonicalProgParams p).rap Trans.computeAIRchained .row ≠
      (Nock.NockVMROM.nock_hasCanonicalRAP F K α β Ksz).Rprog :=
  exactCanonicalProgRowRAP_ne_emptyDomain p _ rfl

/-- Concrete AIR discrimination: the two AIR type indices have different trace widths. -/
theorem exactChainedHasCanonicalRAP2_AIRs_discriminated :
    Trans.computeAIRchained.numTraceCols = 94 ∧
      (Trans.memoryAIRchained (K := K)).numTraceCols = 36 ∧
      Trans.computeAIRchained ≠ (Trans.memoryAIRchained (K := K)) := by
  have hcomp : Trans.computeAIRchained.numTraceCols = 94 := by
    simpa only [kindSeg_numTraceCols] using comp_all_seg_cols.1
  have hmem : (Trans.memoryAIRchained (K := K)).numTraceCols = 36 := by
    simpa only [kindSeg_numTraceCols] using mem_seg_cols.1
  refine ⟨hcomp, hmem, ?_⟩
  intro h
  have hw := congrArg Reified.AIR.numTraceCols h
  rw [hcomp, hmem] at hw
  omega

/-- Honest scope receipt: these are the 94/36 table-chained families, not the paper's named
`+IO` 199/196-column composition. -/
theorem exactChainedCanonicalRAP_minusIO_scope :
    Trans.computeAIRchained.numTraceCols = 94 ∧
      (Trans.memoryAIRchained (K := K)).numTraceCols = 36 ∧
      Trans.computeAIRchained.numTraceCols ≠ 199 ∧
      (Trans.memoryAIRchained (K := K)).numTraceCols ≠ 196 := by
  have hcomp : Trans.computeAIRchained.numTraceCols = 94 := by
    simpa only [kindSeg_numTraceCols] using comp_all_seg_cols.1
  have hmem : (Trans.memoryAIRchained (K := K)).numTraceCols = 36 := by
    simpa only [kindSeg_numTraceCols] using mem_seg_cols.1
  refine ⟨hcomp, hmem, ?_, ?_⟩
  · omega
  · omega

end

end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.exactChainedHasCanonicalRAP2
#print axioms Nock.NockVMROM.Thm54.ChainedSemanticExactLanguage.exactCanonicalRAP_sameExecution
#print axioms Nock.NockVMROM.Thm54.exactCanonicalProgParams_ne_emptyDomain
#print axioms Nock.NockVMROM.Thm54.exactCanonicalProgRAP_equality_forces_indices
#print axioms Nock.NockVMROM.Thm54.legacyEmptyRprog_ne_exactCanonicalProgRowRAP
#print axioms Nock.NockVMROM.Thm54.exactChainedHasCanonicalRAP2_AIRs_discriminated
#print axioms Nock.NockVMROM.Thm54.exactChainedCanonicalRAP_minusIO_scope
