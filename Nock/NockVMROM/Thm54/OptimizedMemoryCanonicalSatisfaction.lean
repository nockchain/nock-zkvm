import Nock.NockVMROM.Thm54.OptimizedMemoryRAP
import Nock.WalkInGate

/-!
# Canonical satisfaction of the optimized memory RAP

This module connects the exact same-execution memory assignment to the coordinate-expanded
`171/93` source RAP and then to its authorized `196/104` padding
.
-/

namespace Nock.NockVMROM.Thm54
namespace OptimizedMemoryCanonicalSatisfaction

open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open scoped Polynomial
open CoordinateBasis
open CoordinateCompiler
open MonolithicRAP
open StrictExtension
open OptimizedMemoryCoreInventory
open OptimizedMemoryCodec
open OptimizedMemorySemanticRealization
open OptimizedMemoryCanonicalTrace
open OptimizedMemoryGateBasis
open OptimizedMemoryRAP
open OptimizedMemorySameExecution

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

theorem env_ext {E₁ E₂ : Env K}
    (htrace : ∀ i, E₁.trace i = E₂.trace i)
    (hnext : ∀ i, E₁.traceNext i = E₂.traceNext i)
    (hchal : ∀ i, E₁.chal i = E₂.chal i)
    (hpub : ∀ i, E₁.pub i = E₂.pub i) :
    E₁ = E₂ := by
  cases E₁ with
  | mk t₁ n₁ c₁ p₁ =>
      cases E₂ with
      | mk t₂ n₂ c₂ p₂ =>
          congr <;> funext i
          · exact htrace i
          · exact hnext i
          · exact hchal i
          · exact hpub i

def canonicalPhysicalEnv
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) : Env F :=
  envOfTrace (canonicalSourceTrace A nodes b R.problem.cfg.kMem) orbit.ω (nodes i) chalVal pubVal

def canonicalGatheredEnv
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) : Env K :=
  gatherEnv b ((memorySourceTemplate b).col0 3)
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)

theorem canonical_physical_cprime
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (k : Fin 3) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace (177 + (k : ℕ)) =
      coord b (R.problem.exec.memoryPubAt i).cprime k := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (by omega : 177 + (k : ℕ) < 182)]
  exact canonicalSourceTrace_cprime A nodes hnodes b R.problem.cfg.kMem i k

theorem canonical_gather_cprime
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 57 =
      (R.problem.exec.memoryPubAt i).cprime := by
  have hcol : (memorySourceTemplate b).col0 3 .traceCur 57 = 177 := by
    rw [memorySourceTemplate_col0]; rfl
  simp only [canonicalGatheredEnv, gatherEnv]
  rw [hcol]
  have hk (k : Fin 3) :=
    canonical_physical_cprime A nodes hnodes b chalVal pubVal orbit i k
  simp only [hk]
  exact b.sum_repr ((R.problem.exec.memoryPubAt i).cprime)

theorem payload_extIndex_ne_rootMask (role : MemoryTablePayloadRole) :
    ((extensionEquiv (.inl role) : ℕ) ≠ 49) := by
  revert role
  decide

theorem canonical_gather_extension_current
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (role : Fin 56)
    (hrole : (role : ℕ) ≠ 49) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace role =
      (encodedRowAt (F := F) A i).extension (extensionEquiv.symm role) := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ q : Fin 3,
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace
        (6 + 3 * (role : ℕ) + (q : ℕ)) • b q) k =
    coord b ((encodedRowAt (F := F) A i).extension (extensionEquiv.symm role)) k
  rw [coord_sum_smul]
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (show 6 + 3 * (role : ℕ) + (k : ℕ) < 182 by omega)]
  rw [canonicalSourceTrace_eval A nodes hnodes b R.problem.cfg.kMem i
    ⟨6 + 3 * (role : ℕ) + (k : ℕ), by omega⟩
    (OptimizedMemoryCanonicalTrace.extRole_ne_rootMask hrole k)
    (OptimizedMemoryCanonicalTrace.extRole_ne_dequeueMask hrole k)]
  have hdiv : (6 + 3 * (role : ℕ) + (k : ℕ) - 6) / 3 = (role : ℕ) := by omega
  have hmod : (6 + 3 * (role : ℕ) + (k : ℕ) - 6) % 3 = (k : ℕ) := by omega
  have hnotbase : ¬ 6 + 3 * (role : ℕ) + (k : ℕ) < 6 := by omega
  simp [sourceCell, hnotbase, hdiv, hmod]

theorem canonical_extension_coord_current
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (role : Fin 56) (k : Fin 3)
    (hcol : 6 + 3 * (role : ℕ) + (k : ℕ) ≠ 153)
    (hdeq : 6 + 3 * (role : ℕ) + (k : ℕ) ≠ 154) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace
        (6 + 3 * (role : ℕ) + (k : ℕ)) =
      coord b
        ((encodedRowAt (F := F) A i).extension (extensionEquiv.symm role)) k := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (show 6 + 3 * (role : ℕ) + (k : ℕ) < 182 by omega)]
  rw [canonicalSourceTrace_eval A nodes hnodes b R.problem.cfg.kMem i
    ⟨6 + 3 * (role : ℕ) + (k : ℕ), by omega⟩ hcol hdeq]
  have hdiv : (6 + 3 * (role : ℕ) + (k : ℕ) - 6) / 3 = (role : ℕ) := by omega
  have hmod : (6 + 3 * (role : ℕ) + (k : ℕ) - 6) % 3 = (k : ℕ) := by omega
  have hnotbase : ¬ 6 + 3 * (role : ℕ) + (k : ℕ) < 6 := by omega
  simp [sourceCell, hnotbase, hdiv, hmod]

theorem canonical_gather_extension_next
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (role : Fin 56) (hrole : (role : ℕ) ≠ 49) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).traceNext role =
      (encodedRowAt (F := F) A ⟨(i : ℕ) + 1, hi⟩).extension
        (extensionEquiv.symm role) := by
  rw [eq_iff_coords_eq b]
  intro k
  change coord b
    (∑ q : Fin 3,
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).traceNext
        (6 + 3 * (role : ℕ) + (q : ℕ)) • b q) k =
    coord b
      ((encodedRowAt (F := F) A ⟨(i : ℕ) + 1, hi⟩).extension
        (extensionEquiv.symm role)) k
  rw [coord_sum_smul]
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (show 6 + 3 * (role : ℕ) + (k : ℕ) < 182 by omega)]
  have hsucc' : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i := by
    simpa [mul_comm] using hsucc
  rw [← hsucc', canonicalSourceTrace_eval A nodes hnodes b R.problem.cfg.kMem
    ⟨(i : ℕ) + 1, hi⟩
    ⟨6 + 3 * (role : ℕ) + (k : ℕ), by omega⟩
    (OptimizedMemoryCanonicalTrace.extRole_ne_rootMask hrole k)
    (OptimizedMemoryCanonicalTrace.extRole_ne_dequeueMask hrole k)]
  have hdiv : (6 + 3 * (role : ℕ) + (k : ℕ) - 6) / 3 = (role : ℕ) := by omega
  have hmod : (6 + 3 * (role : ℕ) + (k : ℕ) - 6) % 3 = (k : ℕ) := by omega
  have hnotbase : ¬ 6 + 3 * (role : ℕ) + (k : ℕ) < 6 := by omega
  simp [sourceCell, hnotbase, hdiv, hmod]

theorem canonical_gather_table_current
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (role : MemoryTablePayloadRole) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace
        (extensionEquiv (.inl role)) =
      match role with
      | .inr (.inr (.inr r)) =>
          if r = 0 then
            RowLayout.interResidentAcc A.interCompress10 R.problem.exec.memoryRows i.val
          else if r = 1 then
            RowLayout.interResidentAcc A.interCompress10 R.problem.exec.memoryRows (i.val + 1)
          else
            (exactMemoryRowEnv A i).trace (memoryTableSourceColumn role)
      | _ =>
          (exactMemoryRowEnv A i).trace (memoryTableSourceColumn role) := by
  have hrow := canonical_gather_extension_current A nodes hnodes b chalVal pubVal orbit i
    (extensionEquiv (.inl role)) (payload_extIndex_ne_rootMask role)
  rw [extensionEquiv.symm_apply_apply] at hrow
  simp [encodedRowAt, semanticRowAt, encode, encodeExtension, extensionEquiv_apply] at hrow ⊢
  exact hrow

/-- Overlay role 27 (`ipre`): honest sampled-coin value.  Twin of
`sampledMemoryRoleValue 6` (`coResidentAcc`). -/
theorem canonical_ipre
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 27 =
      RowLayout.interResidentAcc A.interCompress10 R.problem.exec.memoryRows i.val := by
  have h := canonical_gather_table_current A nodes hnodes b chalVal pubVal orbit i
    (.inr (.inr (.inr (0 : Fin 4))))
  simpa [extensionEquiv_apply, extensionIndex] using h

/-- Overlay role 28 (`icur`): honest sampled-coin value.  Twin of
`sampledMemoryRoleValue 7` (`coResidentAcc` after the row). -/
theorem canonical_icur
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 28 =
      RowLayout.interResidentAcc A.interCompress10 R.problem.exec.memoryRows (i.val + 1) := by
  have h := canonical_gather_table_current A nodes hnodes b chalVal pubVal orbit i
    (.inr (.inr (.inr (1 : Fin 4))))
  simpa [extensionEquiv_apply, extensionIndex] using h

theorem canonical_gather_table_next
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (role : MemoryTablePayloadRole) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).traceNext
        (extensionEquiv (.inl role)) =
      match role with
      | .inr (.inr (.inr r)) =>
          if r = 0 then
            RowLayout.interResidentAcc A.interCompress10 R.problem.exec.memoryRows ((i : ℕ) + 1)
          else if r = 1 then
            RowLayout.interResidentAcc A.interCompress10 R.problem.exec.memoryRows ((i : ℕ) + 1 + 1)
          else
            (exactMemoryRowEnv A ⟨(i : ℕ) + 1, hi⟩).trace (memoryTableSourceColumn role)
      | _ =>
          (exactMemoryRowEnv A ⟨(i : ℕ) + 1, hi⟩).trace (memoryTableSourceColumn role) := by
  have hrow := canonical_gather_extension_next A nodes hnodes b chalVal pubVal orbit
    i hi hsucc (extensionEquiv (.inl role)) (payload_extIndex_ne_rootMask role)
  rw [extensionEquiv.symm_apply_apply] at hrow
  simp [encodedRowAt, semanticRowAt, encode, encodeExtension, extensionEquiv_apply] at hrow ⊢
  exact hrow

theorem canonical_gather_walk_current
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (role : ForestWalkRole) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace
        (extensionEquiv (.inr (.inl role))) =
      (exactMemoryWalkRowEnv A i).trace role := by
  have hne : ((extensionEquiv (.inr (.inl role)) : ℕ) ≠ 49) := by
    simp [extensionEquiv_apply, extensionIndex]; omega
  have hrow := canonical_gather_extension_current A nodes hnodes b chalVal pubVal orbit i
    (extensionEquiv (.inr (.inl role))) hne
  rw [extensionEquiv.symm_apply_apply] at hrow
  simpa [encodedRowAt, semanticRowAt, encode, encodeExtension] using hrow

theorem canonical_gather_walk_next
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (role : ForestWalkRole) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).traceNext
        (extensionEquiv (.inr (.inl role))) =
      (exactMemoryWalkRowEnv A ⟨(i : ℕ) + 1, hi⟩).trace role := by
  have hne : ((extensionEquiv (.inr (.inl role)) : ℕ) ≠ 49) := by
    simp [extensionEquiv_apply, extensionIndex]; omega
  have hrow := canonical_gather_extension_next A nodes hnodes b chalVal pubVal orbit
    i hi hsucc (extensionEquiv (.inr (.inl role))) hne
  rw [extensionEquiv.symm_apply_apply] at hrow
  simpa [encodedRowAt, semanticRowAt, encode, encodeExtension] using hrow

theorem canonical_gather_sampled_current
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (role : SampledMemoryIORole)
    (hrole : (role : ℕ) ≠ 12) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace
        (extensionEquiv (.inr (.inr (.inl role)))) =
      sampledMemoryRoleValue A i role := by
  have hne : ((extensionEquiv (.inr (.inr (.inl role))) : ℕ) ≠ 49) := by
    simp [extensionEquiv_apply, extensionIndex]; omega
  have hrow := canonical_gather_extension_current A nodes hnodes b chalVal pubVal orbit i
    (extensionEquiv (.inr (.inr (.inl role)))) hne
  rw [extensionEquiv.symm_apply_apply] at hrow
  simpa [encodedRowAt, semanticRowAt, encode, encodeExtension] using hrow

theorem canonical_gather_sampled_index
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (role : SampledMemoryIORole)
    (hrole : (role : ℕ) ≠ 12) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace (37 + role) =
      sampledMemoryRoleValue A i role := by
  simpa [extensionEquiv_apply, extensionIndex] using
    canonical_gather_sampled_current A nodes hnodes b chalVal pubVal orbit i role hrole

theorem canonical_gather_selectorMirror_current
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (role : StateSelectorMirrorRole) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace
        (extensionEquiv (.inr (.inr (.inr (.inl role))))) =
      algebraMap F K
        (stateSelector (F := F) (R.problem.exec.memoryPubAt i).st role) := by
  have hne : ((extensionEquiv (.inr (.inr (.inr (.inl role)))) : ℕ) ≠ 49) := by
    simp [extensionEquiv_apply, extensionIndex]; omega
  have hrow := canonical_gather_extension_current A nodes hnodes b chalVal pubVal orbit i
    (extensionEquiv (.inr (.inr (.inr (.inl role))))) hne
  rw [extensionEquiv.symm_apply_apply] at hrow
  simpa [encodedRowAt, semanticRowAt, encode, encodeExtension] using hrow

theorem canonical_base_current
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (j : Fin 6) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace j =
      (encodedRowAt (F := F) A i).base j := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (show (j : ℕ) < 182 by omega)]
  rw [canonicalSourceTrace_eval A nodes hnodes b R.problem.cfg.kMem i ⟨(j : ℕ), by omega⟩
    (by
      have hj : (j : ℕ) < 6 := j.isLt
      exact Nat.ne_of_lt (lt_trans hj (by decide : 6 < 153)))
    (by
      have hj : (j : ℕ) < 6 := j.isLt
      exact Nat.ne_of_lt (lt_trans hj (by decide : 6 < 154)))]
  simp [sourceCell]

theorem canonical_base_next
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω)
    (j : Fin 6) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).traceNext j =
      (encodedRowAt (F := F) A ⟨(i : ℕ) + 1, hi⟩).base j := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (show (j : ℕ) < 182 by omega)]
  have hsucc' : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i := by
    simpa [mul_comm] using hsucc
  rw [← hsucc', canonicalSourceTrace_eval A nodes hnodes b R.problem.cfg.kMem
    ⟨(i : ℕ) + 1, hi⟩ ⟨(j : ℕ), by omega⟩
    (by
      have hj : (j : ℕ) < 6 := j.isLt
      exact Nat.ne_of_lt (lt_trans hj (by decide : 6 < 153)))
    (by
      have hj : (j : ℕ) < 6 := j.isLt
      exact Nat.ne_of_lt (lt_trans hj (by decide : 6 < 154)))]
  simp [sourceCell]

/-- Exact coordinate pins for the memory-table challenges, the aggregate forest challenge, and
its two public initialization values.  Fold challenge `6` remains sampled independently. -/
structure ExactMemoryCoordinatePins
    (A : SampledIOSameExecutionAssignment R p)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F) : Prop where
  memoryChallenge :
    ∀ q : Fin 3,
      (∑ k : Fin 3, chalVal (6 + 3 * (q : ℕ) + (k : ℕ)) • b k) =
        (exactMemoryRowEnv A ⟨0, R.problem.cfg.memRows_pos⟩).chal q
  walkChallenge :
    (∑ k : Fin 3, chalVal (6 + 3 * 3 + (k : ℕ)) • b k) = R.memoryWalkAlpha
  walkInitialCount :
    (∑ k : Fin 3, pubVal (6 + 3 * 0 + (k : ℕ)) • b k) =
      R.memoryWalkAlpha ^ R.problem.cfg.kMem
  /-- The post-challenge public `requests` (extension public role `2`, base publics `12..14`) is
  the sampled IO terminal — the value the memory chip's shared terminal role `40` is bound to
. -/
  requests :
    (∑ k : Fin 3, pubVal (6 + 3 * 2 + (k : ℕ)) • b k) = A.witness10.terminal
  /-- Memory `𝕂` challenge slot `4` is the sampled record-compression coin `γ`: the coin `denominatorPinMixed` reads. -/
  sampledGamma :
    (∑ k : Fin 3, chalVal (6 + 3 * 4 + (k : ℕ)) • b k) = A.sampled.coins.gamma
  /-- Memory `𝕂` challenge slot `5` is the sampled LogUp pole (A-mem-2): the paper's `β` of
  the paper, in `FiniteIO.compress`'s additive convention. -/
  sampledPole :
    (∑ k : Fin 3, chalVal (6 + 3 * 5 + (k : ℕ)) • b k) = A.sampled.coins.pole
  /-- Memory `𝕂` challenge slot `6` is the sampled internal `intermediate` pole
. -/
  sampledInterPole :
    (∑ k : Fin 3, chalVal (6 + 3 * 6 + (k : ℕ)) • b k) = A.interPole
  /-- Memory `𝕂` challenge slot `7` is the walk-node RLC coin `γ`: the coin the in-gate `x^mem` label RLCs read
  (`MemoryWalkLabel.walkGammaChallenge`; the paper, `:848-850`, `:1006`) — the family's
  shared `walkGamma`, the same coin the compute walk reads at compute slot `10`. -/
  walkGamma :
    (∑ k : Fin 3, chalVal (6 + 3 * 7 + (k : ℕ)) • b k) = R.walkGamma
  /-- Memory `𝕂` challenge slot `8` is the accounting base `λ`. -/
  sampledLambda :
    (∑ k : Fin 3, chalVal (6 + 3 * 8 + (k : ℕ)) • b k) =
      (exactMemoryRowEnv A ⟨0, R.problem.cfg.memRows_pos⟩).chal 8

theorem exactMemoryRowEnv_selector
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) (q : Fin 4) :
    (exactMemoryRowEnv A i).trace q =
      algebraMap F K
        (stateSelector (F := F) (R.problem.exec.memoryPubAt i).st q) := by
  generalize hst : (R.problem.exec.memoryPubAt i).st = s
  fin_cases q <;> cases s <;>
    simp [exactMemoryRowEnv, memoryEnvFull, MemoryTable.opSel,
      stateSelector, stateIndex, hst]

theorem exactMemoryRowEnv_trace_ge35
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) (j : ℕ) (hj : 36 ≤ j) :
    (exactMemoryRowEnv A i).trace j = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  simp [exactMemoryRowEnv, memoryEnvFull, Nat.add_comm]

theorem exactMemoryRowEnv_cprime
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) :
    (exactMemoryRowEnv A i).trace 35 = (R.problem.exec.memoryPubAt i).cprime := by
  simp [exactMemoryRowEnv, memoryEnvFull]

theorem exactMemoryRowEnv_chal_ge3
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) (j : ℕ) (hj : 3 ≤ j) (h8 : j ≠ 8) :
    (exactMemoryRowEnv A i).chal j = 0 := by
  simp only [exactMemoryRowEnv, memoryEnvFull]
  split
  · omega
  · omega
  · omega
  · omega
  · rfl

theorem exactMemoryRowEnv_chal_lambda
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) :
    (exactMemoryRowEnv A i).chal 8 = (R.problem.exec.memoryPubAt i).lambda := by
  simp [exactMemoryRowEnv, memoryEnvFull]

/-- Off the overlay roles, `semanticRowAt.table` is the exact-row column
`memoryTableSourceColumn`.  `congrArg` on that column — never `subst` the role. -/
theorem semanticRowAt_table_eq_exact
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows)
    (role : MemoryTablePayloadRole)
    (h : (memoryTableSourceColumn role : ℕ) ≠ 31 ∧
         (memoryTableSourceColumn role : ℕ) ≠ 32) :
    (semanticRowAt A i).table role =
      (exactMemoryRowEnv A i).trace (memoryTableSourceColumn role) := by
  rcases role with r | r
  · simp [semanticRowAt]
  · rcases r with r | r
    · simp [semanticRowAt]
    · rcases r with r | r
      · simp [semanticRowAt]
      · have hr0 : r ≠ 0 := by
          intro heq
          exact h.1 (by simp [memoryTableSourceColumn, heq])
        have hr1 : r ≠ 1 := by
          intro heq
          exact h.2 (by simp [memoryTableSourceColumn, heq])
        simp [semanticRowAt, hr0, hr1]

/-- After the W4 overlay, roles 27/28 (`ipre`/`icur`, physical 31/32) are
`interResidentAcc` at sampled coins, not the table pubs.  The subst env
agrees with `exactMemoryRowEnv` on every other column. -/
theorem canonical_memorySubst_trace
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) (j : ℕ)
    (hinter : j ≠ 31 ∧ j ≠ 32) :
    (Env.ofSubst memorySubst
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)).trace j =
      (exactMemoryRowEnv A i).trace j := by
  simp only [Env.ofSubst]
  by_cases h4 : j < 4
  · have hs := canonical_gather_selectorMirror_current
      A nodes hnodes b chalVal pubVal orbit i ⟨j, h4⟩
    rw [exactMemoryRowEnv_selector A i ⟨j, h4⟩]
    simpa [memorySubst, extensionEquiv_apply, extensionIndex, extVar, Expr.eval, h4] using hs
  · by_cases h35 : j < 35
    · let q : Fin 31 := ⟨j - 4, by omega⟩
      let role : MemoryTablePayloadRole := memoryTablePayloadEquiv.symm q
      have hidx : memoryTablePayloadIndex role = q :=
        memoryTablePayloadEquiv.apply_symm_apply q
      have hcol : (memoryTableSourceColumn role : ℕ) = j := by
        have hi := congrArg Fin.val hidx
        rw [memoryTableSourceColumn_val]
        simp only [q] at hi
        omega
      have hnot :
          (memoryTableSourceColumn role : ℕ) ≠ 31 ∧
            (memoryTableSourceColumn role : ℕ) ≠ 32 :=
        ⟨fun h31 => hinter.1 (hcol ▸ h31), fun h32 => hinter.2 (hcol ▸ h32)⟩
      have hrow := canonical_gather_extension_current A nodes hnodes b chalVal pubVal orbit i
        (extensionEquiv (.inl role)) (payload_extIndex_ne_rootMask role)
      rw [extensionEquiv.symm_apply_apply] at hrow
      have hidxN : (extensionEquiv (.inl role) : ℕ) = j - 4 := by
        simp [extensionEquiv_apply, extensionIndex_payload_val, hidx, q]
      simp only [memorySubst, h4, h35, extVar, Expr.eval]
      simp [encodedRowAt, encode, encodeExtension] at hrow
      rw [semanticRowAt_table_eq_exact A i role hnot] at hrow
      calc
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace (j - 4)
            = (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace
                (extensionEquiv (.inl role)) := by rw [hidxN]
        _ = (exactMemoryRowEnv A i).trace (memoryTableSourceColumn role) := hrow
        _ = (exactMemoryRowEnv A i).trace j := by rw [hcol]
    · by_cases h35eq : j = 35
      · subst j
        have hms : memorySubst .traceCur 35 = extVar .traceCur 57 := by
          simp [memorySubst]
        rw [hms]
        simp [extVar, Expr.eval]
        rw [canonical_gather_cprime A nodes hnodes b chalVal pubVal orbit i,
          exactMemoryRowEnv_cprime]
      · rw [exactMemoryRowEnv_trace_ge35 A i j (by omega)]
        simp [memorySubst, h4, h35, h35eq, Expr.eval]

/-- Table column `j` (`4 ≤ j < 35`) of the exact memory row is extension role `j − 4` of the
canonical gathered row (`memorySubst`). -/
theorem canonical_table_role
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) (j : ℕ) (hj4 : 4 ≤ j) (hj : j < 35)
    (hinter : j ≠ 31 ∧ j ≠ 32) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace (j - 4) =
      (exactMemoryRowEnv A i).trace j := by
  have hsub := canonical_memorySubst_trace A nodes hnodes b chalVal pubVal orbit pins i j hinter
  simpa [Env.ofSubst, memorySubst, extVar, Expr.eval, show ¬ j < 4 by omega, hj] using hsub

/-- Canonical row nodes are one adjacent prefix of the strict orbit. -/
def MemoryOrbitAligned {h : ℕ}
    (nodes : Fin R.problem.cfg.memRows → F)
    (orbit : StrictOrbitDomain F 3 h) : Prop :=
  ∀ i : Fin R.problem.cfg.memRows, ∀ hi : (i : ℕ) + 1 < R.problem.cfg.memRows,
    nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω

/-- Explicit non-pole premise used by the sampled response inverse gate. -/
def MemoryDenominatorsSafe (A : SampledIOSameExecutionAssignment R p) : Prop :=
  ∀ i : Fin R.problem.cfg.memRows,
    responseActive (K := K) (R.problem.exec.memoryPubAt i).ver = 1 →
      responseDenominator A i ≠ 0

/-- Every active memory response denominator is safe under the sampled assignment's exact
pole-hit exclusion. The record is taken from the same execution row and then identified with the
sampled response list; no positional memory lookup is introduced. -/
theorem memoryDenominatorsSafe_of_sampled
    (A : SampledIOSameExecutionAssignment R p) :
    MemoryDenominatorsSafe A := by
  intro i hactive hzero
  have hver : (R.problem.exec.memoryPubAt i).ver = true := by
    cases hs : (R.problem.exec.memoryPubAt i).ver <;>
      simp [responseActive, hs] at hactive ⊢
  have hver' : (R.problem.exec.memoryRowAt i).2.2.ver = true := by
    simpa [ExactExecution.memoryPubAt] using hver
  have hraw :
      (R.problem.exec.memoryPubAt i).mem ∈
        R.problem.exec.memoryRows.flatMap
          (fun row => MemoryTable.responseRecords row.2.2) := by
    rw [List.mem_flatMap]
    refine ⟨R.problem.exec.memoryRowAt i, ?_, ?_⟩
    · exact List.get_mem _ _
    · simp [ExactExecution.memoryPubAt, MemoryTable.responseRecords, hver']
  have hencoded :
      NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
          (R.problem.exec.memoryPubAt i).cprime ∈
        R.problem.exec.derivedResponseIO := by
    rw [ExactExecution.derivedResponseIO_eq_memoryRows]
    refine List.mem_flatMap.mpr ⟨R.problem.exec.memoryRowAt i, List.get_mem _ _, ?_⟩
    simp [ExactExecution.memoryPubAt, hver']
  have hst : (R.problem.exec.memoryPubAt i).st = .read_root := by
    have h := A.honestVer _ (List.get_mem R.problem.exec.memoryRows
      ⟨i, by rw [R.problem.exec.memoryRows_length]; exact i.isLt⟩)
    have h' : (R.problem.exec.memoryRowAt i).2.2.ver =
        decide ((R.problem.exec.memoryRowAt i).2.2.st = MemoryTable.MState.read_root) := h
    rw [hver'] at h'
    simpa [ExactExecution.memoryPubAt] using h'.symm
  have hrec := rowRecord10_of_active R i (Or.inl hst)
  apply A.ioGood10
  simp only [FiniteIO.IOFailureEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine Or.inr (Or.inl ?_)
  simp only [FiniteIO.IOPoleHitEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨RecordCarrier.extRec R.problem.exec.derivedRequestIO
      (NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
      (R.problem.exec.memoryPubAt i).cprime), ?_, ?_⟩
  · refine List.mem_append_right _ ?_
    exact List.mem_map.mpr ⟨_, hencoded, rfl⟩
  · rw [← hrec]
    simpa [responseDenominator, FiniteIO.compress] using hzero

theorem mergedMemoryConstraints_reads_intermediate (c : Expr)
    (hc : c ∈ mergedMemoryConstraints (K := K))
    (hinter : (VarKind.traceCur, 31) ∈ exprVariableSupport c ∨
      (VarKind.traceCur, 32) ∈ exprVariableSupport c) :
    c = MemoryFactorizationScope.mergedGate (K := K) 23 ∨
      c = MemoryFactorizationScope.mergedGate (K := K) 24 := by
  rw [mergedMemoryConstraints, List.mem_append, List.mem_append] at hc
  rcases hc with hfront | hcore
  · rcases hfront with hsv | hz
    · simp only [memSvExprs, List.mem_append, List.mem_singleton] at hsv
      rcases hsv with hsv | rfl
      · simp only [memSvBoolExprs, allMStates, List.mem_map] at hsv
        obtain ⟨st, _, rfl⟩ := hsv
        cases st <;> (exfalso; revert hinter; decide)
      · exfalso; revert hinter; decide
    · simp only [List.mem_singleton] at hz
      obtain rfl := hz
      exfalso; revert hinter; decide
  · simp only [mergedMemoryCore, List.mem_map] at hcore
    obtain ⟨q, hq, rfl⟩ := hcore
    have hlt : q < 27 := by
      have hq' : q ∈ List.range 27 := (mergedCoreOrder_perm_range).mem_iff.mp hq
      simpa [List.mem_range] using hq'
    interval_cases q <;> first
      | exact Or.inl rfl
      | exact Or.inr rfl
      | (exfalso
         dsimp only [MemoryFactorizationScope.mergedGate, gateByM,
           MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock,
           MemoryFactorizationScope.blockDecompose, MemoryFactorizationScope.blockHalt,
           MemoryFactorizationScope.blockReadRoot, MemoryFactorizationScope.blockVerifyChild,
           List.getD, getElem?, List.get?Internal, Option.getD,
           MemoryFactorizationScope.lamScaleE, MemoryFactorizationScope.lamE,
           MemoryFactorizationScope.recC', tc, mopCol, mPt, mLc, mRc, mMem, fpCol, mrCol,
           mconsExpr, chl, poleExpr, recRLCExpr, exprVariableSupport] at hinter
         simp only [Finset.mem_union, Finset.mem_singleton, Prod.mk.injEq,
           eq_self_iff_true, true_and, and_true, Finset.notMem_empty] at hinter
         norm_num at hinter)

/-- Non-overlaid merged sources vanish.  Classes `23`/`24` read the overlaid
roles `27`/`28` and are *not* claimed here: their paper form is
`canonical_paperAggregator` (sampled-role + PRL), not DeployedRow. -/
theorem canonical_memoryRowSources
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (hlam : ∀ i, (R.problem.exec.memoryPubAt i).lambda =
      (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    ∀ e ∈ memoryRowSources (K := K),
      e ≠ (MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst →
      e ≠ (MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst →
      e.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) = 0 := by
  intro e he h23 h24
  unfold memoryRowSources at he
  rw [List.mem_map] at he
  obtain ⟨c, hc, rfl⟩ := he
  rw [Expr.eval_subst]
  have hexact := mergedMemoryConstraints_eval_zero _ (exact_memoryAIR_sources P hlam i) c hc
  have h23c : c ≠ MemoryFactorizationScope.mergedGate (K := K) 23 := fun hc23 => h23 (by rw [hc23])
  have h24c : c ≠ MemoryFactorizationScope.mergedGate (K := K) 24 := fun hc24 => h24 (by rw [hc24])
  rw [← hexact]
  refine eval_eq_of_support_agree (exactMemoryRowEnv A i)
      (Env.ofSubst memorySubst (canonicalGatheredEnv A nodes b chalVal pubVal orbit i))
      c ?_
  intro v hv
  match v with
  | (VarKind.traceCur, j) =>
      by_cases hinter : j = 31 ∨ j = 32
      · have hmem : (VarKind.traceCur, 31) ∈ exprVariableSupport c ∨
            (VarKind.traceCur, 32) ∈ exprVariableSupport c :=
          hinter.elim (fun h31 => Or.inl (by simpa [h31] using hv))
            (fun h32 => Or.inr (by simpa [h32] using hv))
        have hagg : c = MemoryFactorizationScope.mergedGate (K := K) 23 ∨
            c = MemoryFactorizationScope.mergedGate (K := K) 24 :=
          mergedMemoryConstraints_reads_intermediate c hc hmem
        exact hagg.elim (fun h => (h23c h).elim) (fun h => (h24c h).elim)
      · have htr := canonical_memorySubst_trace A nodes hnodes b chalVal pubVal orbit pins i j
          ⟨fun h => hinter (Or.inl h), fun h => hinter (Or.inr h)⟩
        simpa [envAt] using htr
  | (VarKind.traceNext, _) =>
      simp [envAt, Env.ofSubst, memorySubst, Expr.eval, exactMemoryRowEnv, memoryEnvFull]
  | (VarKind.challenge, j) =>
      simp [envAt]
      by_cases hj : j < 3
      · have hp := pins.memoryChallenge ⟨j, hj⟩
        simp only [envAt, Env.ofSubst, memorySubst, hj, if_pos hj, Expr.eval]
        conv_lhs =>
          simp only [canonicalGatheredEnv, gatherEnv, canonicalPhysicalEnv, envOfTrace,
            memorySourceTemplate_col0, memoryCol0]
        have hsame : (exactMemoryRowEnv A i).chal j =
            (exactMemoryRowEnv A ⟨0, R.problem.cfg.memRows_pos⟩).chal j := by
          rcases (show j = 0 ∨ j = 1 ∨ j = 2 by omega) with rfl | rfl | rfl <;>
            simp [exactMemoryRowEnv, memoryEnvFull]
        rw [hsame]
        exact hp
      · by_cases h8 : j = 8
        · subst h8
          simp [Env.ofSubst, memorySubst, Expr.eval]
          have hcol :
              (memorySourceTemplate b).col0 3 .challenge 8 = 6 + 3 * 8 := by
            rw [memorySourceTemplate_col0]; rfl
          change (∑ k : Fin 3,
              chalVal ((memorySourceTemplate b).col0 3 .challenge 8 + (k : ℕ)) • b k) =
            (exactMemoryRowEnv A i).chal 8
          simp only [hcol]
          rw [pins.sampledLambda, exactMemoryRowEnv_chal_lambda,
            exactMemoryRowEnv_chal_lambda]
          exact (hlam i).symm
        · rw [exactMemoryRowEnv_chal_ge3 A i j (by omega) h8]
          simp [Env.ofSubst, memorySubst, hj, h8, Expr.eval]
  | (VarKind.publicVal, _) =>
      simp [envAt, Env.ofSubst, memorySubst, Expr.eval, exactMemoryRowEnv, memoryEnvFull]

theorem canonical_memoryChainSource
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows) :
    memoryChainSource.eval
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) = 0 := by
  have hlast := canonical_gather_sampled_current
    A nodes hnodes b chalVal pubVal orbit i (11 : Fin 14) (by decide)
  have hlast' :
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 =
        lastMaskK (K := K) i := by
    simpa [extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue] using hlast
  by_cases hi : (i : ℕ) + 1 < R.problem.cfg.memRows
  · have hcur := canonical_icur A nodes hnodes b chalVal pubVal orbit i
    have hnext := canonical_gather_table_next A nodes hnodes b chalVal pubVal orbit
      i hi (halign i hi) (.inr (.inr (.inr (0 : Fin 4))))
    simp [extensionEquiv_apply, extensionIndex] at hnext
    simp only [memoryChainSource, notLastE, lastE, Trans.icurChainExpr,
      Reified.tc, Trans.tn, Expr.subst, Expr.eval, memoryChainSubst, extVar]
    norm_num [Expr.eval]
    rw [hlast', hcur, hnext]
    exact Or.inr (sub_eq_zero.mpr rfl)
  · have hilast : (i : ℕ) + 1 = R.problem.cfg.memRows := by
      omega
    simp only [memoryChainSource, notLastE, lastE, Trans.icurChainExpr,
      Reified.tc, Trans.tn, Expr.subst, Expr.eval, memoryChainSubst, extVar]
    norm_num [Expr.eval]
    rw [hlast']
    simp [lastMaskK, hilast]

theorem exactMemoryWalkRowEnv_trace_ge7
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) (j : ℕ) (hj : 7 ≤ j) :
    (exactMemoryWalkRowEnv A i).trace j = 0 := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hj
  simp [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked, Nat.add_comm]

theorem canonical_physical_rootMask
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 153 =
      if (i : ℕ) < R.problem.cfg.kMem then 1 else 0 := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (by decide : (153 : ℕ) < 182)]
  rw [canonicalSourceTrace_root_fixed]
  exact rootRowMask_eval nodes R.problem.cfg.kMem hnodes i

theorem canonical_physical_rootMask_next
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows)
    (hsucc : nodes ⟨(i : ℕ) + 1, hi⟩ = nodes i * orbit.ω) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).traceNext 153 =
      if (i : ℕ) + 1 < R.problem.cfg.kMem then 1 else 0 := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (by decide : (153 : ℕ) < 182)]
  have hsucc' : nodes ⟨(i : ℕ) + 1, hi⟩ = orbit.ω * nodes i := by
    simpa [mul_comm] using hsucc
  rw [← hsucc', canonicalSourceTrace_root_fixed]
  exact rootRowMask_eval nodes R.problem.cfg.kMem hnodes ⟨(i : ℕ) + 1, hi⟩

theorem canonical_physical_dequeueMask
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154 =
      if (i : ℕ) + 1 = R.problem.cfg.memRows then 0
      else if (i : ℕ) + 1 < R.problem.cfg.kMem then 0
      else 1 := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (by decide : (154 : ℕ) < 182)]
  rw [canonicalSourceTrace_dequeue_fixed]
  exact dequeueRowMask_eval nodes R.problem.cfg.kMem hnodes i

theorem canonical_physical_dequeue_mirror
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (k : Fin 3) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace (174 + (k : ℕ)) =
      coord b (1 : K) k *
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154 := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (by omega : 174 + (k : ℕ) < 182), dif_pos (by decide : (154 : ℕ) < 182)]
  rw [canonicalSourceTrace_dequeue_mirror, canonicalSourceTrace_dequeue_fixed]
  simp [dequeueRowMask_eval nodes R.problem.cfg.kMem hnodes i]

theorem canonical_gather_dequeueMask
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 56 =
      algebraMap F K
        ((canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154) := by
  have hcol : (memorySourceTemplate b).col0 3 .traceCur 56 = 174 := by
    rw [memorySourceTemplate_col0]; rfl
  simp only [canonicalGatheredEnv, gatherEnv]
  rw [hcol]
  have hk (k : Fin 3) :=
    canonical_physical_dequeue_mirror A nodes hnodes b chalVal pubVal orbit i k
  simp only [hk]
  have h1 : (∑ k : Fin 3, coord b (1 : K) k • b k) = (1 : K) := b.sum_repr (1 : K)
  calc
    (∑ k : Fin 3,
        (coord b (1 : K) k *
          (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154) • b k)
      = (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154 •
          (∑ k : Fin 3, coord b (1 : K) k • b k) := by
        simp [mul_comm, smul_smul, Finset.smul_sum]
    _ = (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154 • (1 : K) := by
        rw [h1]
    _ = algebraMap F K
          ((canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154) := by
        simp [Algebra.smul_def]

theorem canonical_dequeueMaskBindingCoord_zero
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (k : Fin 3) :
    (maskBindingCoord b 56 154 k).eval
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  have hmir := canonical_physical_dequeue_mirror A nodes hnodes b chalVal pubVal orbit i k
  simp only [maskBindingCoord, CoeffExpr.eval, extCoord, bcur]
  change
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace (174 + (k : ℕ)) -
      coord b (1 : K) k *
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154 = 0
  rw [hmir, sub_self]

theorem canonical_walkBoundarySubst_env
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    Env.ofSubst walkBoundarySubst
        (withRootMaskLift
          (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
          (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)) =
      exactMemoryWalkRowEnv A i := by
  apply env_ext <;> intro j
  · simp only [Env.ofSubst]
    by_cases hj : j < 6
    · have hw := canonical_gather_walk_current
        A nodes hnodes b chalVal pubVal orbit i ⟨j, hj⟩
      have hne : 31 + j ≠ 153 ∧ 31 + j ≠ 154 := by omega
      simp [walkBoundarySubst, hj, extVar, Expr.eval, withRootMaskLift, hne.1, hne.2,
        extensionEquiv_apply, extensionIndex]
      exact hw
    · by_cases hj6 : j = 6
      · subst j
        have hrm := canonical_physical_rootMask A nodes hnodes b chalVal pubVal orbit i
        have hrmE : (rootMaskE).eval
            (withRootMaskLift
              (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
              (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)) =
            algebraMap F K
              ((canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 153) := by
          simp [rootMaskE, extVar, Expr.eval, withRootMaskLift]
        have hsub : walkBoundarySubst .traceCur 6 = rootMaskE := by
          simp [walkBoundarySubst]
        rw [hsub, hrmE, hrm]
        simp only [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked, Nock.Walk.rootMask]
        split_ifs <;> simp [map_one, map_zero] <;> omega
      · rw [exactMemoryWalkRowEnv_trace_ge7 A i j (by omega)]
        simp [walkBoundarySubst, hj, hj6, Expr.eval]
  · simp [Env.ofSubst, walkBoundarySubst, Expr.eval,
      exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
  · simp only [Env.ofSubst]
    rcases j with _ | j
    · simp only [walkBoundarySubst, Expr.eval, withRootMaskLift]
      change (∑ k : Fin 3, chalVal (6 + 3 * 3 + (k : ℕ)) • b k) =
        R.memoryWalkAlpha
      exact pins.walkChallenge
    · simp [walkBoundarySubst, Expr.eval, exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
  · simp only [Env.ofSubst]
    rcases j with _ | _ | j
    · simp only [walkBoundarySubst, Expr.eval, withRootMaskLift]
      change (∑ k : Fin 3, pubVal (6 + 3 * 0 + (k : ℕ)) • b k) =
        R.memoryWalkAlpha ^ R.problem.cfg.kMem
      exact pins.walkInitialCount
    · simp [walkBoundarySubst, Expr.eval, withRootMaskLift,
        exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
    · simp [walkBoundarySubst, Expr.eval, exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]

theorem canonical_walkSubst_env
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows)
    (hi : (i : ℕ) + 1 < R.problem.cfg.memRows) :
    Env.ofSubst walkSubst
        (withRootMaskLift
          (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
          (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)) =
      Trans.twoRow (exactMemoryWalkRowEnv A i)
        (exactMemoryWalkRowEnv A ⟨(i : ℕ) + 1, hi⟩) := by
  apply env_ext <;> intro j
  · simp only [Env.ofSubst, Trans.twoRow]
    by_cases hj : j < 6
    · have hw := canonical_gather_walk_current
        A nodes hnodes b chalVal pubVal orbit i ⟨j, hj⟩
      have hne : 31 + j ≠ 153 ∧ 31 + j ≠ 154 := by omega
      simpa [walkSubst, hj, extVar, Expr.eval, withRootMaskLift, hne.1, hne.2,
        extensionEquiv_apply, extensionIndex] using hw
    · by_cases hj6 : j = 6
      · subst j
        have hrm := canonical_physical_rootMask A nodes hnodes b chalVal pubVal orbit i
        have hrmE : (rootMaskE).eval
            (withRootMaskLift
              (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
              (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)) =
            algebraMap F K
              ((canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 153) := by
          simp [rootMaskE, extVar, Expr.eval, withRootMaskLift]
        have hsub : walkSubst .traceCur 6 = rootMaskE := by
          simp [walkSubst]
        rw [hsub, hrmE, hrm]
        simp only [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked, Nock.Walk.rootMask]
        split_ifs <;> simp [map_one, map_zero] <;> omega
      · rw [exactMemoryWalkRowEnv_trace_ge7 A i j (by omega)]
        simp [walkSubst, hj, hj6, Expr.eval]
  · simp only [Env.ofSubst, Trans.twoRow]
    by_cases hj : j < 6
    · have hw := canonical_gather_walk_next
        A nodes hnodes b chalVal pubVal orbit i hi (halign i hi) ⟨j, hj⟩
      have hne : 31 + j ≠ 153 ∧ 31 + j ≠ 154 := by omega
      simpa [walkSubst, hj, extVar, Expr.eval, withRootMaskLift, hne.1, hne.2,
        extensionEquiv_apply, extensionIndex] using hw
    · by_cases hj6 : j = 6
      · subst j
        have hrm := canonical_physical_rootMask_next A nodes hnodes b chalVal pubVal
          orbit i hi (halign i hi)
        have hrmE : (rootMaskENext).eval
            (withRootMaskLift
              (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
              (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)) =
            algebraMap F K
              ((canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).traceNext 153) := by
          simp [rootMaskENext, extVar, Expr.eval, withRootMaskLift]
        have hsub : walkSubst .traceNext 6 = rootMaskENext := by
          simp [walkSubst]
        rw [hsub, hrmE, hrm]
        simp only [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked, Nock.Walk.rootMask]
        split_ifs <;> simp [map_one, map_zero] <;> omega
      · rw [exactMemoryWalkRowEnv_trace_ge7 A ⟨(i : ℕ) + 1, hi⟩ j (by omega)]
        simp [walkSubst, hj, hj6, Expr.eval]
  · simp only [Env.ofSubst, Trans.twoRow]
    rcases j with _ | j
    · simp only [walkSubst, Expr.eval, withRootMaskLift]
      change (∑ k : Fin 3, chalVal (6 + 3 * 3 + (k : ℕ)) • b k) =
        R.memoryWalkAlpha
      exact pins.walkChallenge
    · simp [walkSubst, Expr.eval, exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
  · simp only [Env.ofSubst, Trans.twoRow]
    rcases j with _ | _ | j
    · simp only [walkSubst, Expr.eval, withRootMaskLift]
      change (∑ k : Fin 3, pubVal (6 + 3 * 0 + (k : ℕ)) • b k) =
        R.memoryWalkAlpha ^ R.problem.cfg.kMem
      exact pins.walkInitialCount
    · simp [walkSubst, Expr.eval, withRootMaskLift,
        exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
    · simp [walkSubst, Expr.eval, exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]

theorem canonical_walkSources
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows) :
    (∀ e ∈ walkBoundarySources,
      e.eval (withRootMaskLift
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)) = 0) ∧
    (∀ e ∈ walkTransitionSources,
      e.eval (withRootMaskLift
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)) = 0) := by
  have hw := exact_forest_walk_sources_masked P
  constructor
  · intro e he
    rw [walkBoundarySources, List.mem_map] at he
    obtain ⟨g, hg, rfl⟩ := he
    have hfirst := canonical_gather_sampled_current
      A nodes hnodes b chalVal pubVal orbit i (10 : Fin 14) (by decide)
    by_cases hi0 : (i : ℕ) = 0
    · have hi : i = ⟨0, R.problem.cfg.memRows_pos⟩ := Fin.ext hi0
      subst i
      have h47 :
          (withRootMaskLift
              (canonicalGatheredEnv A nodes b chalVal pubVal orbit
                ⟨0, R.problem.cfg.memRows_pos⟩)
              (canonicalPhysicalEnv A nodes b chalVal pubVal orbit
                ⟨0, R.problem.cfg.memRows_pos⟩)).trace 47 =
            (canonicalGatheredEnv A nodes b chalVal pubVal orbit
              ⟨0, R.problem.cfg.memRows_pos⟩).trace 47 := by
        simp [withRootMaskLift]
      simp only [Expr.eval, Expr.eval_subst, firstE, extVar]
      rw [h47]
      rw [show (canonicalGatheredEnv A nodes b chalVal pubVal orbit
          ⟨0, R.problem.cfg.memRows_pos⟩).trace 47 = 1 by
        simpa [extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
          firstMaskK] using hfirst]
      rw [canonical_walkBoundarySubst_env A nodes hnodes b chalVal pubVal orbit
        pins ⟨0, R.problem.cfg.memRows_pos⟩, one_mul]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl | rfl
      · exact hw.2.1
      · exact hw.2.2.1
      · exact hw.2.2.2.1
    · simp only [Expr.eval, firstE, extVar, withRootMaskLift]
      rw [show (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 47 = 0 by
        simpa [extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
          firstMaskK, hi0] using hfirst]
      simp
  · intro e he
    simp only [walkTransitionSources, walkLnCountTransitionSources, List.mem_append,
      List.mem_map, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at he
    have hlast := canonical_gather_sampled_current
      A nodes hnodes b chalVal pubVal orbit i (11 : Fin 14) (by decide)
    rcases he with ⟨g, hg, rfl⟩ | rfl
    · by_cases hi : (i : ℕ) + 1 < R.problem.cfg.memRows
      · have h48 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 = 0 := by
          simpa [extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
            lastMaskK, show (i : ℕ) + 1 ≠ R.problem.cfg.memRows by omega] using hlast
        have h48lift :
            (withRootMaskLift
                (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
                (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)).trace 48 =
              (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 := by
          simp [withRootMaskLift]
        simp only [Expr.eval, Expr.eval_subst, notLastE, lastE, extVar]
        rw [h48lift, h48]
        simp only [sub_zero, map_one, one_mul]
        rw [canonical_walkSubst_env A nodes hnodes b chalVal pubVal orbit pins halign i hi]
        have hstep := hw.2.2.2.2 ((i : ℕ) + 1) (by omega) (by omega)
        have hg' : g = Trans.walkLnStep ∨ g = Trans.walkCountStep := by
          simpa [List.mem_cons, List.not_mem_nil] using hg
        rcases hg' with rfl | rfl
        · simpa [Trans.walkStepMasked, exactMemoryWalkRowEnv] using hstep.1
        · simpa [Trans.walkStepMasked, exactMemoryWalkRowEnv] using hstep.2.1
      · have hilast : (i : ℕ) + 1 = R.problem.cfg.memRows := by omega
        have h48 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 = 1 := by
          simpa [extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
            lastMaskK, hilast] using hlast
        have h48lift :
            (withRootMaskLift
                (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
                (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)).trace 48 =
              (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 := by
          simp [withRootMaskLift]
        simp only [Expr.eval, notLastE, lastE, extVar]
        rw [h48lift, h48]
        simp
    · have hdm := canonical_physical_dequeueMask A nodes hnodes b chalVal pubVal orbit i
      by_cases hi : (i : ℕ) + 1 < R.problem.cfg.memRows
      · have hstep := hw.2.2.2.2 ((i : ℕ) + 1) (by omega) (by omega)
        have hacc := (Trans.reified_walk_acc_stepMasked_sound
          (Nock.Walk.rootMask (K := K) R.problem.cfg.kMem) ((i : ℕ) + 1)).1 hstep.2.2
        have h48 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 = 0 := by
          simpa [extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
            lastMaskK, show (i : ℕ) + 1 ≠ R.problem.cfg.memRows by omega] using hlast
        have henv := canonical_walkSubst_env A nodes hnodes b chalVal pubVal orbit
          pins halign i hi
        have hdmVal : algebraMap F K
            ((canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154) =
              1 - Nock.Walk.rootMask (K := K) R.problem.cfg.kMem ((i : ℕ) + 1 + 1) := by
          rw [hdm]
          simp [Nock.Walk.rootMask]
          split_ifs <;> simp <;> omega
        have h48lift :
            (withRootMaskLift
                (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
                (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)).trace 48 =
              (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 := by
          simp [withRootMaskLift]
        have h56lift :
            (withRootMaskLift
                (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
                (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)).trace 56 =
              (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 56 := by
          simp [withRootMaskLift]
        have h56val := canonical_gather_dequeueMask A nodes hnodes b chalVal pubVal orbit i
        simp only [walkAccStepHosted, Expr.eval, Expr.eval_subst, dequeueMaskE, notLastE,
          lastE, extVar]
        rw [h48lift, h48, h56lift, h56val, hdmVal, henv]
        simp only [sub_zero, map_one, one_mul, Expr.eval, Trans.tn, Reified.tc, Trans.twoRow]
        · have h0 : (exactMemoryWalkRowEnv A ⟨(i : ℕ) + 1, hi⟩).trace 0 =
              A.exact.memoryWalk.ln ((i : ℕ) + 1 + 1) := by
            simp [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
          have h3 : (exactMemoryWalkRowEnv A ⟨(i : ℕ) + 1, hi⟩).trace 3 =
              Nock.Walk.curCol R.memoryNodeVal R.memoryWalkRows ((i : ℕ) + 1 + 1) := by
            simp [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
          have h2n : (exactMemoryWalkRowEnv A ⟨(i : ℕ) + 1, hi⟩).trace 2 =
              memoryAccInGate A ((i : ℕ) + 1 + 1) := by
            simp [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
          have h2c : (exactMemoryWalkRowEnv A i).trace 2 = memoryAccInGate A ((i : ℕ) + 1) := by
            simp [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
          have h1c : (exactMemoryWalkRowEnv A i).trace 1 =
              A.exact.memoryWalk.count ((i : ℕ) + 1) := by
            simp [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
          have h4n : (exactMemoryWalkRowEnv A ⟨(i : ℕ) + 1, hi⟩).trace 4 =
              Trans.walkCC (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
                (Nock.Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha ((i : ℕ) + 1 + 1) := by
            simp [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked]
          rw [h0, h3, h2n, h2c, h1c, h4n]
          have hcw := Trans.c_mul_walkCC (Nock.Walk.chldCol R.memoryNodeVal R.memoryWalkRows)
            (Nock.Walk.foCol R.memoryWalkRows) R.memoryWalkAlpha
            (A.exact.memoryWalk.count ((i : ℕ) + 1)) ((i : ℕ) + 1 + 1)
          rw [hcw]
          linear_combination hacc
      · have hilast : (i : ℕ) + 1 = R.problem.cfg.memRows := by omega
        have hdm0 : (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 154 = 0 := by
          simpa [hilast] using hdm
        have h48 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 = 1 := by
          simpa [extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
            lastMaskK, hilast] using hlast
        have h56val := canonical_gather_dequeueMask A nodes hnodes b chalVal pubVal orbit i
        simp [walkAccStepHosted, walkSubst, dequeueMaskE, notLastE, lastE, extVar,
          Expr.subst, Expr.eval, withRootMaskLift, Trans.tn, Reified.tc, hdm0, h48,
          h56val, map_zero]

/-- Honest `ver`: a `ver = 1` row is a `read_root` row. -/
theorem st_read_root_of_ver
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) (hver : (R.problem.exec.memoryRowAt i).2.2.ver = true) :
    (R.problem.exec.memoryPubAt i).st = .read_root := by
  have h := A.honestVer _ (List.get_mem R.problem.exec.memoryRows
    ⟨i, by rw [R.problem.exec.memoryRows_length]; exact i.isLt⟩)
  have h' : (R.problem.exec.memoryRowAt i).2.2.ver =
      decide ((R.problem.exec.memoryRowAt i).2.2.st = MemoryTable.MState.read_root) := h
  rw [hver] at h'
  simpa [ExactExecution.memoryPubAt] using h'.symm

theorem responseContribution_eq_ioRowTerm
    (A : SampledIOSameExecutionAssignment R p)
    (i : Fin R.problem.cfg.memRows) :
    responseContribution A i =
      RowLayout.ioRowTerm A.compress10 (R.problem.exec.memoryRowAt i) := by
  cases hs : (R.problem.exec.memoryRowAt i).2.2.ver
  · simp [responseContribution, responseActive, RowLayout.ioRowTerm, RowLayout.ioSelector,
      ExactExecution.memoryPubAt, hs]
  · have hrec := rowRecord10_of_active R i (Or.inl (st_read_root_of_ver A i hs))
    simp [responseContribution, responseActive, safeResponseDenominator,
      responseDenominator, RowLayout.ioRowTerm, RowLayout.ioSelector,
      ExactExecution.memoryPubAt, hs, hrec, SampledIOSameExecutionAssignment.compress10]

theorem canonical_sampledSources
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (hsafe : MemoryDenominatorsSafe A)
    (i : Fin R.problem.cfg.memRows) :
    ∀ e ∈ sampledSources,
      e.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) = 0 := by
  let E := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hpub2 : E.pub 2 = A.witness10.terminal := by
    change (∑ k : Fin 3, pubVal ((memorySourceTemplate b).col0 3 .publicVal 2 + (k : ℕ)) • b k) =
      A.witness10.terminal
    exact pins.requests
  have hv : ∀ q : Fin 14, (q : ℕ) ≠ 12 →
      E.trace (37 + q) = sampledMemoryRoleValue A i q :=
    fun q hq => canonical_gather_sampled_index A nodes hnodes b chalVal pubVal orbit i q hq
  have hsafe' : safeResponseDenominator A i ≠ 0 := by
    by_cases hs : (R.problem.exec.memoryPubAt i).ver = true
    · have ha : responseActive (K := K) (R.problem.exec.memoryPubAt i).ver = 1 := by
        simp [responseActive, hs]
      simpa [safeResponseDenominator, ha] using hsafe i ha
    · simp [safeResponseDenominator, responseActive, hs]
  have hstep :
      responseAccumulator A ((i : ℕ) + 1) =
        responseAccumulator A i + responseContribution A i := by
    rw [responseAccumulator, responseAccumulator,
      RowLayout.coResidentAcc_succ A.compress10 R.problem.exec.memoryRows
        (by simpa using i.isLt)]
    rw [responseContribution_eq_ioRowTerm A i]
    let ii : Fin R.problem.exec.memoryRows.length :=
      Fin.cast R.problem.exec.memoryRows_length.symm i
    have hrow := R.problem.exec.memoryRowAt_cast ii
    have hii : Fin.cast R.problem.exec.memoryRows_length ii = i := by
      apply Fin.ext
      rfl
    rw [hii] at hrow
    simpa [ii] using congrArg (RowLayout.ioRowTerm A.compress10) hrow.symm
  have hterminal :
      responseAccumulator A R.problem.cfg.memRows = A.witness10.terminal := by
    rw [responseAccumulator]
    rw [← R.problem.exec.memoryRows_length]
    rw [show A.compress10 = fun v => FiniteIO.compress A.sampled.coins
        (RecordCarrier.extRec R.problem.exec.derivedRequestIO v) from rfl]
    rw [RowLayout.coResidentAcc_terminal_eq_responseAcc_map R.problem.exec
      A.witness10_accepts (RecordCarrier.extRec R.problem.exec.derivedRequestIO) rfl]
    exact A.witness10_accepts.responseTerm
  dsimp [E] at hv
  have hv0 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 37 =
      sampledMemoryRoleValue A i 0 := by simpa using hv (0 : Fin 14) (by decide)
  have hv1 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 38 =
      sampledMemoryRoleValue A i 1 := by simpa using hv (1 : Fin 14) (by decide)
  have hv2 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 39 =
      sampledMemoryRoleValue A i 2 := by simpa using hv (2 : Fin 14) (by decide)
  have hv3 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 40 =
      sampledMemoryRoleValue A i 3 := by simpa using hv (3 : Fin 14) (by decide)
  have hv5 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 42 =
      sampledMemoryRoleValue A i 5 := by simpa using hv (5 : Fin 14) (by decide)
  have hv6 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 43 =
      sampledMemoryRoleValue A i 6 := by simpa using hv (6 : Fin 14) (by decide)
  have hv7 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 44 =
      sampledMemoryRoleValue A i 7 := by simpa using hv (7 : Fin 14) (by decide)
  have hv8 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 45 =
      sampledMemoryRoleValue A i 8 := by simpa using hv (8 : Fin 14) (by decide)
  have hv10 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 47 =
      sampledMemoryRoleValue A i 10 := by simpa using hv (10 : Fin 14) (by decide)
  have hv11 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 =
      sampledMemoryRoleValue A i 11 := by simpa using hv (11 : Fin 14) (by decide)
  have hv13 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 50 =
      sampledMemoryRoleValue A i 13 := by simpa using hv (13 : Fin 14) (by decide)
  intro e he
  simp only [sampledSources, List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simp only [Expr.eval, extVar]
    rw [hv13, hv1]
    exact sub_eq_zero.mpr (by
      simpa [sampledMemoryRoleValue] using mul_inv_cancel₀ hsafe')
  · simp only [Expr.eval, extVar]
    rw [hv2]
    cases hs : (R.problem.exec.memoryPubAt i).ver <;>
      simp [sampledMemoryRoleValue, responseActive, hs]
  · simp only [Expr.eval, extVar]
    rw [hv5, hv2, hv1]
    simp [sampledMemoryRoleValue, responseContribution]
  · simp only [Expr.eval, extVar]
    rw [hv7, hv6, hv5]
    exact sub_eq_zero.mpr hstep
  · simp only [Expr.eval, extVar]
    rw [hv13, hv2, hv0]
    simp [sampledMemoryRoleValue, safeResponseDenominator]
  · simp only [Expr.eval, extVar]
    rw [hv10]
    by_cases hi0 : (i : ℕ) = 0 <;>
      simp [sampledMemoryRoleValue, firstMaskK, hi0]
  · simp only [Expr.eval, extVar]
    rw [hv11]
    by_cases hilast : (i : ℕ) + 1 = R.problem.cfg.memRows <;>
      simp [sampledMemoryRoleValue, lastMaskK, hilast]
  · simp only [Expr.eval, extVar]
    rw [hv10, hv6]
    by_cases hi0 : (i : ℕ) = 0
    · simp [sampledMemoryRoleValue, firstMaskK, hi0, responseAccumulator,
        RowLayout.coResidentAcc_zero]
    · simp [sampledMemoryRoleValue, firstMaskK, hi0]
  · simp only [Expr.eval, extVar]
    rw [hv11, hv7, hv3]
    by_cases hilast : (i : ℕ) + 1 = R.problem.cfg.memRows
    · simpa [sampledMemoryRoleValue, lastMaskK, hilast] using
        sub_eq_zero.mpr hterminal
    · simp [sampledMemoryRoleValue, lastMaskK, hilast]
  · -- the terminal binding: role `40` is the terminal, public `2` is the terminal
    simp only [Expr.eval, extVar]
    rw [hv3, hpub2]
    simp [sampledMemoryRoleValue]

/-- **The four endpoint gates vanish on canonical rows.**  Roles `27`/`28` are
the overlay `interResidentAcc` (`canonical_ipre`/`canonical_icur`), not the
table pubs: `ipre(0) = 0` is `interResidentAcc_zero`, and `icur(last) = 0`
is `interResidentAcc_last_of_paired` from PRL. -/
theorem canonical_endpointSources
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows) :
    (∀ e ∈ degreeOneEndpoints,
      e.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) = 0) ∧
    (∀ e ∈ foldedDegreeThreeEndpoints,
      e.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) = 0) := by
  have hforest := exact_forest_walk_sources_masked P
  have hs10 := canonical_gather_sampled_index
    A nodes hnodes b chalVal pubVal orbit i (10 : Fin 14) (by decide)
  have hs4 := canonical_gather_sampled_index
    A nodes hnodes b chalVal pubVal orbit i (4 : Fin 14) (by decide)
  have hs11 := canonical_gather_sampled_index
    A nodes hnodes b chalVal pubVal orbit i (11 : Fin 14) (by decide)
  have hw2 := canonical_gather_walk_current
    A nodes hnodes b chalVal pubVal orbit i (2 : Fin 6)
  have h27 := canonical_ipre A nodes hnodes b chalVal pubVal orbit i
  have h28 := canonical_icur A nodes hnodes b chalVal pubVal orbit i
  constructor
  · intro e he
    simp only [degreeOneEndpoints, List.not_mem_nil] at he
  · intro e he
    simp only [foldedDegreeThreeEndpoints, intermediateInitGate, intermediateTerminalGate,
      List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl
    · simp only [Expr.eval, extVar]
      rw [show (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 41 =
          sampledMemoryRoleValue A i 4 by simpa using hs4]
      by_cases hi0 : (i : ℕ) = 0
      · have hi : i = ⟨0, R.problem.cfg.memRows_pos⟩ := Fin.ext hi0
        subst i
        simpa [sampledMemoryRoleValue, forestInitResidual, firstMaskK,
          exactMemoryWalkRowEnv] using
          hforest.2.2.2.1
      · simp [sampledMemoryRoleValue, forestInitResidual, firstMaskK, hi0]
    · simp only [Expr.eval, extVar]
      rw [show (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 =
          sampledMemoryRoleValue A i 11 by simpa using hs11]
      rw [show (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 33 =
          (exactMemoryWalkRowEnv A i).trace 2 by
        simpa [extensionEquiv_apply, extensionIndex] using hw2]
      by_cases hilast : (i : ℕ) + 1 = R.problem.cfg.memRows
      · have hacc : (exactMemoryWalkRowEnv A i).trace 2 =
            memoryAccInGate A R.problem.cfg.memRows := by
          simp [exactMemoryWalkRowEnv, Trans.walkRowEnvMasked, hilast]
        rw [hacc, memoryAccInGate_last_zero P]
        simp
      · simp [sampledMemoryRoleValue, lastMaskK, hilast]
    · -- `first · ipre`: role `47` is the first-row mask, role `27` is `ipre`.
      simp only [Expr.eval, extVar]
      rw [show (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 47 =
          sampledMemoryRoleValue A i 10 by simpa using hs10, h27]
      by_cases hi0 : (i : ℕ) = 0
      · have hi : i = ⟨0, R.problem.cfg.memRows_pos⟩ := Fin.ext hi0
        subst i
        simp [sampledMemoryRoleValue, firstMaskK, RowLayout.interResidentAcc_zero]
      · simp [sampledMemoryRoleValue, firstMaskK, hi0]
    · -- `last · icur`: role `48` is the last-row mask, role `28` is `icur`.
      simp only [Expr.eval, extVar]
      rw [show (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 48 =
          sampledMemoryRoleValue A i 11 by simpa using hs11, h28]
      by_cases hilast : (i : ℕ) + 1 = R.problem.cfg.memRows
      · have hlen : (i : ℕ) + 1 = R.problem.exec.memoryRows.length := by
          simpa [R.problem.exec.memoryRows_length] using hilast
        simp only [sampledMemoryRoleValue, lastMaskK, if_pos hilast, one_mul]
        rw [hlen, RowLayout.interResidentAcc_last_of_paired _ _ hprl hC]
      · simp [sampledMemoryRoleValue, lastMaskK, hilast]

theorem canonical_baseTransitionGates
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (hsafe : MemoryDenominatorsSafe A)
    (i : Fin R.problem.cfg.memRows) :
    ∀ g ∈ foldedBaseTransitionGates b,
      g.eval (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  have hb0 := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (0 : Fin 6)
  have hb1 := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (1 : Fin 6)
  have hb2 := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (2 : Fin 6)
  have hb3 := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (3 : Fin 6)
  have hb4 := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (4 : Fin 6)
  have hb5 := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (5 : Fin 6)
  have hb0' : (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 0 =
      (encodedRowAt (F := F) A i).base 0 := by simpa using hb0
  have hb1' : (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 1 =
      (encodedRowAt (F := F) A i).base 1 := by simpa using hb1
  have hb2' : (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 2 =
      (encodedRowAt (F := F) A i).base 2 := by simpa using hb2
  have hb3' : (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 3 =
      (encodedRowAt (F := F) A i).base 3 := by simpa using hb3
  have hb4' : (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 4 =
      (encodedRowAt (F := F) A i).base 4 := by simpa using hb4
  have hb5' : (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 5 =
      (encodedRowAt (F := F) A i).base 5 := by simpa using hb5
  let envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hcoord (E : Expr) (hE : E ∈ sampledSources) (k : Fin 3) :
      (coordinateCompile b ((memorySourceTemplate b).col0 3) E k).eval envF = 0 := by
    have hz := canonical_sampledSources A P nodes hnodes b chalVal pubVal orbit
      pins hsafe i E hE
    have hc := coordinateCompile_eval b ((memorySourceTemplate b).col0 3)
      (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF) E k
    change E.eval (gatherEnv b ((memorySourceTemplate b).col0 3) envF) = 0 at hz
    rw [hz, coord_zero] at hc
    exact hc.symm
  intro g hg
  simp only [foldedBaseTransitionGates, List.mem_append] at hg
  rcases hg with hg | hg
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl | rfl
    all_goals
      simp only [CoeffExpr.eval, bbool, bcur, bsum4]
      try rw [hb0']
      try rw [hb1']
      try rw [hb2']
      try rw [hb3']
      try simp only [encodedRowAt, encode, encodeBase, semanticRowAt]
      cases hs : (R.problem.exec.memoryPubAt i).st <;>
        try simp [stateSelector, stateIndex, hs]
    all_goals aesop
  · simp only [semanticBaseTail, List.mem_append] at hg
    rcases hg with hg | hg
    · obtain ⟨k, -, rfl⟩ := List.mem_ofFn.mp hg
      simpa [sampledTerminalCoord, extCoord, coordinateCompile,
        ChipTemplate.col0, ChipTemplate.baseCols, memorySourceTemplate, extVar, envF] using
        hcoord (.Sub (extVar .traceCur 40) (extVar .publicVal 2)) (by simp [sampledSources]) k
    · obtain ⟨k, -, rfl⟩ := List.mem_ofFn.mp hg
      simpa [sampledAccumulatorCoord, extCoord, coordinateCompile,
        ChipTemplate.col0, ChipTemplate.baseCols, memorySourceTemplate, extVar, envF] using
        hcoord
          (.Sub (extVar .traceCur 44)
            (.Add (extVar .traceCur 43) (extVar .traceCur 42)))
          (by simp [sampledSources]) k

/-- Honest vanishing of `readRootVerGate`: selector 0 off `read_root`;
    on `read_root` the honest `ver` is `1` (`hhon`) so coord 0 matches
    `coord b 1 0`. -/
theorem canonical_readRootVerGate
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (i : Fin R.problem.cfg.memRows) :
    (readRootVerGate b).eval
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  have hsel : (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 2 =
      (encodedRowAt (F := F) A i).base 2 := by
    simpa using canonical_base_current A nodes hnodes b chalVal pubVal orbit i (2 : Fin 6)
  have hcol := canonical_extension_coord_current A nodes hnodes b chalVal pubVal orbit i
    ⟨39, by omega⟩ (0 : Fin 3) (by decide) (by decide)
  have hsym : extensionEquiv.symm ⟨39, by omega⟩ =
      (.inr (.inr (.inl ⟨2, by omega⟩)) : ExtensionRole) := by
    apply Equiv.injective extensionEquiv
    simp [extensionEquiv_apply, extensionIndex]
  have hver := hhon (R.problem.exec.memoryRowAt i) (R.problem.exec.memoryRowAt_mem i)
  simp only [readRootVerGate, CoeffExpr.eval, bcur, extCoord]
  rw [hsel, hcol, hsym]
  simp only [encodedRowAt, encode, encodeBase, encodeExtension, semanticRowAt,
    sampledMemoryRoleValue, ExactExecution.memoryPubAt]
  cases hst : (R.problem.exec.memoryRowAt i).2.2.st <;>
    simp [stateSelector, stateIndex, hst, responseActive, hver]

/-- Every coordinate of the promoted masked memory-chain source vanishes on canonical rows. -/
theorem canonical_chainCoord_zero
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows) (k : Fin 3) :
    (chainCoord (F := F) k).eval
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  let envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hb5 := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (5 : Fin 6)
  by_cases hilast : (i : ℕ) + 1 = R.problem.cfg.memRows
  · have hb5last : envF.trace 5 = 1 := by
      rw [show envF.trace 5 = (encodedRowAt (F := F) A i).base 5 by simpa [envF] using hb5]
      simp [encodedRowAt, encode, encodeBase, semanticRowAt, lastMask, hilast]
    simp [chainCoord, CoeffExpr.eval, extCoord, bcur, envF, hb5last]
  · have hb5zero : envF.trace 5 = 0 := by
      rw [show envF.trace 5 = (encodedRowAt (F := F) A i).base 5 by simpa [envF] using hb5]
      simp [encodedRowAt, encode, encodeBase, semanticRowAt, lastMask, hilast]
    have hlast := canonical_gather_sampled_current
      A nodes hnodes b chalVal pubVal orbit i (11 : Fin 14) (by decide)
    have hlastzero : envK.trace 48 = 0 := by
      simpa [envK, extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
        lastMaskK, hilast] using hlast
    have hchain := canonical_memoryChainSource A P nodes hnodes b chalVal pubVal orbit halign i
    have hdiff : envK.trace 28 = envK.traceNext 27 := by
      change memoryChainSource.eval envK = 0 at hchain
      simp [memoryChainSource, notLastE, lastE, Trans.icurChainExpr,
        memoryChainSubst, extVar, Expr.subst, Expr.eval, hlastzero] at hchain
      exact sub_eq_zero.mp hchain
    have hcur :=
      (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF).trace 28 k
    have hnext :=
      (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF).traceNext 27 k
    change envF.trace (90 + (k : ℕ)) = coord b (envK.trace 28) k at hcur
    change envF.traceNext (87 + (k : ℕ)) = coord b (envK.traceNext 27) k at hnext
    have hcoordEq : envF.trace (90 + (k : ℕ)) = envF.traceNext (87 + (k : ℕ)) := by
      rw [hcur, hnext, hdiff]
    simp [chainCoord, CoeffExpr.eval, extCoord, bcur, envF, hb5zero, hcoordEq]

/-- Coordinate-level census for the first extension-mask binding. -/
theorem canonical_firstMaskBindingCoord_zero
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (k : Fin 3) :
    (maskBindingCoord b 47 4 k).eval
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  let envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hcur := (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF).trace 47 k
  change envF.trace (147 + (k : ℕ)) = coord b (envK.trace 47) k at hcur
  have hmask := canonical_gather_sampled_current A nodes hnodes b chalVal pubVal orbit
    i (10 : Fin 14) (by decide)
  have hmaskK : envK.trace 47 =
      algebraMap F K ((encodedRowAt (F := F) A i).base 4) := by
    rw [show envK.trace 47 = sampledMemoryRoleValue A i 10 by
      simpa [envK, extensionEquiv_apply, extensionIndex] using hmask]
    simp [sampledMemoryRoleValue, firstMaskK, encodedRowAt, encode, encodeBase,
      semanticRowAt, firstMask]
  have hbase := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (4 : Fin 6)
  have hlift :
      coord b (algebraMap F K ((encodedRowAt (F := F) A i).base 4)) k =
        coord b (1 : K) k * (encodedRowAt (F := F) A i).base 4 := by
    rw [show algebraMap F K ((encodedRowAt (F := F) A i).base 4) =
      (encodedRowAt (F := F) A i).base 4 • (1 : K) by simp [Algebra.smul_def]]
    simp [coord, mul_comm]
  simp only [maskBindingCoord, CoeffExpr.eval, extCoord, bcur]
  rw [show envF.trace (147 + (k : ℕ)) = coord b (envK.trace 47) k by exact hcur,
    hmaskK, hlift, show envF.trace 4 = (encodedRowAt (F := F) A i).base 4 by
      simpa [envF] using hbase]
  ring

theorem canonical_lastMaskBindingCoord_zero
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (k : Fin 3) :
    (maskBindingCoord b 48 5 k).eval
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  let envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hcur := (isCoordEnv_gather b ((memorySourceTemplate b).col0 3) envF).trace 48 k
  change envF.trace (150 + (k : ℕ)) = coord b (envK.trace 48) k at hcur
  have hmask := canonical_gather_sampled_current A nodes hnodes b chalVal pubVal orbit
    i (11 : Fin 14) (by decide)
  have hmaskK : envK.trace 48 =
      algebraMap F K ((encodedRowAt (F := F) A i).base 5) := by
    rw [show envK.trace 48 = sampledMemoryRoleValue A i 11 by
      simpa [envK, extensionEquiv_apply, extensionIndex] using hmask]
    simp [sampledMemoryRoleValue, lastMaskK, encodedRowAt, encode, encodeBase,
      semanticRowAt, lastMask]
  have hbase := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (5 : Fin 6)
  have hlift :
      coord b (algebraMap F K ((encodedRowAt (F := F) A i).base 5)) k =
        coord b (1 : K) k * (encodedRowAt (F := F) A i).base 5 := by
    rw [show algebraMap F K ((encodedRowAt (F := F) A i).base 5) =
      (encodedRowAt (F := F) A i).base 5 • (1 : K) by simp [Algebra.smul_def]]
    simp [coord, mul_comm]
  simp only [maskBindingCoord, CoeffExpr.eval, extCoord, bcur]
  rw [show envF.trace (150 + (k : ℕ)) = coord b (envK.trace 48) k by exact hcur,
    hmaskK, hlift, show envF.trace 5 = (encodedRowAt (F := F) A i).base 5 by
      simpa [envF] using hbase]
  ring

/-- Change one current-row physical coordinate while preserving every other coordinate and all
challenge/public values. -/
def mutateCurrentTrace (env : Env F) (column : ℕ) (δ : F) : Env F where
  trace q := if q = column then env.trace q + δ else env.trace q
  traceNext := env.traceNext
  chal := env.chal
  pub := env.pub

def mutateNextTrace (env : Env F) (column : ℕ) (δ : F) : Env F where
  trace := env.trace
  traceNext q := if q = column then env.traceNext q + δ else env.traceNext q
  chal := env.chal
  pub := env.pub

theorem canonical_verify_axis_named_gate_rejects
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (hlam : ∀ i, (R.problem.exec.memoryPubAt i).lambda =
      (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows)
    (hst : (R.problem.exec.memoryPubAt i).st = .verify_child)
    (hLam0 : (exactMemoryRowEnv A ⟨0, R.problem.cfg.memRows_pos⟩).chal 8 ≠ 0)
    (δ : K) (hδ : δ ≠ 0) :
    (verifyAxisSource (K := K)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) 26 δ) ≠ 0 := by
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hz := canonical_memoryRowSources A P hlam nodes hnodes b chalVal pubVal orbit
    pins i (verifyAxisSource (K := K)) (verifyAxisSource_mem (K := K))
    (by
      intro h
      simp only [verifyAxisSource, MemoryFactorizationScope.mergedGate, gateByM, Expr.subst] at h
      injection h with hL _
      injection hL with _ hQ
      simp only [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock,
        MemoryFactorizationScope.blockDecompose, List.getD, Expr.subst, memorySubst, tc] at hQ
      injection hQ with h8 _
      injection h8 with _ hidx
      exact absurd hidx (by norm_num))
    (by
      intro h
      simp only [verifyAxisSource, MemoryFactorizationScope.mergedGate, gateByM, Expr.subst] at h
      injection h with hL _
      injection hL with _ hQ
      simp only [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock,
        MemoryFactorizationScope.blockDecompose, List.getD, Expr.subst, memorySubst, tc] at hQ
      injection hQ)
  have hsel := canonical_gather_selectorMirror_current A nodes hnodes b chalVal pubVal orbit
    i (3 : Fin 4)
  have hsel' : envK.trace 54 = 1 := by
    simpa [envK, extensionEquiv_apply, extensionIndex, stateSelector, stateIndex, hst] using hsel
  have h51 : envK.trace 51 = 0 := by
    simpa [envK, extensionEquiv_apply, extensionIndex, stateSelector, stateIndex, hst] using
      canonical_gather_selectorMirror_current A nodes hnodes b chalVal pubVal orbit i (0 : Fin 4)
  have h52 : envK.trace 52 = 0 := by
    simpa [envK, extensionEquiv_apply, extensionIndex, stateSelector, stateIndex, hst] using
      canonical_gather_selectorMirror_current A nodes hnodes b chalVal pubVal orbit i (1 : Fin 4)
  have h53 : envK.trace 53 = 0 := by
    simpa [envK, extensionEquiv_apply, extensionIndex, stateSelector, stateIndex, hst] using
      canonical_gather_selectorMirror_current A nodes hnodes b chalVal pubVal orbit i (2 : Fin 4)
  have hLam : envK.chal 8 ≠ 0 := by
    have hcol :
        (memorySourceTemplate b).col0 3 .challenge 8 = 6 + 3 * 8 := by
      rw [memorySourceTemplate_col0]; rfl
    change (∑ k : Fin 3,
        chalVal ((memorySourceTemplate b).col0 3 .challenge 8 + (k : ℕ)) • b k) ≠ 0
    simp only [hcol]
    rw [pins.sampledLambda]
    exact hLam0
  exact verifyAxisSource_mutation_rejected envK δ h51 h52 h53 hsel' hLam hz hδ

theorem canonical_read_timestamp_named_gate_rejects
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (hlam : ∀ i, (R.problem.exec.memoryPubAt i).lambda =
      (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows)
    (hst : (R.problem.exec.memoryPubAt i).st = .read_root)
    (hLam0 : (exactMemoryRowEnv A ⟨0, R.problem.cfg.memRows_pos⟩).chal 8 ≠ 0)
    (haxis : (R.problem.exec.memoryPubAt i).mem.axis ≠ 0)
    (δ : K) (hδ : δ ≠ 0) :
    (readTimestampSource (K := K)).eval
      (mutateExtensionTrace
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) 26 δ) ≠ 0 := by
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hz := canonical_memoryRowSources A P hlam nodes hnodes b chalVal pubVal orbit
    pins i (readTimestampSource (K := K)) (readTimestampSource_mem (K := K))
    (by
      intro h
      simp only [readTimestampSource, MemoryFactorizationScope.mergedGate, gateByM, Expr.subst] at h
      injection h with hL _
      injection hL with _ hQ
      simp only [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock,
        MemoryFactorizationScope.blockDecompose, List.getD, Expr.subst, memorySubst, tc] at hQ
      injection hQ with h7 _
      injection h7 with _ hidx
      exact absurd hidx (by norm_num))
    (by
      intro h
      simp only [readTimestampSource, MemoryFactorizationScope.mergedGate, gateByM, Expr.subst] at h
      injection h with hL _
      injection hL with _ hQ
      simp only [MemoryFactorizationScope.memQuantity, MemoryFactorizationScope.paddedBlock,
        MemoryFactorizationScope.blockDecompose, List.getD, Expr.subst, memorySubst, tc] at hQ
      injection hQ)
  have hsel := canonical_gather_selectorMirror_current A nodes hnodes b chalVal pubVal orbit
    i (2 : Fin 4)
  have hsel' : envK.trace 53 = 1 := by
    simpa [envK, extensionEquiv_apply, extensionIndex, stateSelector, stateIndex, hst] using hsel
  have h51 : envK.trace 51 = 0 := by
    simpa [envK, extensionEquiv_apply, extensionIndex, stateSelector, stateIndex, hst] using
      canonical_gather_selectorMirror_current A nodes hnodes b chalVal pubVal orbit i (0 : Fin 4)
  have h52 : envK.trace 52 = 0 := by
    simpa [envK, extensionEquiv_apply, extensionIndex, stateSelector, stateIndex, hst] using
      canonical_gather_selectorMirror_current A nodes hnodes b chalVal pubVal orbit i (1 : Fin 4)
  have h54 : envK.trace 54 = 0 := by
    simpa [envK, extensionEquiv_apply, extensionIndex, stateSelector, stateIndex, hst] using
      canonical_gather_selectorMirror_current A nodes hnodes b chalVal pubVal orbit i (3 : Fin 4)
  have hLam : envK.chal 8 ≠ 0 := by
    have hcol :
        (memorySourceTemplate b).col0 3 .challenge 8 = 6 + 3 * 8 := by
      rw [memorySourceTemplate_col0]; rfl
    change (∑ k : Fin 3,
        chalVal ((memorySourceTemplate b).col0 3 .challenge 8 + (k : ℕ)) • b k) ≠ 0
    simp only [hcol]
    rw [pins.sampledLambda]
    exact hLam0
  have htr25 : envK.trace 25 = (R.problem.exec.memoryPubAt i).mem.axis := by
    let role : MemoryTablePayloadRole := .inr (.inr (.inl ⟨6, by decide⟩))
    have hidx : extensionEquiv (.inl role) = ⟨25, by decide⟩ := by
      simp [extensionEquiv_apply, extensionIndex, role]
    have hgather :=
      canonical_gather_extension_current A nodes hnodes b chalVal pubVal orbit i
        ⟨25, by decide⟩ (by decide)
    have hsymm : extensionEquiv.symm ⟨25, by decide⟩ = .inl role :=
      (Equiv.symm_apply_eq extensionEquiv).mpr hidx
    unfold envK
    rw [hgather, hsymm, encodedRowAt]
    have htab : (encode (semanticRowAt A i)).extension (.inl role) =
        (semanticRowAt A i).table role := by
      have hd := congrArg (fun row : SemanticRow F K => row.table role)
        (decode_encodedRowAt A i)
      simpa [decode, encodedRowAt] using hd
    rw [htab]
    simp only [semanticRowAt, role, memoryTableSourceColumn]
    simpa [exactMemoryRowEnv, Nock.Reified.tc, Expr.eval] using
      (Nock.Reified.eval_mMemAxis R.problem.cfg.challenges.memoryInputs
        (MemoryTable.opSel (R.problem.exec.memoryPubAt i).st)
        (R.problem.exec.memoryPubAt i) (A.exact.memoryTableAux i))
  exact readTimestampSource_mutation_rejected envK δ h51 h52 hsel' h54 hLam
    (by rwa [htr25]) hz hδ

theorem canonical_forest_count_named_gate_rejects
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (δ : K) (hδ : δ ≠ 0) :
    let i : Fin R.problem.cfg.memRows := ⟨0, R.problem.cfg.memRows_pos⟩
    forestCountSource.eval
      (mutateExtensionTrace
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) 32 δ) ≠ 0 := by
  let i : Fin R.problem.cfg.memRows := ⟨0, R.problem.cfg.memRows_pos⟩
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hzLift := (canonical_walkSources A P nodes hnodes b chalVal pubVal orbit
    pins halign i).1 forestCountSource forestCountSource_mem
  have hz : forestCountSource.eval envK = 0 := by
    convert hzLift using 1
    apply eval_eq_of_support_agree
    intro v hv
    refine (lift_agree_off_masks _ _ v.1 ?_ ?_).symm
    · have : v.2 ≠ 153 := by
        revert v hv; decide +revert
      exact this
    · have : v.2 ≠ 154 := by
        revert v hv; decide +revert
      exact this
  have hfirst := canonical_gather_sampled_current A nodes hnodes b chalVal pubVal orbit
    i (10 : Fin 14) (by decide)
  have hfirst' : envK.trace 47 = 1 := by
    simpa [envK, i, extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
      firstMaskK] using hfirst
  exact forestCountSource_mutation_rejected envK δ hfirst' hz hδ

theorem canonical_forest_seed_named_gate_rejects
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (δ : K) (hδ : δ ≠ 0) :
    let i : Fin R.problem.cfg.memRows := ⟨0, R.problem.cfg.memRows_pos⟩
    forestSeedSource.eval
      (mutateExtensionTrace
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) 33 δ) ≠ 0 := by
  let i : Fin R.problem.cfg.memRows := ⟨0, R.problem.cfg.memRows_pos⟩
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hzLift := (canonical_walkSources A P nodes hnodes b chalVal pubVal orbit
    pins halign i).1 forestSeedSource forestSeedSource_mem
  have hz : forestSeedSource.eval envK = 0 := by
    convert hzLift using 1
    apply eval_eq_of_support_agree
    intro v hv
    refine (lift_agree_off_masks _ _ v.1 ?_ ?_).symm
    · have : v.2 ≠ 153 := by
        revert v hv; decide +revert
      exact this
    · have : v.2 ≠ 154 := by
        revert v hv; decide +revert
      exact this
  have hfirst := canonical_gather_sampled_current A nodes hnodes b chalVal pubVal orbit
    i (10 : Fin 14) (by decide)
  have hfirst' : envK.trace 47 = 1 := by
    simpa [envK, i, extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
      firstMaskK] using hfirst
  exact forestSeedSource_mutation_rejected envK δ hfirst' hz hδ

theorem canonical_denominator_named_gate_rejects
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (hsafe : MemoryDenominatorsSafe A)
    (i : Fin R.problem.cfg.memRows)
    (δ : K) (hδ : δ ≠ 0) :
    denominatorSource.eval
      (mutateExtensionTrace
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) 38 δ) ≠ 0 := by
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hz := canonical_sampledSources A P nodes hnodes b chalVal pubVal orbit
    pins hsafe i denominatorSource denominatorSource_mem
  have hinv : envK.trace 50 ≠ 0 := by
    intro hzero
    change denominatorSource.eval envK = 0 at hz
    simp [denominatorSource, sampledSources, extVar, Expr.eval, hzero] at hz
  exact denominatorSource_mutation_rejected envK δ hinv hz hδ

theorem canonical_multiplicity_named_gate_rejects
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows)
    (hactive : responseActive (K := K) (R.problem.exec.memoryPubAt i).ver = 1)
    (h2 : (2 : K) ≠ 0) :
    multiplicitySource.eval
      (mutateExtensionTrace
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) 39 1) ≠ 0 := by
  let envK := canonicalGatheredEnv A nodes b chalVal pubVal orbit i
  have hm := canonical_gather_sampled_current A nodes hnodes b chalVal pubVal orbit
    i (2 : Fin 14) (by decide)
  have hmult : envK.trace 39 = 1 := by
    simpa [envK, extensionEquiv_apply, extensionIndex, sampledMemoryRoleValue,
      hactive] using hm
  exact multiplicitySource_mutation_rejected envK hmult h2

theorem canonical_selectorMirrorCoord_zero
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (s : Fin 4) (k : Fin 3) :
    (CoeffExpr.sub
      (CoeffExpr.var .traceCur (6 + 3 * (51 + s) + k))
      (CoeffExpr.mul (CoeffExpr.const (coord b (1 : K) k))
        (CoeffExpr.var .traceCur s))).eval
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  have hext := canonical_extension_coord_current A nodes hnodes b chalVal pubVal orbit i
    (extensionEquiv (.inr (.inr (.inr (.inl s))))) k (by
      simp [extensionEquiv_apply, extensionIndex]
      omega) (by
      simp [extensionEquiv_apply, extensionIndex]
      omega)
  rw [extensionEquiv.symm_apply_apply] at hext
  have hbase := canonical_base_current A nodes hnodes b chalVal pubVal orbit i
    ⟨s, by omega⟩
  have hext' :
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace
          (6 + 3 * (51 + (s : ℕ)) + (k : ℕ)) =
        coord b (algebraMap F K
          (stateSelector (F := F) (R.problem.exec.memoryPubAt i).st s)) k := by
    simpa [extensionEquiv_apply, extensionIndex, encodedRowAt, encode,
      encodeExtension, semanticRowAt] using hext
  have hbase' :
      (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace s =
        stateSelector (F := F) (R.problem.exec.memoryPubAt i).st s := by
    simpa [encodedRowAt, encode, encodeBase, semanticRowAt] using hbase
  have hcoord :
      coord b (algebraMap F K
          (stateSelector (F := F) (R.problem.exec.memoryPubAt i).st s)) k =
        coord b (1 : K) k *
          stateSelector (F := F) (R.problem.exec.memoryPubAt i).st s := by
    rw [show algebraMap F K
        (stateSelector (F := F) (R.problem.exec.memoryPubAt i).st s) =
      stateSelector (F := F) (R.problem.exec.memoryPubAt i).st s • (1 : K) by
        simp [Algebra.smul_def]]
    simp [coord, mul_comm]
  simp only [CoeffExpr.eval]
  rw [hext', hbase', hcoord, sub_self]


theorem canonical_selectorEqualityChecks
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    ∀ g ∈ foldedEqualityChecks b,
      g.eval (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  intro g hg
  obtain ⟨s, k, rfl⟩ := (mem_foldedEqualityChecks b g).mp hg
  exact canonical_selectorMirrorCoord_zero A nodes hnodes b chalVal pubVal orbit i s k

/-- Canonical rows inhabit the exact union of mask, chain, and selector-compression
collision exclusions. -/
theorem canonical_scalarCollisionExcluded
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows) :
    FirstMaskCollisionExcluded b
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ∧
      LastMaskCollisionExcluded b
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ∧
      ChainCollisionExcluded
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) ∧
      SelectorEqualityCollisionExcluded b
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) := by
  refine ⟨fun _ k => canonical_firstMaskBindingCoord_zero A nodes hnodes b chalVal
      pubVal orbit i k,
    fun _ k => canonical_lastMaskBindingCoord_zero A nodes hnodes b chalVal
      pubVal orbit i k,
    fun _ k => canonical_chainCoord_zero A P nodes hnodes b chalVal pubVal orbit
      halign i k, ?_⟩
  intro s _ k
  exact canonical_selectorMirrorCoord_zero A nodes hnodes b chalVal pubVal orbit i s k

/-- Mutating coordinate zero of one committed selector mirror makes the gate that commits that
coordinate evaluate to `1` on the same canonical physical environment.

The control is therefore stronger than it was — it needs no compression coin
to detect the mutation. -/
theorem canonical_selector_mirror_named_gate_rejects
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) (s : Fin 4) :
    MixedCoordinateCompiler.mixedCompile b memoryCol0 (selectorMixed (F := F) s) 0
        ∈ foldedEqualityChecks b ∧
      (MixedCoordinateCompiler.mixedCompile b memoryCol0 (selectorMixed (F := F) s) 0).eval
        (mutateCurrentTrace
          (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)
          (6 + 3 * (51 + (s : ℕ))) 1) = 1 := by
  refine ⟨(mem_foldedEqualityChecks b _).mpr ⟨s, 0, rfl⟩, ?_⟩
  have h0 := canonical_selectorMirrorCoord_zero A nodes hnodes b chalVal pubVal orbit i s 0
  fin_cases s <;>
    simp [MixedCoordinateCompiler.mixedCompile, selectorMixed, memoryCol0, bcur,
      mutateCurrentTrace, CoeffExpr.eval] at h0 ⊢ <;>
    linear_combination h0

/-- Non-aggregator transition sources vanish.  Classes `23`/`24` are the
deployed aggregator and stay off the honest DeployedRow path. -/
theorem canonical_transitionSources
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (hlam : ∀ i, (R.problem.exec.memoryPubAt i).lambda =
      (R.problem.exec.memoryPubAt ⟨0, R.problem.cfg.memRows_pos⟩).lambda)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (hsafe : MemoryDenominatorsSafe A)
    (i : Fin R.problem.cfg.memRows) :
    ∀ e ∈ transitionSources (K := K),
      e ≠ (MemoryFactorizationScope.mergedGate (K := K) 23).subst memorySubst →
      e ≠ (MemoryFactorizationScope.mergedGate (K := K) 24).subst memorySubst →
      e.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) = 0 := by
  intro e he h23 h24
  unfold transitionSources at he
  rcases List.mem_append.mp he with h | hsampled
  rcases List.mem_append.mp h with h | htransition
  rcases List.mem_append.mp h with h | hboundary
  rcases List.mem_append.mp h with hrow | hchain
  · exact canonical_memoryRowSources A P hlam nodes hnodes b chalVal pubVal orbit
      pins i e hrow h23 h24
  · simp only [List.mem_singleton] at hchain
    subst e
    exact canonical_memoryChainSource A P nodes hnodes b chalVal pubVal orbit
      halign i
  · have hlift := (canonical_walkSources A P nodes hnodes b chalVal pubVal orbit
      pins halign i).1 e hboundary
    simp only [walkBoundarySources, List.mem_map, List.mem_cons, List.not_mem_nil,
      or_false] at hboundary
    obtain ⟨g, hg, rfl⟩ := hboundary
    have hg' : g = Trans.walkLn1 ∨ g = Trans.walkCount1 ∨
        g = Trans.walkAccInitMasked := by
      simpa [List.mem_cons, List.not_mem_nil] using hg
    rcases hg' with rfl | rfl | rfl
    all_goals
      convert hlift using 1
      apply eval_eq_of_support_agree
      intro v hv
      refine (lift_agree_off_masks _ _ v.1 ?_ ?_).symm
      · have : v.2 ≠ 153 := by revert v hv; decide +revert
        exact this
      · have : v.2 ≠ 154 := by revert v hv; decide +revert
        exact this
  · have hlift := (canonical_walkSources A P nodes hnodes b chalVal pubVal orbit
      pins halign i).2 e htransition
    simp only [walkTransitionSources, walkLnCountTransitionSources, List.mem_append,
      List.mem_map, List.mem_singleton, List.mem_cons, List.not_mem_nil, or_false] at htransition
    rcases htransition with ⟨g, hg, rfl⟩ | hbad
    · have hg' : g = Trans.walkLnStep ∨ g = Trans.walkCountStep := by
        simpa [List.mem_cons, List.not_mem_nil] using hg
      rcases hg' with rfl | rfl
      all_goals
        convert hlift using 1
        apply eval_eq_of_support_agree
        intro v hv
        refine (lift_agree_off_masks _ _ v.1 ?_ ?_).symm
        · have : v.2 ≠ 153 := by revert v hv; decide +revert
          exact this
        · have : v.2 ≠ 154 := by revert v hv; decide +revert
          exact this
    · subst e
      have hlift := (canonical_walkSources A P nodes hnodes b chalVal pubVal orbit
        pins halign i).2 walkAccStepHosted (by
          simp [walkTransitionSources, walkLnCountTransitionSources])
      convert hlift using 1
      apply eval_eq_of_support_agree
      intro v hv
      refine (lift_agree_off_masks _ _ v.1 ?_ ?_).symm
      · have : v.2 ≠ 153 := by revert v hv; decide +revert
        exact this
      · have : v.2 ≠ 154 := by revert v hv; decide +revert
        exact this
  · exact canonical_sampledSources A P nodes hnodes b chalVal pubVal orbit
      pins hsafe i e hsampled

/-- Endpoints only: the fold of classes `23`/`24` does not vanish after the
27/28 overlay, so `FoldCollisionExcluded` / full `DeployedRow` extension is
not claimed.  Committed completeness is `PaperRow`. -/
theorem canonical_extensionEndpoints
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (hprl : RowLayout.PairedRecordLayout R.problem.exec)
    (hhon : ∀ row ∈ R.problem.exec.memoryRows,
      row.2.2.ver = decide (row.2.2.st = MemoryTable.MState.read_root))
    (hC : R.problem.exec.CprimeCoherent)
    (i : Fin R.problem.cfg.memRows) :
    (∀ e ∈ degreeOneEndpoints,
      e.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) = 0) ∧
    (∀ e ∈ foldedDegreeThreeEndpoints,
      e.eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i) = 0) :=
  canonical_endpointSources A P nodes hnodes b chalVal pubVal orbit pins hprl hhon hC i

/-- **The response-accumulator chain vanishes on canonical rows**: off the last row
the *after* accumulator of row `i` (role `44`, `responseAccumulator A (i+1)`) is the *before*
accumulator of row `i+1` (role `43` at the next row, the same value), and at the last row the
`(1 − last)` mask kills the gate.  The exact analogue of `canonical_memoryChainSource`. -/
theorem canonical_accChainMixed
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows) :
    (accChainMixed (F := F)).eval
        (gatherEnv b ((memorySourceTemplate b).col0 3)
          (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i))
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  let envF := canonicalPhysicalEnv A nodes b chalVal pubVal orbit i
  have hb5 := canonical_base_current A nodes hnodes b chalVal pubVal orbit i (5 : Fin 6)
  change (accChainMixed (F := F)).eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
    envF = 0
  simp only [accChainMixed, MixedCoordinateCompiler.MixedExpr.eval, bcur, CoeffExpr.eval]
  by_cases hi : (i : ℕ) + 1 < R.problem.cfg.memRows
  · -- interior row: the two accumulator values agree
    have hafter := canonical_gather_sampled_index A nodes hnodes b chalVal pubVal orbit i
      (7 : SampledMemoryIORole) (by decide)
    have hbefore := canonical_gather_extension_next A nodes hnodes b chalVal pubVal orbit
      i hi (halign i hi) (extensionEquiv (.inr (.inr (.inl (6 : SampledMemoryIORole)))))
      (by decide)
    rw [extensionEquiv.symm_apply_apply] at hbefore
    have hbefore' :
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).traceNext 43 =
          responseAccumulator A ((i : ℕ) + 1) := by
      simpa [extensionEquiv_apply, extensionIndex, encodedRowAt, semanticRowAt, encode,
        encodeExtension, sampledMemoryRoleValue] using hbefore
    have hafter' :
        (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 44 =
          responseAccumulator A ((i : ℕ) + 1) := by
      simpa [sampledMemoryRoleValue] using hafter
    rw [hafter', hbefore', sub_self, mul_zero]
  · -- last row: the mask is one
    have hilast : (i : ℕ) + 1 = R.problem.cfg.memRows := by omega
    have hb5last : envF.trace 5 = 1 := by
      rw [show envF.trace 5 = (encodedRowAt (F := F) A i).base 5 by simpa [envF] using hb5]
      simp [encodedRowAt, encode, encodeBase, semanticRowAt, lastMask, hilast]
    rw [show (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 5 = 1 from hb5last]
    simp

/-- **The 31st:** physical column `181` of the canonical row is the honest exponent carrier
(`honestReqIdx`). -/
theorem canonical_physical_reqIdx
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 181 = honestReqIdx R i := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (show (181 : ℕ) < 182 by omega)]
  exact canonicalSourceTrace_reqIdx A nodes hnodes b R.problem.cfg.kMem i

/-- **The response-denominator pin vanishes on canonical rows**: the honest
role `37` is `responseDenominator A i = FiniteIO.compress A.sampled.coins (encRec mem)`
(`sampledMemoryRoleValue 0`), roles `19..26` are the record fields in `encRec` order
(`canonical_table_role` at table columns `23..30`), and the two coin slots are the sampled `γ`
and `pole` by `ExactMemoryCoordinatePins.sampledGamma`/`sampledPole`.  So the gate reads
`compress coins record − (pole + Walk.rlc γ record) = 0` literally — the paper's
`RLC^α(x_mem(i,·)) − β` in the additive convention.  Lifted from W2's
`MemoryPaperFactorization.canonical_denominatorPin`. -/
theorem canonical_denominatorPinMixed
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (i : Fin R.problem.cfg.memRows) :
    (denominatorPinMixed (F := F)).eval
        (gatherEnv b ((memorySourceTemplate b).col0 3)
          (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i))
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  change (denominatorPinMixed (F := F)).eval (canonicalGatheredEnv A nodes b chalVal pubVal orbit i)
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0
  have h37 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 37
      = responseDenominator A i := by
    have := canonical_gather_sampled_index A nodes hnodes b chalVal pubVal orbit i (0 : Fin 14)
      (by decide)
    simpa [sampledMemoryRoleValue] using this
  have hgamma : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).chal 4
      = A.sampled.coins.gamma := by
    change (∑ k : Fin 3, chalVal ((memorySourceTemplate b).col0 3 .challenge 4 + (k : ℕ)) • b k)
      = A.sampled.coins.gamma
    exact pins.sampledGamma
  have hpole : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).chal 5
      = A.sampled.coins.pole := by
    change (∑ k : Fin 3, chalVal ((memorySourceTemplate b).col0 3 .challenge 5 + (k : ℕ)) • b k)
      = A.sampled.coins.pole
    exact pins.sampledPole
  have hrole : ∀ c : ℕ, c < 8 →
      (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace (19 + c)
        = (exactMemoryRowEnv A i).trace (23 + c) := by
    intro c hc
    have := canonical_table_role A nodes hnodes b chalVal pubVal orbit pins i (23 + c)
      (by omega) (by omega) (by omega)
    rwa [show 23 + c - 4 = 19 + c by omega] at this
  have r0 := hrole 0 (by norm_num)
  have r1 := hrole 1 (by norm_num)
  have r2 := hrole 2 (by norm_num)
  have r3 := hrole 3 (by norm_num)
  have r4 := hrole 4 (by norm_num)
  have r5 := hrole 5 (by norm_num)
  have r6 := hrole 6 (by norm_num)
  have r7 := hrole 7 (by norm_num)
  have r57 : (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 57 =
      (R.problem.exec.memoryPubAt i).cprime :=
    canonical_gather_cprime A nodes hnodes b chalVal pubVal orbit i
  have r181 := canonical_physical_reqIdx A nodes hnodes b chalVal pubVal orbit i
  have h37' : responseDenominator A i =
      FiniteIO.compress A.sampled.coins (NockVM.encRecC (R.problem.exec.memoryPubAt i).mem
        (R.problem.exec.memoryPubAt i).cprime) +
        A.sampled.coins.gamma ^ 9 * algebraMap F K (honestReqIdx R i) := by
    simp only [responseDenominator, rowRecord10, FiniteIO.compress, RecordCarrier.rlc_withExp,
      honestReqIdx, map_natCast]
    ring
  norm_num at r0 r1 r2 r3 r4 r5 r6 r7
  simp only [denominatorPinMixed, recordRLC, recordRLCExpr, reqIdxRLCTerm, reqIdxCol, bcur,
    CoeffExpr.eval, r181,
    MixedCoordinateCompiler.MixedExpr.eval, MixedCoordinateCompiler.MixedExpr.ofExpr_eval,
    Expr.eval, h37, h37', hgamma, hpole, r0, r1, r2, r3, r4,
    r5, r6, r7, r57, FiniteIO.compress, Walk.rlc,
    Fin.sum_univ_succ, Fin.sum_univ_eight,
    NockVM.encRecC, MemoryTable.Pub.cprime, exactMemoryRowEnv, memoryEnvFull]
  simp [Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

/-- **The five `𝕂`-valued mixed transition gates vanish on canonical rows**.  Each of the first three is the mixed gate whose `e` compiled coordinates are
*definitionally* the coordinate bodies proved zero just above, so those are
`mixedCompile_zero_iff` applied to existing theorems; the fourth is `canonical_accChainMixed`, the
fifth `canonical_denominatorPinMixed` (which is where `pins` enters: the two coin slots).  No
compression coin appears anywhere in it. -/
theorem canonical_mixedTransitionGates
    (A : SampledIOSameExecutionAssignment R p)
    (P : MemoryChipAssignment A)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (halign : MemoryOrbitAligned nodes orbit)
    (i : Fin R.problem.cfg.memRows) :
    ∀ g ∈ foldedMixedTransitionGates (F := F),
      g.eval
          (gatherEnv b ((memorySourceTemplate b).col0 3)
            (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i))
          (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  intro g hg
  have hiso := isCoordEnv_gather b ((memorySourceTemplate b).col0 3)
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i)
  simp only [foldedMixedTransitionGates, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (MixedCoordinateCompiler.mixedCompile_zero_iff b
      ((memorySourceTemplate b).col0 3) hiso _).2
      fun k => canonical_firstMaskBindingCoord_zero A nodes hnodes b chalVal pubVal orbit i k
  · exact (MixedCoordinateCompiler.mixedCompile_zero_iff b
      ((memorySourceTemplate b).col0 3) hiso _).2
      fun k => canonical_lastMaskBindingCoord_zero A nodes hnodes b chalVal pubVal orbit i k
  · exact (MixedCoordinateCompiler.mixedCompile_zero_iff b
      ((memorySourceTemplate b).col0 3) hiso _).2
      fun k => canonical_chainCoord_zero A P nodes hnodes b chalVal pubVal orbit halign i k
  · exact canonical_accChainMixed A nodes hnodes b chalVal pubVal orbit halign i
  · exact canonical_denominatorPinMixed A nodes hnodes b chalVal pubVal orbit pins i
  · exact (MixedCoordinateCompiler.mixedCompile_zero_iff b
      ((memorySourceTemplate b).col0 3) hiso _).2
      fun k => canonical_dequeueMaskBindingCoord_zero A nodes hnodes b chalVal pubVal orbit i k

/-- **Honest `halt` leaves are base-field values** (the 29th's completeness side condition).
Every `halt` row of the execution carries a `𝕂` leaf in the image of `𝔽`: the honest generator's
`halt` rows are atoms `k` with leaf `(k : K)` (`enc_atom`, the paper;
`TraceGen.GenMem.genHaltNodes`, `genAnnotatedNounWalk`).  `eqBlk` alone leaves the leaf free
, so for an arbitrary sampled assignment this is a hypothesis of
completeness, not a theorem; it never enters `nockCompiles_zmod` (canonical satisfaction is off
its proof closure). -/
def HaltLeavesBase (A : SampledIOSameExecutionAssignment R p) : Prop :=
  ∀ i : Fin R.problem.cfg.memRows,
    (R.problem.exec.memoryPubAt i).st = .halt →
      ∃ a : F, algebraMap F K a = (R.problem.exec.memoryPubAt i).pt.noun.leaf

/-- Physical column `180` of the canonical row is the honest atom (`honestAtomOf`). -/
theorem canonical_physical_atom
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 180 =
      OptimizedMemoryCanonicalTrace.honestAtomOf (F := F) (R.problem.exec.memoryPubAt i) := by
  simp only [canonicalPhysicalEnv, envOfTrace]
  rw [dif_pos (show (180 : ℕ) < 182 by omega)]
  exact OptimizedMemoryCanonicalTrace.canonicalSourceTrace_atom A nodes hnodes b
    R.problem.cfg.kMem i

/-- **The `halt`-row atom gate vanishes on canonical rows** (the 29th), given honest `halt`
leaves are base-field values.  Off `halt` the selector is `0`; on `halt` the atom column is the
`𝔽`-preimage of the leaf. -/
theorem canonical_haltAtomMixed
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (pins : ExactMemoryCoordinatePins A b chalVal pubVal)
    (hhalt : HaltLeavesBase A)
    (i : Fin R.problem.cfg.memRows) :
    (haltAtomMixed (F := F)).eval
        (gatherEnv b ((memorySourceTemplate b).col0 3)
          (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i))
        (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i) = 0 := by
  rw [haltAtomMixed_eval]
  have hsel := canonical_base_current A nodes hnodes b chalVal pubVal orbit i ⟨1, by omega⟩
  have hleaf := canonical_table_role A nodes hnodes b chalVal pubVal orbit pins i 6
    (by omega) (by omega) ⟨by omega, by omega⟩
  have hatom := canonical_physical_atom A nodes hnodes b chalVal pubVal orbit i
  change (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 2 = _ at hleaf
  change algebraMap F K ((canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 1) *
      ((canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 2 -
        algebraMap F K ((canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 180)) = 0
  rw [hleaf, hatom]
  have hsel' : (canonicalPhysicalEnv A nodes b chalVal pubVal orbit i).trace 1 =
      stateSelector (F := F) (R.problem.exec.memoryPubAt i).st 1 := by
    rw [show ((1 : ℕ)) = ((⟨1, by omega⟩ : Fin 6) : ℕ) from rfl, hsel]
    simp [encodedRowAt, semanticRowAt, encode, encodeBase]
  rw [hsel']
  by_cases hst : (R.problem.exec.memoryPubAt i).st = .halt
  · have hspec := OptimizedMemoryCanonicalTrace.honestAtomOf_spec (F := F)
      (R.problem.exec.memoryPubAt i) ⟨hst, hhalt i hst⟩
    simp [exactMemoryRowEnv, memoryEnvFull, hspec]
  · have h0 : stateSelector (F := F) (R.problem.exec.memoryPubAt i).st 1 = 0 := by
      generalize hs : (R.problem.exec.memoryPubAt i).st = s at hst
      cases s <;> simp_all [stateSelector, stateIndex]
    simp [h0]

-- `canonicalSourceTrace_satisfies` lives in `MemoryPaperFactorization` (W2: the committed
-- language is `PaperRow`, which this module cannot see without a cycle).

/-- Extend a source trace by zero polynomials in precisely the authorized right-padding columns. -/
def rightPadTrace (S : RAP F) (extra : Fin S.k → ℕ)
    (P : Fin S.w → F[X]) : Fin (S.w + RAPPadding.extraWidth extra) → F[X] :=
  Fin.addCases P (fun _ => 0)

@[simp] theorem project_rightPadTrace (S : RAP F) (extra : Fin S.k → ℕ)
    (P : Fin S.w → F[X]) :
    RAPPadding.projectTrace S extra (rightPadTrace S extra P) = P := by
  funext i
  simp [RAPPadding.projectTrace, RAPPadding.columnInclusion, rightPadTrace]
  exact Fin.addCases_left i

/-- The canonical `196`-column trace: the semantic `171` columns followed by exactly `25`
authorized residual zero columns. -/
def canonicalFinalMemoryTrace
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h) :
    Fin (namedFinalMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem).rap.w →
      F[X] :=
  let S := namedSourceMemoryRAP R.problem.cfg.memRows_pos nodes b chalVal pubVal orbit R.problem.cfg.kMem
  rightPadTrace S.rap
    (RAPPadding.firstRoundExtra S.rap S.rounds_pos
      (RAPPadding.memoryResidualColumns 3))
    (canonicalSourceTrace A nodes b R.problem.cfg.kMem)

-- `canonicalFinalMemoryTrace_satisfies` and `canonicalMemoryRealization` live in
-- `MemoryPaperFactorization` (W2 cycle: committed language is `PaperRow`).

/-- A mixed gate is evaluated
against **two** environments — the gathered `Env K` and the base `Env F` — because its `Lift`/
`Scale` leaves read base columns `0..5`, which `gatherEnv` provably cannot reach
(`(memorySourceTemplate b).col0 3 kind idx = 6 + 3·idx ≥ 6`). That is why a one-argument
`Env K → Prop` language (`Batch29.B29SemanticTemplate`) structurally cannot carry a mixed gate,
while this two-environment statement can.

**Consumers must re-index:** the right-hand side is now a four-fold conjunction, so
`OptimizedStrictFullPackage.memory_source_gate_facts`'s `.2.2` became `.2.2.1`. -/
theorem sourceMemoryRAP_satisfies_iff_language
    {h : ℕ} (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    (orbit : StrictOrbitDomain F 3 h)
    (P : Fin 182 → F[X]) :
    (sourceMemoryRAP b chalVal pubVal orbit (rowNodeSet nodes)).Satisfies P ↔
      ∀ x ∈ rowNodeSet nodes,
        (∀ g ∈ baseTransitionGates b,
          g.eval (envOfTrace P orbit.ω x chalVal pubVal) = 0) ∧
        (∀ g ∈ equalityChecks b,
          g.eval (envOfTrace P orbit.ω x chalVal pubVal) = 0) ∧
        (∀ g ∈ (memorySourceTemplate b).extTransition ++
            (memorySourceTemplate b).extDeg1 ++ (memorySourceTemplate b).extDeg3,
          g.eval (gatherEnv b ((memorySourceTemplate b).col0 3)
            (envOfTrace P orbit.ω x chalVal pubVal)) = 0) ∧
        (∀ g ∈ mixedTransitionGates (F := F) (K := K) b,
          g.eval (gatherEnv b ((memorySourceTemplate b).col0 3)
            (envOfTrace P orbit.ω x chalVal pubVal))
            (envOfTrace P orbit.ω x chalVal pubVal) = 0) := by
  show (expandChipTail (memorySourceTemplate b) b chalVal pubVal orbit (rowNodeSet nodes) 2).Satisfies P
    ↔ _
  rw [expandChipTail_satisfies_iff_language
    (memorySourceTemplate b) b chalVal pubVal orbit (rowNodeSet nodes) 2 P]
  exact Iff.rfl

end
end OptimizedMemoryCanonicalSatisfaction
end Nock.NockVMROM.Thm54

#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_gather_extension_current
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.memoryDenominatorsSafe_of_sampled
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_denominatorPinMixed
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_scalarCollisionExcluded
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_ipre
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_icur
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.canonical_memoryRowSources
#print axioms Nock.NockVMROM.Thm54.OptimizedMemoryCanonicalSatisfaction.sourceMemoryRAP_satisfies_iff_language
