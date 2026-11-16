/-
  Nock/RedTeam/Batch911Thm54HWCanonicalTrace.lean

  * `canonical_gather_axis` — the canonical gathered memory env's role 25 is the package
    execution's row `mem.axis` (the stored Form R `T`; replica of the `htr25` step inside
    `OptimizedMemoryCanonicalSatisfaction.canonical_verify_axis_named_gate_rejects`).
  * `lblM_canonical_axis` — at EVERY tuple `c`, the decoded label `lblM P (canonicalMemoryTrace P)
    c (i+1)` carries that stored `T` in its `axis` slot (the decode reads trace columns only).
  * `canonical_accepted_at_honest_tuple` — under the `chalVal` pin, `hmore` and `CprimeCoherent`
    (the hypotheses of `canonicalMemoryTrace_satisfies`), the canonical trace is accepted by the
    deployed family memory chip `P.memoryChipAt P.honestTuple`
    (`RAP.SatisfiesWithPreprocessing`, via `Batch728.satisfies_familyQm_of_chip_eq`).
  * **`hW_fails_on_accepted_canonical`** — the same trace, accepted at the deployed chip, refutes
    `WrapMemoryIdentity P P.honestTuple (canonicalMemoryTrace P)` as soon as ONE execution row
    stores a nonzero `T` that is not a fixed point of `formRT λ ∘ nockAxisOf` at the package `λ`.
  * `hW_fails_at_lambda_three` — instantiation: package `λ = 3`, `25 ≤ ringChar K` (every admissible
    prime), and one row storing the honest encode `formRT 3 a` of an axis `a ∈ {4,…,7}`
    (`RawSemanticAssembly.MemoryRowFrame.memoryRecordAxis` is that storage law).

  **Scope (rule 8(b)).**  Acceptance here is the memory conjunct only, at the honest tuple.  NOT
  compiled: (i) a concrete package instance with such a row (`nockCompiles_zmod` at `lmb = 3` and a
  program with an axis-4 lookup would supply it; not instantiated), (ii) `honestTuple ∉`
  the consumed failure event at the canonical traces.
-/
import Nock.RedTeam.Batch910Thm54HWAxisDichotomy
import Nock.NockVMROM.Thm54.OptimizedCanonicalTraces
import Nock.NockVMROM.Thm54.WrapMemoryConjuncts
import Nock.RedTeam.Batch728Thm54MPrimeTopoReceipts
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

namespace Nock.RedTeam.Batch911

open scoped Polynomial
open Polynomial
open Nock
open Nock.Framework
open Nock.Framework.Reify
open Nock.Reified
open Module
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
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
open OptimizedMemoryCanonicalSatisfaction
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.ExecOfTraces

noncomputable section

/-! ## A. Role 25 of the canonical memory env is the stored `T` -/

section Canonical

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable {p : ℕ} [CharP K p]
variable {R : PlusIOSegmentedFamily F K}

theorem canonical_gather_axis
    (A : SampledIOSameExecutionAssignment R p)
    (nodes : Fin R.problem.cfg.memRows → F) (hnodes : Function.Injective nodes)
    (b : Basis (Fin 3) F K) (chalVal pubVal : ℕ → F)
    {h : ℕ} (orbit : StrictOrbitDomain F 3 h)
    (i : Fin R.problem.cfg.memRows) :
    (canonicalGatheredEnv A nodes b chalVal pubVal orbit i).trace 25 =
      (R.problem.exec.memoryPubAt i).mem.axis := by
  let role : MemoryTablePayloadRole := .inr (.inr (.inl ⟨6, by decide⟩))
  have hidx : extensionEquiv (.inl role) = ⟨25, by decide⟩ := by
    simp [extensionEquiv_apply, extensionIndex, role]
  have hgather :=
    canonical_gather_extension_current A nodes hnodes b chalVal pubVal orbit i
      ⟨25, by decide⟩ (by decide)
  have hsymm : extensionEquiv.symm ⟨25, by decide⟩ = .inl role :=
    (Equiv.symm_apply_eq extensionEquiv).mpr hidx
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

end Canonical

/-! ## B. The decoded label of the canonical trace, at every tuple -/

section Package

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

theorem memorySourceEnvAt_trace25_eq_sourceEnv
    (c : OptimizedProductionChallengeTuple K F)
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (FamilyComputeRows.memorySourceEnvAt P c Qm i).trace 25 =
      (P.memorySourceEnv Qm i).trace 25 := by
  rw [WrapMemoryConjuncts.memorySourceEnvAt_trace_eq_rowEnvK P c Qm i 25 (by norm_num)]
  rfl

/-- **The decoded `axis` slot of the canonical trace is the stored `T`, at every tuple.** -/
theorem lblM_canonical_axis
    (c : OptimizedProductionChallengeTuple K F)
    (i : Fin P.optimized.family.problem.cfg.memRows) :
    (lblM P (MultiRootOptimizedAcceptance.canonicalMemoryTrace P) c (i.val + 1)).2.2.mem.axis =
      (P.optimized.family.problem.exec.memoryPubAt i).mem.axis := by
  rw [lblM_succ]
  change (FamilyComputeRows.memorySourceEnvAt P c
      (MultiRootOptimizedAcceptance.canonicalMemoryTrace P) i).trace 25 = _
  rw [memorySourceEnvAt_trace25_eq_sourceEnv, MultiRootOptimizedAcceptance.canonical_memorySourceEnv]
  exact canonical_gather_axis P.optimized.sampled P.optimized.memoryNodes
    P.optimized.memoryNodes_injective P.optimized.basis P.optimized.memoryChallenge
    P.optimized.memoryPublic P.optimized.orbit i

/-! ## C. Accepted at the deployed family memory chip, and `hW` fails on it -/

variable
  (hmchal : DeployedChipFamily.memoryChalValOfTuple P.optimized.basis P.honestTuple =
    P.optimized.memoryChallenge)
  (hmore : ∀ i : Fin P.optimized.family.problem.cfg.memRows,
    0 < (i : ℕ) → (i : ℕ) < P.optimized.family.problem.cfg.kMem →
      (P.optimized.family.problem.exec.memoryPubAt i).pt.counts = 0 ∧
        (P.optimized.family.problem.exec.memoryPubAt i).pt.indicator = 0)
  (hC : P.optimized.family.problem.exec.CprimeCoherent)

include hmchal hmore hC

/-- The canonical memory trace is accepted by the deployed family memory chip at the honest
tuple. -/
theorem canonical_accepted_at_honest_tuple :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt P.honestTuple)
      (WrapMemoryConjuncts.familyQm P P.honestTuple
        (MultiRootOptimizedAcceptance.canonicalMemoryTrace P)) :=
  Batch728.satisfies_familyQm_of_chip_eq P P.honestTuple _
    (P.memoryChipAt_honest_of_chalVal hmchal)
    (MultiRootOptimizedAcceptance.canonicalMemoryTrace_satisfies P hmore hC)

/-- **`hW` fails on an accepted trace.**  The canonical memory trace is accepted by the deployed
family memory chip at the honest tuple, and `WrapMemoryIdentity` at that tuple and trace is FALSE
as soon as one execution row stores a nonzero `T` that is not a fixed point of
`formRT λ ∘ nockAxisOf` at the package `λ`. -/
theorem hW_fails_on_accepted_canonical
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (h0 : (P.optimized.family.problem.exec.memoryPubAt i).mem.axis ≠ 0)
    (hfix : (P.optimized.family.problem.exec.memoryPubAt i).mem.axis ≠
      formRT P.honestTuple.2.2.2.lambda
        (nockAxisOf (P.optimized.family.problem.exec.memoryPubAt i).mem.axis)) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt P.honestTuple)
        (WrapMemoryConjuncts.familyQm P P.honestTuple
          (MultiRootOptimizedAcceptance.canonicalMemoryTrace P)) ∧
      ¬ Batch509.WrapMemoryIdentity P P.honestTuple
        (MultiRootOptimizedAcceptance.canonicalMemoryTrace P) := by
  refine ⟨canonical_accepted_at_honest_tuple P hmchal hmore hC, ?_⟩
  have hax := lblM_canonical_axis P P.honestTuple i
  exact Batch910.not_hW_of_row P P.honestTuple _ (i.val + 1)
    (by rw [hax]; exact h0) (by rw [hax]; exact hfix)

/-- **Instantiation at `λ = 3`.**  At every admissible prime (`25 ≤ ringChar K`), if the honest
tuple's `λ` is `3` and one execution row stores the honest Form R encode `formRT 3 a` of an axis
with shift `2` (`a ∈ {4, 5, 6, 7}`), the accepted canonical trace refutes `hW`. -/
theorem hW_fails_at_lambda_three (hp : 25 ≤ ringChar K)
    (hlam : P.honestTuple.2.2.2.lambda = 3)
    (i : Fin P.optimized.family.problem.cfg.memRows) {a : ℕ} (ha : formRCertShift a = 2)
    (hrow : (P.optimized.family.problem.exec.memoryPubAt i).mem.axis = formRT (3 : K) a) :
    RAP.SatisfiesWithPreprocessing (P.memoryChipAt P.honestTuple)
        (WrapMemoryConjuncts.familyQm P P.honestTuple
          (MultiRootOptimizedAcceptance.canonicalMemoryTrace P)) ∧
      ¬ Batch509.WrapMemoryIdentity P P.honestTuple
        (MultiRootOptimizedAcceptance.canonicalMemoryTrace P) := by
  obtain ⟨h0, hfix⟩ := Batch910.three_shift_two_witness (K := K) hp ha
  exact hW_fails_on_accepted_canonical P hmchal hmore hC i
    (by rw [hrow]; exact h0) (by rw [hrow, hlam]; exact hfix)

end Package

end

end Nock.RedTeam.Batch911

#print axioms Nock.RedTeam.Batch911.canonical_gather_axis
#print axioms Nock.RedTeam.Batch911.lblM_canonical_axis
#print axioms Nock.RedTeam.Batch911.canonical_accepted_at_honest_tuple
#print axioms Nock.RedTeam.Batch911.hW_fails_on_accepted_canonical
#print axioms Nock.RedTeam.Batch911.hW_fails_at_lambda_three
