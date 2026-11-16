import Nock.NockVMROM.Thm54.FamilyIOChainRouteB
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!
Its gate-level conjuncts — `compute_source`, `compute`, `memory` — are today
proved at the PACKAGE envs through `productionNamedComputeRAP_satisfies_iff_sourceLanguage`,
the `lastRowMask` binding and `memoryRealization.arbitrary_final_iff_source`.

* `compute_source_at` — `CorrectedComputeSourceObligations` at `rowEnvAt P c Qc i`, every row
  (`FamilyComputeRows.row_obligations_at`; the `_iff_sourceLanguage` lemma is parametric in
  `chalVal`/`pubVal`, so it applies to `computeChipAt c` verbatim);
* `memory_at` — the base and mixed gate facts at `memEnvF` / `memEnvK`
  (`FamilyMemoryRows.base_at_family` / `mixed_at_family`).

None of these needs `c ∉ optimizedFailureEvent`, `FamilyIOGood`, `rowsBound` or any coin pin.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch883

open scoped Polynomial
open Polynomial
open Nock
open Nock.Reified
open Nock.Framework
open Nock.Framework.Reify
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedComputeSemanticRealization
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyIOChain

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc : Fin (P.computeChipAt c).rap.w → F[X])
  (Qm : Fin (P.memoryChipAt c).rap.w → F[X])

/-- The 2a `compute_source` conjunct at the family env, from family satisfaction alone. -/
theorem compute_source_at (hacc : DeployedAcceptanceAt P c Qc Qm) (i : Fin (rows P)) :
    CorrectedComputeSourceObligations (rows P) (rowEnvAt P c Qc i)
      (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
        (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)) :=
  row_obligations_at P c Qc hacc.compute_satisfies i

theorem notLast_at (hacc : DeployedAcceptanceAt P c Qc Qm) (i : Fin (rows P))
    (hi : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows) :
    (rowEnvAt P c Qc i).baseTrace 12 = 0 := by
  have hbind := hacc.compute_satisfies.2 (1 : Fin 2)
  have hresources := P.optimized.exact_chip_resources
  dsimp only at hresources
  have hw0 : P.computeChip.rap.w = 303 := hresources.1
  have hw : (P.computeChipAt c).rap.w = 303 := (computeChipAt_width P c).trans hw0
  have hj12 : 12 < (P.computeChipAt c).rap.w := by omega
  change Qc ⟨12, hj12⟩ =
    Nock.Framework.lastRowMask P.optimized.family.problem.cfg.compRows_pos
      P.optimized.computeNodes at hbind
  have heval := congrArg (fun f : F[X] => f.eval (P.optimized.computeNodes i)) hbind
  rw [Nock.Framework.lastRowMask_eval P.optimized.family.problem.cfg.compRows_pos
    P.optimized.computeNodes P.optimized.computeNodes_injective] at heval
  have hne : i ≠
      ⟨P.optimized.family.problem.cfg.compRows - 1,
        Nat.sub_lt P.optimized.family.problem.cfg.compRows_pos (by omega)⟩ := by
    intro heq
    have hv := congrArg Fin.val heq
    simp only at hv
    omega
  simp only [hne, if_false] at heval
  show (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
    (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c)).trace 12 = 0
  simp only [envOfTrace, hj12, dite_true]
  exact heval

/-- The 2a `compute` conjunct at the family env, from family satisfaction alone. -/
theorem compute_at (hacc : DeployedAcceptanceAt P c Qc Qm) (i : Fin (rows P))
    (hi : (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows) :
    CorrectedDecodedTransitionSources (rowEnvAt P c Qc i) :=
  corrected_conditional_transition_soundness (compute_source_at P c Qc Qm hacc i)
    (notLast_at P c Qc Qm hacc i hi)

/-- The 2a `memory` conjunct at the family envs, from family satisfaction alone. -/
theorem memory_at (hacc : DeployedAcceptanceAt P c Qc Qm) (i : Fin (memRows P)) :
    (∀ g ∈ baseTransitionGates P.optimized.basis,
      g.eval (memEnvF P c Qm i) = 0) ∧
    (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
      g.eval (memEnvK P c Qm i) (memEnvF P c Qm i) = 0) :=
  ⟨base_at_family P c Qm hacc.memory_satisfies i, mixed_at_family P c Qm hacc.memory_satisfies i⟩

/-- All three gate conjuncts of the retyped target, packaged. -/
theorem family_target_gates (hacc : DeployedAcceptanceAt P c Qc Qm) :
    (∀ i : Fin (rows P),
      CorrectedComputeSourceObligations (rows P) (rowEnvAt P c Qc i)
        (envOfTrace Qc P.optimized.orbit.ω (P.optimized.computeNodes i)
          (computeChalValOfTuple P.optimized.basis c) (P.familyComputePublic c))) ∧
    (∀ i : Fin (rows P), (i : ℕ) + 1 < P.optimized.family.problem.cfg.compRows →
      CorrectedDecodedTransitionSources (rowEnvAt P c Qc i)) ∧
    (∀ i : Fin (memRows P),
      (∀ g ∈ baseTransitionGates P.optimized.basis, g.eval (memEnvF P c Qm i) = 0) ∧
      (∀ g ∈ mixedTransitionGates (F := F) (K := K) P.optimized.basis,
        g.eval (memEnvK P c Qm i) (memEnvF P c Qm i) = 0)) :=
  ⟨compute_source_at P c Qc Qm hacc, compute_at P c Qc Qm hacc, memory_at P c Qc Qm hacc⟩

end

end Nock.RedTeam.Batch883

#print axioms Nock.RedTeam.Batch883.family_target_gates
