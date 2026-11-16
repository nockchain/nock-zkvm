/-
  Nock/RedTeam/Batch912Thm54SpecializeARoute.lean

  The trace-built template's memory forest is `wrapMemoryLabel` over the decoded forest, so

  Consumers of `hW` and their restatement (each compiled here without `hW`):
  * `Batch509.specialized_memoryForest_eq` → `specialized_memoryForest_eq_encode` (restatement;
    the true shape of the encoded forest) and `execA_memoryForest_eq` (the A-view equality);
  * `Batch509.wrapSpecializeJoin` / `specializedMemoryTopology_of_exec` → `wrapSpecializeJoinA`
    (`MemoryExactTopologyTopo` of the A-view execution);
  * `Batch761.specialized_memorySharedInputs` → `specialized_memorySharedInputs_noHW` (the ENCODED
    execution, since `encodeRow` never touches the inputs) and `memorySharedInputsA`;
  * `Batch761.bridgeTwin_of_wrapSpecializeJoin` / `bridgeTwin_of_deployed` → `bridgeTwinA`,
    `bridgeTwinA_of_deployed` (`ExactAxisBridgeLocalTopo` of the A-view execution; deployed form's
    residual is `hpow` only).
-/
import Nock.RedTeam.Batch761Thm54BridgeTwin
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch912

open scoped Polynomial
open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.AxisBridgeLocalTopo
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.ResponseTsMemPowers
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

section Views

variable (h : TracesWalkHyps P Qc₀ Qm₀ c)

/-- The a-bearing view of the trace-built execution at the tuple's `(α, λ)`. -/
abbrev execA :=
  (execTemplateOfTraces P Qc₀ Qm₀ c h (nprSeed c.1)).specializeA (alphaM c.1) c.2.2.2.lambda

variable
  (htop : ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest,
    RVTWithArity (FmemTopo (K := K)) t)
  (hpow : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
    memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
      MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts)

include htop hpow in
/-- **The a-bearing view is the decoded forest** (no `hW`). -/
theorem execA_memoryForest_eq :
    (execA P c Qc₀ Qm₀ h).memoryForest = (execOfTraces P Qc₀ Qm₀ c h).memoryForest := by
  change ((execOfTraces P Qc₀ Qm₀ c h).memoryForest.map
      (mapNTree (wrapMemoryLabel (alphaM c.1)))).map
      (mapNTree (fun row => row.specializeA (alphaM c.1))) = _
  rw [List.map_map]
  change (reconForest P.optimized.family.problem.cfg.kMem
      (foM P Qm₀ c) (lblM P Qm₀ c) P.optimized.family.problem.cfg.memRows).map _ =
    reconForest P.optimized.family.problem.cfg.kMem
      (foM P Qm₀ c) (lblM P Qm₀ c) P.optimized.family.problem.cfg.memRows
  have hcomp : ((mapNTree (fun row : MemoryRowTemplate (K := K) => row.specializeA (alphaM c.1))) ∘
      (mapNTree (wrapMemoryLabel (alphaM c.1)))) =
      mapNTree (fun r => (wrapMemoryLabel (alphaM c.1) r).specializeA (alphaM c.1)) := by
    funext t
    exact Batch509.mapNTree_comp (wrapMemoryLabel (alphaM c.1))
      (fun row => row.specializeA (alphaM c.1)) t
  rw [hcomp, Batch509.mapNTree_reconForest]
  refine Batch509.reconForest_eq_of_lbl P.optimized.family.problem.cfg.kMem
    (foM P Qm₀ c) P.optimized.family.problem.cfg.memRows ?_
  intro i
  exact Batch509.wrap_idA_lblM_of_topology P c Qc₀ Qm₀ h htop hpow i

include htop hpow in
/-- **The encoded specialized forest is `encodeRow λ` over the decoded forest** (no `hW`). -/
theorem specialized_memoryForest_eq_encode (hz : nprSeed c.1 ≠ 0) :
    ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).memoryForest =
      (execOfTraces P Qc₀ Qm₀ c h).memoryForest.map
        (mapNTree (MemoryRowTemplate.encodeRow c.2.2.2.lambda)) := by
  rw [Batch509.specialized_memoryForest_map]
  change (reconForest P.optimized.family.problem.cfg.kMem
      (foM P Qm₀ c) (lblM P Qm₀ c) P.optimized.family.problem.cfg.memRows).map _ =
    (reconForest P.optimized.family.problem.cfg.kMem
      (foM P Qm₀ c) (lblM P Qm₀ c) P.optimized.family.problem.cfg.memRows).map _
  rw [Batch509.mapNTree_reconForest, Batch509.mapNTree_reconForest]
  refine Batch509.reconForest_eq_of_lbl P.optimized.family.problem.cfg.kMem
    (foM P Qm₀ c) P.optimized.family.problem.cfg.memRows ?_
  intro i
  change MemoryRowTemplate.encodeRow c.2.2.2.lambda
      ((wrapMemoryLabel (alphaM c.1) (lblM P Qm₀ c i)).specializeA (alphaM c.1)) = _
  rw [Batch509.wrap_idA_lblM_of_topology P c Qc₀ Qm₀ h htop hpow i]

include htop hpow in
/-- **`wrapSpecializeJoin` on the A-view** (no `hW`). -/
theorem wrapSpecializeJoinA : MemoryExactTopologyTopo (execA P c Qc₀ Qm₀ h) := by
  intro t ht
  rw [execA_memoryForest_eq P c Qc₀ Qm₀ h htop hpow] at ht
  exact htop t ht

/-- Shared inputs of any execution whose forest's labels are all `f (lblM j)` for an `f` that
keeps `.2.1`. -/
theorem sharedInputs_of_forest {cfg : ExactConfig F K} (exec : ExactExecution cfg)
    (f : MemoryTable.MState × MemoryTable.DTmem K → MemoryTable.MState × MemoryTable.DTmem K)
    (hf : ∀ r, (f r).2.1 = r.2.1)
    (hforest : exec.memoryForest = (execOfTraces P Qc₀ Qm₀ c h).memoryForest.map (mapNTree f))
    (hinp : cfg.challenges.memoryInputs =
      { z := nprSeed c.1, β := -(c.2.2.2.interPole), γ := c.2.1.1 }) :
    MemorySharedInputs exec := by
  intro row hrow
  rw [ExactExecution.memoryRows, List.mem_map] at hrow
  obtain ⟨t', ht', rfl⟩ := hrow
  rw [mem_bfsForest] at ht'
  obtain ⟨root, hroot, hin⟩ := ht'
  rw [hforest] at hroot
  change root ∈ (reconForest P.optimized.family.problem.cfg.kMem (foM P Qm₀ c) (lblM P Qm₀ c)
    P.optimized.family.problem.cfg.memRows).map (mapNTree f) at hroot
  rw [Batch509.mapNTree_reconForest, reconForest, List.mem_map] at hroot
  obtain ⟨i, _, rfl⟩ := hroot
  obtain ⟨j, hj⟩ := Batch761.inTree_buildTF_label _ _ _ _ _ _ hin i rfl
  rw [hj, hf, Batch761.lblM_inputs, hinp]

include htop hpow in
/-- **Shared inputs at the ENCODED specialized execution, without `hW`.** -/
theorem specialized_memorySharedInputs_noHW (hz : nprSeed c.1 ≠ 0) :
    MemorySharedInputs ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda) :=
  sharedInputs_of_forest P c Qc₀ Qm₀ h _ (MemoryRowTemplate.encodeRow c.2.2.2.lambda)
    (fun r => by unfold MemoryRowTemplate.encodeRow; rfl)
    (specialized_memoryForest_eq_encode P c Qc₀ Qm₀ h htop hpow hz)
    (specializedCfg_memoryInputs P Qc₀ Qm₀ c h hz)

include htop hpow in
/-- **Shared inputs at the A-view, without `hW`.** -/
theorem memorySharedInputsA (hz : nprSeed c.1 ≠ 0) : MemorySharedInputs (execA P c Qc₀ Qm₀ h) :=
  sharedInputs_of_forest P c Qc₀ Qm₀ h _ id (fun _ => rfl)
    (by
      rw [execA_memoryForest_eq P c Qc₀ Qm₀ h htop hpow]
      have hid : (mapNTree (id : MemoryTable.MState × MemoryTable.DTmem K →
          MemoryTable.MState × MemoryTable.DTmem K)) = id := funext Batch509.mapNTree_id
      rw [hid, List.map_id])
    (specializedCfg_memoryInputs P Qc₀ Qm₀ c h hz)

include htop hpow in
/-- **The bridge twin on the A-view** (no `hW`). -/
theorem bridgeTwinA (hz : nprSeed c.1 ≠ 0)
    (i : Fin ((cfgTemplateOfTraces P Qc₀ Qm₀ c (nprSeed c.1)).specialize
      (alphaM c.1) c.2.2.2.lambda).kMem) :
    ExactAxisBridgeLocalTopo _ (execA P c Qc₀ Qm₀ h) i :=
  exactAxisBridgeLocalTopo (wrapSpecializeJoinA P c Qc₀ Qm₀ h htop hpow)
    (memorySharedInputsA P c Qc₀ Qm₀ h htop hpow hz) i

end Views

section Deployed

variable
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

include hz in
/-- **Deployed form on the A-view.**  Deployed acceptance and `c ∉ optimizedFailureEvent`
discharge `htop` (`Batch501.memoryTopology_of_deployed_of_good`, as in `Batch761`); the residual is
`hpow` only (`Batch844.hpow_of_family_acceptance`). No `WrapMemoryIdentity`. -/
theorem bridgeTwinA_of_deployed
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hpow : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
        MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts)
    (i : Fin ((cfgTemplateOfTraces P Qc₀ Qm₀ c (nprSeed c.1)).specialize
      (alphaM c.1) c.2.2.2.lambda).kMem) :
    ExactAxisBridgeLocalTopo _
      (execA P c Qc₀ Qm₀
        (Batch489.tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth
          hacc hgood)) i :=
  bridgeTwinA P c Qc₀ Qm₀ _
    (Batch501.memoryTopology_of_deployed_of_good P c Qc₀ Qm₀ hsatC hsatM hchar hz hax hbasis
      hwidth hacc hgood)
    hpow hz i

end Deployed

end

end Nock.RedTeam.Batch912

#print axioms Nock.RedTeam.Batch912.execA_memoryForest_eq
#print axioms Nock.RedTeam.Batch912.specialized_memoryForest_eq_encode
#print axioms Nock.RedTeam.Batch912.wrapSpecializeJoinA
#print axioms Nock.RedTeam.Batch912.specialized_memorySharedInputs_noHW
#print axioms Nock.RedTeam.Batch912.memorySharedInputsA
#print axioms Nock.RedTeam.Batch912.bridgeTwinA
#print axioms Nock.RedTeam.Batch912.bridgeTwinA_of_deployed
