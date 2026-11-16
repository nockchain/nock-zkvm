/-
  Nock/RedTeam/Batch761Thm54BridgeTwin.lean

  **C1-3 route (i) (lane `bridge-twin`): the β-free axis-bridge twin, fed by
  `Batch509.wrapSpecializeJoin`.**

  `AxisBridgeLocalTopo.ExactAxisBridgeLocalTopo` is the β-free twin of
  `AxisSoundness.ExactAxisBridgeLocal` (`rvt : RVTWithArity FmemTopo`, the other two fields
  verbatim).  This file supplies its instance on the wrap-then-specialized execution of the
  decoded traces — the execution Part 2 reasons about:

  * `inTree_buildTF_label` — every node of a reconstructed tree carries a label of `lbl`;
  * `lblM_inputs` — every decoded memory label carries the constant inputs
    `{z := nprSeed, β := −interPole, γ}` (definitional: `lblMAt` writes them);
  * `specialized_memorySharedInputs` — hence `MemorySharedInputs` at the specialized execution,
    with no `Vmem` / `interV`: the shared-inputs field is a definitional fact of the decode, not
    a row-acceptance fact;
  * `bridgeTwin_of_wrapSpecializeJoin` — the twin at every root of the specialized execution, from
    exactly `wrapSpecializeJoin`'s hypotheses (`htop` β-free topology of `execOfTraces`, the parked
    `hW`, `hpow`);

  No β-dependent fact is used anywhere in this file.
-/
import Nock.NockVMROM.Thm54.AxisBridgeLocalTopo
import Nock.RedTeam.Batch501Thm54MemoryTopology
import Nock.RedTeam.Batch509Thm54WrapSpecialize
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch761

open scoped Polynomial
open Nock Nock.Walk Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.AxisBridgeLocalTopo
open Nock.NockVMROM.Thm54.MemoryTopoBetaFree
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.StrategyOfTracesCore
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.WrapMemoryConjuncts
open Nock.NockVMROM.Thm54.FamilyMemoryRows
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.ResponseTsMemPowers
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.DeployedAcceptance
open Nock.NockVMROM.Thm54.OptimizedComputeFinalTrace
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.Framework
open Nock.Framework.Reify
open MonolithicRAP

/-! ## Generic: every node of a reconstructed tree carries a label of `lbl` -/

theorem inTree_buildTF_label {LT : Type*} (kroots : ℕ) (fo : ℕ → ℕ) (lbl : ℕ → LT) (hh : ℕ) :
    ∀ t s : NTree LT, InTree t s →
      ∀ i, t = buildTF kroots fo lbl hh i → ∃ j, NTree.label s = lbl j := by
  intro t s hts
  induction hts with
  | here c =>
      intro i hc
      exact ⟨i, by rw [hc, buildTF_label]⟩
  | sub hs _ ih =>
      intro i hc
      rw [hc, buildTF_children, List.mem_map] at hs
      obtain ⟨j, _, rfl⟩ := hs
      exact ih j rfl

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)
  (c : OptimizedProductionChallengeTuple K F)
  (Qc₀ : Fin P.computeChip.rap.w → F[X])
  (Qm₀ : Fin P.memoryChip.rap.w → F[X])

/-- Every decoded memory label carries the constant inputs `lblMAt` writes. -/
theorem lblM_inputs (j : ℕ) :
    (lblM P Qm₀ c j).2.1 =
      { z := nprSeed c.1, β := -(c.2.2.2.interPole), γ := c.2.1.1 } := by
  unfold lblM
  split <;> rfl

section Specialized

variable (h : TracesWalkHyps P Qc₀ Qm₀ c) (hz : nprSeed c.1 ≠ 0)

/-- **Shared inputs at the specialized execution, β-free.**  Under `wrapSpecializeJoin`'s
hypotheses the specialized forest is the decoded forest (`Batch509.specialized_memoryForest_eq`),
whose every label is some `lblM P Qm₀ c j`, whose inputs are the specialized config's
`memoryInputs` (`specializedCfg_memoryInputs`, `rfl`). -/
theorem specialized_memorySharedInputs
    (htop : ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest,
      RVTWithArity (FmemTopo (K := K)) t)
    (hW : Batch509.WrapMemoryIdentity P c Qm₀)
    (hpow : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
        MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts) :
    MemorySharedInputs ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda) := by
  intro row hrow
  rw [ExactExecution.memoryRows, List.mem_map] at hrow
  obtain ⟨t', ht', rfl⟩ := hrow
  rw [mem_bfsForest] at ht'
  obtain ⟨root, hroot, hin⟩ := ht'
  rw [Batch509.specialized_memoryForest_eq P c Qc₀ Qm₀ h hz htop hW hpow] at hroot
  change root ∈ reconForest P.optimized.family.problem.cfg.kMem (foM P Qm₀ c) (lblM P Qm₀ c)
    P.optimized.family.problem.cfg.memRows at hroot
  rw [reconForest, List.mem_map] at hroot
  obtain ⟨i, _, rfl⟩ := hroot
  obtain ⟨j, hj⟩ := inTree_buildTF_label _ _ _ _ _ _ hin i rfl
  rw [hj, lblM_inputs]
  exact (specializedCfg_memoryInputs P Qc₀ Qm₀ c h hz).symm

/-- **The twin instance fed by `Batch509.wrapSpecializeJoin`.**  At every root of the
wrap-then-specialized execution, `ExactAxisBridgeLocalTopo` holds from exactly
`wrapSpecializeJoin`'s hypotheses. -/
theorem bridgeTwin_of_wrapSpecializeJoin
    (htop : ∀ t ∈ (execOfTraces P Qc₀ Qm₀ c h).memoryForest,
      RVTWithArity (FmemTopo (K := K)) t)
    (hW : Batch509.WrapMemoryIdentity P c Qm₀)
    (hpow : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
        MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts)
    (i : Fin ((strategyOfTraces P Qc₀ Qm₀ c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).kMem) :
    ExactAxisBridgeLocalTopo _
      ((strategyOfTraces P Qc₀ Qm₀ c h).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda) i :=
  exactAxisBridgeLocalTopo
    (Batch509.wrapSpecializeJoin P c Qc₀ Qm₀ h hz htop hW hpow)
    (specialized_memorySharedInputs P c Qc₀ Qm₀ h hz htop hW hpow) i

end Specialized

section Deployed

variable
  (hsatC : RAP.SatisfiesWithPreprocessing (P.computeChipAt c) (familyQc P c Qc₀))
  (hsatM : RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) (familyQm P c Qm₀))
  (hchar : MemStateTagChar F)
  (hz : nprSeed c.1 ≠ 0)
  (hax : FormRAxisBound P.optimized.sampled P.optimized.basis)
  (hbasis : FormRBasis P.optimized.basis)
  (hwidth : FormRWidth F)

/-- **Deployed form.**  Deployed acceptance and `c ∉ optimizedFailureEvent` discharge `htop`
(`Batch501.memoryTopology_of_deployed_of_good`); the residuals are the parked wrap identity `hW`
and active-row `MemPower` `hpow`, both pre-existing (no β-dependent premise). -/
theorem bridgeTwin_of_deployed
    (hacc : DeployedAcceptanceAt P c (familyQc P c Qc₀) (familyQm P c Qm₀))
    (hgood : c ∉ P.optimizedFailureEvent Qc₀ Qm₀)
    (hW : Batch509.WrapMemoryIdentity P c Qm₀)
    (hpow : ∀ i, 1 ≤ i → i ≤ P.optimized.family.problem.cfg.memRows →
      memoryMemRecKind (lblM P Qm₀ c i).1 = .active →
        MemPower (alphaM c.1) (lblM P Qm₀ c i).2.2.mem.ts)
    (i : Fin ((strategyOfTraces P Qc₀ Qm₀ c
        (Batch489.tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth
          hacc hgood)).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).kMem) :
    ExactAxisBridgeLocalTopo _
      ((strategyOfTraces P Qc₀ Qm₀ c
          (Batch489.tracesWalkHyps_of_deployed P c Qc₀ Qm₀ hsatC hsatM hchar hax hbasis hwidth
            hacc hgood)).specializedExec
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda) i :=
  bridgeTwin_of_wrapSpecializeJoin P c Qc₀ Qm₀ _ hz
    (Batch501.memoryTopology_of_deployed_of_good P c Qc₀ Qm₀ hsatC hsatM hchar hz hax hbasis
      hwidth hacc hgood)
    hW hpow i

end Deployed

end

end Nock.RedTeam.Batch761

#print axioms Nock.RedTeam.Batch761.inTree_buildTF_label
#print axioms Nock.RedTeam.Batch761.specialized_memorySharedInputs
#print axioms Nock.RedTeam.Batch761.bridgeTwin_of_wrapSpecializeJoin
#print axioms Nock.RedTeam.Batch761.bridgeTwin_of_deployed
