/-
  Nock/NockVMROM/Thm54/StrategyOfTracesCore.lean

  `strategyOfTraces : ProductionStrategy`.
  Timestamp via `ofRawData`; execution template wraps `execOfTraces`
  (mentions `Qc`/`Qm`).  Tables = `decodeEx` on `Qc`; walks = decoded
  `ln` columns; topology = `sfTriple`/`memCell` of the labels.
-/
import Nock.NockVMROM.Thm54.ExecOfTraces
import Nock.NockVMROM.Thm54.FamilyComputeRows
import Nock.NockVMROM.Thm54.ProductionP8Containment
import Nock.NockVMROM.Thm54.ProductionRawVerifier
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.NockVMROM.Thm54.RawTopologyAIR
import Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
import Nock.NockVMROM.Thm54.PlusIOSegmentedRAP
import Nock.NockVMROM.Thm54.JointCoins
import Nock.Framework.NockInstances
import Mathlib.GroupTheory.OrderOfElement
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

namespace Nock.NockVMROM.Thm54.StrategyOfTracesCore

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ExecOfTraces
open Nock.NockVMROM.Thm54.FamilyComputeRows
open Nock.NockVMROM.Thm54.StrategyOfTraces
open Nock.NockVMROM.Thm54.DeployedComputeRows
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage
open Nock.NockVMROM.Thm54.OptimizedComputeHostileAccumulator
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.NockVMROM.Thm54.RawTopologyAIR
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open scoped BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}
  (P : OptimizedFullStrictNockVMROMPackage F K hOrb)

/-! ## Templates off `execOfTraces` -/

/-- Relative wrap: `lnPrevExponent = 0`, so specialize is taken against the
published `ln_prev`. -/
def wrapComputeLabel (row : State × DTcomp K) : ComputeRowTemplate (K := K) where
  timestamp :=
    { state := row.1
      lnPrevExponent := 0
      lnExponent := Nock.Framework.recordCount row.1
      recordExponent := fun i => (i : ℕ) + 1 }
  placeholder := row

/-- Case (b) discrete log of a committed timestamp in `⟨α⟩`.  Used only by the hostile memory wrap. -/
noncomputable def memExponent (α ts : K) : ℕ :=
  if h : ∃ n : ℕ, n < orderOf α ∧ α ^ n = ts then
    Nat.find h
  else 0

theorem memExponent_pow {α ts : K}
    (h : ∃ n : ℕ, n < orderOf α ∧ α ^ n = ts) :
    α ^ memExponent α ts = ts := by
  simp only [memExponent, h, ↓reduceDIte]
  exact (Nat.find_spec h).2

/-- Membership / finder form used by the hostile wrap. -/
theorem memExponent_spec {α ts : K}
    (h : ∃ e : ℕ, e < orderOf α ∧ α ^ e = ts) :
    α ^ memExponent α ts = ts :=
  memExponent_pow h

/-- Hostile memory wrap: `recordExponent` is the discrete log of the
committed `mem.ts` in `⟨α⟩`, so `specialize` recovers the timestamp.  Honest templates are untouched. -/
def wrapMemoryLabel (α : K)
    (row : MState × DTmem K) : MemoryRowTemplate (K := K) where
  timestamp :=
    { state := row.1
      recordExponent := memExponent α row.2.2.mem.ts }
  placeholder := row

/-- Config template of `cfgOfTraces` with `z` overwritten by the seed. -/
def cfgTemplateOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (z : K) :
    ExactConfigTemplate F K :=
  configTemplateOf (cfgOfTraces P Qc Qm c) z

theorem cfgTemplateOfTraces_z
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (z : K) :
    (cfgTemplateOfTraces P Qc Qm c z).challenges.z = z :=
  rfl

/-- Execution template: inverse-BFS trees of `execOfTraces`, wrapped. -/
def execTemplateOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (z : K) :
    ExactExecutionTemplate (cfgTemplateOfTraces P Qc Qm c z) where
  computeTree :=
    mapNTree wrapComputeLabel (execOfTraces P Qc Qm c h).computeTree
  memoryForest :=
    (execOfTraces P Qc Qm c h).memoryForest.map
      (mapNTree (wrapMemoryLabel (alphaM c.1)))
  memoryForest_nonempty := by
    intro hempty
    exact (execOfTraces P Qc Qm c h).memoryForest_nonempty (List.map_eq_nil_iff.mp hempty)
  memory_root_count := by
    simp only [List.length_map, cfgTemplateOfTraces, configTemplateOf]
    exact (execOfTraces P Qc Qm c h).memory_root_count
  compute_bfs_length := by
    have hlen := (execOfTraces P Qc Qm c h).compute_bfs_length
    have hmap :
        (bfsForest
          [mapNTree wrapComputeLabel (execOfTraces P Qc Qm c h).computeTree]).length =
        (bfsForest [(execOfTraces P Qc Qm c h).computeTree]).length := by
      rw [show [mapNTree wrapComputeLabel (execOfTraces P Qc Qm c h).computeTree] =
            [(execOfTraces P Qc Qm c h).computeTree].map (mapNTree wrapComputeLabel) from rfl,
        bfsForest_mapNTree, List.length_map]
    simpa [cfgTemplateOfTraces, configTemplateOf, hmap] using hlen
  memory_bfs_length := by
    have hlen := (execOfTraces P Qc Qm c h).memory_bfs_length
    have hmap :
        (bfsForest
          ((execOfTraces P Qc Qm c h).memoryForest.map
            (mapNTree (wrapMemoryLabel (alphaM c.1))))).length =
        (bfsForest (execOfTraces P Qc Qm c h).memoryForest).length := by
      rw [bfsForest_mapNTree, List.length_map]
    simpa [cfgTemplateOfTraces, configTemplateOf, hmap] using hlen

/-- Data-only timestamp: claim from the decoded traces; templates from
`execOfTraces`; `z` is the seed (`ofRawData`). -/
def timestampOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K) :=
  DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
    (publicClaimOf P Qc Qm)
    (fun seed => cfgTemplateOfTraces P Qc Qm c seed.1)
    (fun seed => execTemplateOfTraces P Qc Qm c h seed.1)
    (fun _ => rfl)

theorem timestampOfTraces_claim
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    (timestampOfTraces P Qc Qm c h).claim = publicClaimOf P Qc Qm :=
  rfl

theorem timestampOfTraces_sampledSeed
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (z : K) (hz : z ≠ 0) :
    ((timestampOfTraces P Qc Qm c h).afterSeed ⟨z, hz⟩).configTemplate.challenges.z = z :=
  rfl

/-! ## Family / tables / walks / topology off `(Qc, Qm)` -/

/-- Node encoders are the paper encoding (`NodeEncoding`), not `P.walkFamily`.
`requests` is the compute public terminal (`computePublic` block 6..8).
`responses` is last-row memory `memAcc` (role 44, the `LN`/`LL` accumulator).
`outMem` is first-row `icur` (role 28).  No `(0 : K) * length`. -/
def familyDataOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    AlphaMFamilyData (timestampOfTraces P Qc Qm c h) z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode P.stateTagChar
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode P.stateTagChar
  requests :=
    algebraMap K (IOField K)
      (∑ k : Fin 3,
          P.optimized.computePublic (6 + (k : ℕ)) • P.optimized.basis k)
  responses :=
    algebraMap K (IOField K)
      ((memorySourceEnvAt P c Qm
        ⟨P.optimized.family.problem.cfg.memRows - 1,
          Nat.pred_lt (Nat.pos_iff_ne_zero.mp
            P.optimized.family.problem.cfg.memRows_pos)⟩).trace 44)
  outMem :=
    algebraMap K (IOField K)
      ((memorySourceEnvAt P c Qm
        ⟨0, P.optimized.family.problem.cfg.memRows_pos⟩).trace 28)

/-- Compute extras = `decodeEx` of each `Qc` row. -/
def tablesOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    RawTableArrays (familyDataOfTraces P Qc Qm c h z hz α lmb).base where
  compute := fun i =>
    if hj : i.val < P.optimized.family.problem.cfg.compRows then
      decodeEx (rowEnvAt P c (familyQc P c Qc) ⟨i.val, hj⟩)
    else
      decodeEx (rowEnvAt P c (familyQc P c Qc)
        ⟨0, P.optimized.family.problem.cfg.compRows_pos⟩)
  memory := fun _ => 0

/-- Walk columns from the decoded `Qc`/`Qm` labels (constant in later coins). -/
def walksOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    RawWalkArrays K where
  computeLn := fun i => (lblC P Qc c i).2.2.1.ln
  computeCount := fun i => (lblC P Qc c i).2.2.1.ln_prev
  computeAcc := fun _ => 0
  memoryLn := fun i => (lblM P Qm c i).2.2.ipre
  memoryCount := fun i => (lblM P Qm c i).2.2.icur
  memoryAcc := fun _ => 0

/-- IO arrays read off the traces: `progAcc` is compute `acc_after`
(role 60 / raw 73), `memAcc` is memory role 44, `multiplicity` from
the `read_root` selector (base column 2). Mentions `Qc`/`Qm`. -/
def ioOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    RawIOArrays (familyDataOfTraces P Qc Qm c h z hz α lmb).base (ringChar K) where
  multiplicity := fun j =>
    let i := j.val % P.optimized.family.problem.cfg.memRows
    if hlt : i < P.optimized.family.problem.cfg.memRows then
      if (memoryBaseEnvAt P c Qm ⟨i, hlt⟩).trace 2 = 1 then 1 else 0
    else
      0
  progAcc := fun i =>
    if hlt : i < P.optimized.family.problem.cfg.compRows then
      algebraMap K (IOField K)
        ((rowEnvAt P c (familyQc P c Qc) ⟨i, hlt⟩).toSourceEnv.trace
          accAfterIndex)
    else
      0
  memAcc := fun i =>
    if hlt : i < P.optimized.family.problem.cfg.memRows then
      algebraMap K (IOField K)
        ((memorySourceEnvAt P c Qm ⟨i, hlt⟩).trace 44)
    else
      0

def afterAlphaMOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    AlphaMCommitment (p := ringChar K) (timestampOfTraces P Qc Qm c h) z hz α lmb where
  familyData := familyDataOfTraces P Qc Qm c h z hz α lmb
  tables := tablesOfTraces P Qc Qm c h z hz α lmb
  io := ioOfTraces P Qc Qm c h z hz α lmb

/-- Child payloads from `sfTriple` / `memCell` of the decoded labels. -/
def topologyOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    RawTopologyArrays (afterAlphaMOfTraces P Qc Qm c h z hz α lmb).familyData.base where
  compute :=
    { childPayload := fun i slot =>
        match clabC P Qc c (i.val + 1) slot.val with
        | some child => ⟨child.2.2.1.s, child.2.2.1.f, child.2.2.1.e⟩
        | none => ComputeLinkPayload.zero }
  memory :=
    { childPayload := fun i slot =>
        match clabM P Qm c (i.val + 1) slot.val with
        | some child => child.2.2.pt
        | none => Cell.zero }

def rawVerifierOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    TemplateRawJointSoundness.Strategy F K (ringChar K) where
  timestamp := timestampOfTraces P Qc Qm c h
  afterAlphaM := afterAlphaMOfTraces P Qc Qm c h
  afterCoins := fun _ _ _ => walksOfTraces P Qc Qm c

def verifierOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K) where
  raw := rawVerifierOfTraces P Qc Qm c h
  topologyAfterAlphaM := topologyOfTraces P Qc Qm c h

/-- `strategyOfTraces : ProductionStrategy`, from the traces.  Not `P.strategy`.

**** no binding hypothesis.  Before the split this took
`hbinds : TracesBindsHyps` (`BindsAt` at EVERY seed), which is refuted at `3 ≤ |K|`: the decoded
execution writes the sampled seed into every memory row, so binding forces `z = nprSeed c.1`
(`Batch573.bindsAt_traces_forces_seed`).  The seed-local binding is
`strategyOfTraces_bindsAtCoin`, a theorem given the tree bindings. -/
def strategyOfTraces
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    ProductionStrategy F K where
  verifier := verifierOfTraces P Qc Qm c h
  skeleton := decodedSkeletonOf P Qc Qm
  publicClaim_eq := rfl

theorem strategyOfTraces_claim
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) :
    (strategyOfTraces P Qc Qm c h).verifier.raw.claim =
      publicClaimOf P Qc Qm :=
  rfl

/-- The `(z, α, λ)`-specialized hostile execution IS the strategy's (definitional; this is what
`Batch531.tracesSpecializedExec` named before the fold). -/
theorem strategyOfTraces_specializedExec
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c) (z : K) (hz : z ≠ 0) (α lmb : K) :
    (strategyOfTraces P Qc Qm c h).specializedExec z hz α lmb =
      (specializedProblem (timestampOfTraces P Qc Qm c h) z hz α lmb).exec :=
  rfl

theorem strategyOfTraces_bindsAtCoin
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hc : ∀ hz : nprSeed c.1 ≠ 0,
      SemanticStrategy.ComputeTreeBinds (nprSeed c.1)
        (decodedSkeletonOf P Qc Qm).computeTree
        (specializedProblem (timestampOfTraces P Qc Qm c h)
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).exec.computeTree)
    (hm : ∀ hz : nprSeed c.1 ≠ 0,
      List.Forall₂ (SemanticStrategy.MemoryTreeBinds (nprSeed c.1))
        (decodedSkeletonOf P Qc Qm).memoryForest
        (specializedProblem (timestampOfTraces P Qc Qm c h)
          (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).exec.memoryForest) :
    (strategyOfTraces P Qc Qm c h).BindsAtCoin c.1 c.2.2.2.lambda :=
  fun hz =>
    SemanticStrategy.BindsAt.ofTreeBindings
      (specializedProblem_seed _ _ hz _ _) (hc hz) (hm hz)

/-- `z_eq` is definitional: the template writes `z := seed`. -/
theorem strategyOfTraces_z_eq
    (Qc : Fin P.computeChip.rap.w → F[X])
    (Qm : Fin P.memoryChip.rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps P Qc Qm c)
    (hz : nprSeed c.1 ≠ 0) :
    ((strategyOfTraces P Qc Qm c h).specializedCfg
        (nprSeed c.1) hz (alphaM c.1) c.2.2.2.lambda).challenges.z =
      nprSeed c.1 :=
  rfl

end

end Nock.NockVMROM.Thm54.StrategyOfTracesCore
