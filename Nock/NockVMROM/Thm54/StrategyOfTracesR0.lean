/-
  Nock/NockVMROM/Thm54/StrategyOfTracesR0.lean

  Additive: nothing is re-pointed; the lifted `StrategyOfTracesLift.strategyOfTraces` and the
  originals stay.

  **Why.**

  * the record exponent is `natLift reqIdx` (memory base column `181`, round 0);
  * the stored axis is the Nock axis `a` RECOVERED from the round-0 certificate of the compute
    request that exponent names: the exponent locator `DecodedLambdaEvent.locateExp` and the C-a
    slot map give `(m, c) = (decodedShift e, decodedBits e)` (compute selectors `0..9`, certificate
    block `202..270`), and `a := certAxis m c` is the integer with MSB at position `m` and lower
    bits `c₁ … c_m`.

  The WRAP's own metadata (record exponent, recovered axis) reads round-0 columns only: no `ts`, no
  `nounByFP`, no challenge.  **Scope**: "round 0" is a property of the memory-wrap
  metadata ONLY.  The specialization of the wrapped row stores `formRT λ a = λ^m` and `formRC λ a`, i.e. the
  decoded `(T, C')` when the certificate is padded and below `p` (`Batch974`'s `wrapJoin`), never a
  re-encoded `T`.

  **The built strategy.**  §C restates `StrategyOfTracesLift`'s `familyDataOfTraces … strategyOfTraces`
  chain over an arbitrary timestamp strategy `Ts` (the bodies never read `Ts`, only their types do),
  so that the lifted strategy is the instance at `timestampOfTraces` (`rfl`, `Batch970`) and
  `strategyOfTracesR0` is the instance at `timestampOfTracesR0`, whose execution template differs
  from the lifted one ONLY in the memory forest's wrap.  The compute template, the configuration,
  the skeleton and the public claim are the lifted ones verbatim.

  Paper: the paper (axis doubling), `:1413` (memory timestamps), `:1420-1424`,
  `:2054-2082` (`V_mem`), `:2117` (`mem_record`).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesLift
import Nock.NockVMROM.Thm54.DecodedLambdaEvent
import Nock.NockVMROM.Thm54.RecordCarrier

namespace Nock.NockVMROM.Thm54.StrategyOfTracesR0

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
open Nock.Reified
open Nock.Framework
open Nock.ComputeTable
open Nock.MemoryTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.OptimizedStrictPackage
open Nock.NockVMROM.Thm54.MonolithicRAP
open Nock.NockVMROM.Thm54.OptimizedComputeCorrectedFinal
open Nock.NockVMROM.Thm54.OptimizedMemoryGateBasis
open Nock.NockVMROM.Thm54.OptimizedMemoryRAP
open Nock.NockVMROM.Thm54.DeployedChipFamily
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateRawJointSoundness
open Nock.NockVMROM.Thm54.ProductionP8Containment
open Nock.NockVMROM.Thm54.ProductionRawVerifier
open Nock.NockVMROM.Thm54.RawTopologyAIR
open Nock.NockVMROM.Thm54.DecodedLambdaEvent
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.OptimizedComputeFiniteIOGates
open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedSectionVars false

set_option quotPrecheck false

/-- `P.computeChip` at `O := P.optimized` (as in `StrategyOfTracesLift`). -/
local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

/-- `P.memoryChip` at `O := P.optimized` (as in `StrategyOfTracesLift`). -/
local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

noncomputable section

/-! ## §A  The certificate axis (pure arithmetic) -/

/-- **The axis of a Form R certificate** `(m, c)`: the integer whose binary expansion is `1`
followed by `c₁ … c_m` (MSB first), i.e. `2^m + Σ_{j<m} c_{j+1}·2^{m−1−j}`.  It inverts
`(formRCertShift, formRCertBit)` (`formRCertShift_certAxis`, `formRCertBit_certAxis`). -/
def certAxis : ℕ → (ℕ → Bool) → ℕ
  | 0, _ => 1
  | m + 1, c => 2 * certAxis m c + (if c (m + 1) then 1 else 0)

theorem certAxis_pos (m : ℕ) (c : ℕ → Bool) : 0 < certAxis m c := by
  induction m with
  | zero => simp [certAxis]
  | succ m ih => simp only [certAxis]; omega

theorem certAxis_lt (m : ℕ) (c : ℕ → Bool) : certAxis m c < 2 ^ (m + 1) := by
  induction m with
  | zero => simp [certAxis]
  | succ m ih =>
      simp only [certAxis, pow_succ]
      split_ifs <;> omega

theorem certAxis_ge (m : ℕ) (c : ℕ → Bool) : 2 ^ m ≤ certAxis m c := by
  induction m with
  | zero => simp [certAxis]
  | succ m ih =>
      simp only [certAxis, pow_succ]
      split_ifs <;> omega

theorem size_certAxis (m : ℕ) (c : ℕ → Bool) : Nat.size (certAxis m c) = m + 1 := by
  apply le_antisymm
  · exact Nat.size_le.mpr (certAxis_lt m c)
  · exact Nat.lt_size.mpr (certAxis_ge m c)

/-- The shift of the certificate axis is `m`. -/
theorem formRCertShift_certAxis (m : ℕ) (c : ℕ → Bool) :
    MemoryTable.formRCertShift (certAxis m c) = m := by
  unfold MemoryTable.formRCertShift
  rw [size_certAxis]; rfl

/-- Bit `k` (LSB `0`) of the certificate axis, `k < m`, is `c_{m−k}`. -/
theorem testBit_certAxis (m : ℕ) (c : ℕ → Bool) :
    ∀ k, k < m → (certAxis m c).testBit k = c (m - k) := by
  induction m with
  | zero => intro k hk; omega
  | succ m ih =>
      intro k hk
      simp only [certAxis]
      rcases k with _ | k
      · rw [show (2 * certAxis m c + if c (m + 1) then 1 else 0) =
            (if c (m + 1) then 1 else 0) + 2 * certAxis m c by ring,
          Nat.testBit_zero]
        split_ifs with h <;> simp [h, Nat.add_mul_mod_self_left]
      · have hk' : k < m := by omega
        rw [show (2 * certAxis m c + if c (m + 1) then 1 else 0) =
            (if c (m + 1) then 1 else 0) + 2 * certAxis m c by ring,
          Nat.testBit_succ]
        have hdiv : ((if c (m + 1) then 1 else 0) + 2 * certAxis m c) / 2 = certAxis m c := by
          split_ifs <;> omega
        rw [hdiv, ih k hk']
        congr 1
        omega

/-- The MSB-first certificate bits of the certificate axis are `c₁ … c_m`, then `false`. -/
theorem formRCertBit_certAxis (m : ℕ) (c : ℕ → Bool) (j : ℕ) :
    MemoryTable.formRCertBit (certAxis m c) j = (decide (j < m) && c (j + 1)) := by
  unfold MemoryTable.formRCertBit
  rw [formRCertShift_certAxis]
  by_cases hj : j < m
  · rw [if_pos hj, testBit_certAxis m c (m - 1 - j) (by omega)]
    simp only [hj, decide_true, Bool.true_and]
    congr 1
    omega
  · rw [if_neg hj]; simp [hj]

/-! ## §B  The round-0 wrap, env-parametric -/

section Wrap

variable {F K : Type} [Field F] [Field K]

/-- **The recovered axis of exponent `e`** from the round-0 compute envs: the certificate the
exponent locator assigns to `e` (`decodedShift` / `decodedBits`), read as an integer. -/
def certAxisOfEnvs {N : ℕ} (envsC : Fin N → Env K) (e : ℕ) : ℕ :=
  certAxis (decodedShift envsC e) (decodedBits envsC e)

/-- **The record exponent of (1-indexed) memory row `i`**: `natLift reqIdx` (base column `181`),
with `lblM`'s off-range convention (row `1`). -/
def memRowExpOfEnvs {M : ℕ} (envsF : Fin M → Env F) (hM : 0 < M) (i : ℕ) : ℕ :=
  if h : i - 1 < M then RecordCarrier.natLift ((envsF ⟨i - 1, h⟩).trace reqIdxCol)
  else RecordCarrier.natLift ((envsF ⟨0, hM⟩).trace reqIdxCol)

/-- **The round-0 memory wrap** at exponent `e` and recovered axis `a`: the template row stores the
Nock axis `a` (not the decoded `T`) and takes its record exponent from `e` (not from `ts`).
Every other placeholder field is the decoded row's; `specializeA` overwrites the timestamp and
`encodeRow` writes `(T, C', λ)` from `a`. -/
def wrapMemoryLabelR0 (e a : ℕ) (row : MState × DTmem K) : MemoryRowTemplate (K := K) where
  timestamp :=
    { state := row.1
      recordExponent := e }
  placeholder := (row.1, (row.2.1, { row.2.2 with mem := { row.2.2.mem with axis := (a : K) } }))

/-- The wrap at row `i` of a pair of env families: `e := memRowExpOfEnvs`, `a := certAxisOfEnvs e`. -/
def wrapR0OfEnvs {N M : ℕ} (envsC : Fin N → Env K) (envsF : Fin M → Env F) (hM : 0 < M)
    (i : ℕ) (row : MState × DTmem K) : MemoryRowTemplate (K := K) :=
  wrapMemoryLabelR0 (memRowExpOfEnvs envsF hM i)
    (certAxisOfEnvs envsC (memRowExpOfEnvs envsF hM i)) row

theorem wrapMemoryLabelR0_state (e a : ℕ) (row : MState × DTmem K) :
    (wrapMemoryLabelR0 e a row).timestamp.state = row.1 := rfl

theorem wrapMemoryLabelR0_recordExponent (e a : ℕ) (row : MState × DTmem K) :
    (wrapMemoryLabelR0 e a row).timestamp.recordExponent = e := rfl

end Wrap

/-! ## §C  Over `O`: the round-0 template and the built strategy -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

variable (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- The compute envs the wrap reads (round-0 columns only): the family compute source envs. -/
def computeEnvsR0
    (Qc : Fin (CC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    Fin O.family.problem.cfg.compRows → Env K :=
  fun i => (FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) i).toSourceEnv

/-- The memory envs the wrap reads (`reqIdx` only): the family memory base envs. -/
def memoryEnvsR0
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    Fin O.family.problem.cfg.memRows → Env F :=
  FamilyEnvCore.memoryBaseEnvAt O c Qm

/-- The round-0 template row of (1-indexed) memory row `i`: the round-0 wrap of the decoded
label `lblM`. -/
def lblMR0
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ℕ → MemoryRowTemplate (K := K) :=
  fun i => wrapR0OfEnvs (computeEnvsR0 O Qc c) (memoryEnvsR0 O Qm c)
    O.family.problem.cfg.memRows_pos i (lblM O Qm c i)

/-- **The round-0 execution template**: the lifted compute template's tree, restated directly (so the
round-0 strategy does not reach the lifted memory wrap / `memExponent` through a projection); the memory forest
is the inverse BFS of the round-0 template rows (the lifted one is the inverse BFS of `lblM`
mapped through `wrapMemoryLabel α`). -/
def execTemplateOfTracesR0
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) :
    ExactExecutionTemplate (cfgTemplateOfTraces O Qc Qm c z) where
  computeTree :=
    mapNTree StrategyOfTracesLift.wrapComputeLabel (execOfTraces O Qc Qm c h).computeTree
  memoryForest :=
    reconForest O.family.problem.cfg.kMem (foM O Qm c) (lblMR0 O Qc Qm c)
      O.family.problem.cfg.memRows
  memoryForest_nonempty := by
    have hk := family_kMem_pos O
    intro hempty
    have hlen := congrArg List.length hempty
    simp [reconForest, List.length_map, List.length_range'] at hlen
    exact (Nat.ne_of_gt (Nat.succ_le_iff.mp hk) hlen)
  memory_root_count := by
    simp [reconForest, List.length_map, List.length_range', cfgTemplateOfTraces,
      StrategyOfTracesLift.configTemplateOf, cfgOfTraces]
  compute_bfs_length := by
    have hlen := (execOfTraces O Qc Qm c h).compute_bfs_length
    have hmap :
        (bfsForest
          [mapNTree StrategyOfTracesLift.wrapComputeLabel
            (execOfTraces O Qc Qm c h).computeTree]).length =
        (bfsForest [(execOfTraces O Qc Qm c h).computeTree]).length := by
      rw [show [mapNTree StrategyOfTracesLift.wrapComputeLabel
              (execOfTraces O Qc Qm c h).computeTree] =
            [(execOfTraces O Qc Qm c h).computeTree].map
              (mapNTree StrategyOfTracesLift.wrapComputeLabel) from rfl,
        bfsForest_mapNTree, List.length_map]
    simpa [cfgTemplateOfTraces, StrategyOfTracesLift.configTemplateOf, hmap] using hlen
  memory_bfs_length := by
    have hk := family_kMem_pos O
    rw [bfsForest_reconForest O.family.problem.cfg.kMem (foM O Qm c)
      (lblMR0 O Qc Qm c) O.family.problem.cfg.memRows hk h.sfMemory h.validMemory]
    simp only [List.length_map, List.length_range']
    simp only [cfgTemplateOfTraces, StrategyOfTracesLift.configTemplateOf]
    exact (cfgOfTraces_memRows O Qc Qm c).symm

/-- The round-0 timestamp strategy: `timestampOfTraces` with the round-0 execution template. -/
def timestampOfTracesR0
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K) :=
  DataOnlyTemplateFixedStagedTimestampStrategy.ofRawData
    (publicClaimOf O Qc Qm)
    (fun seed => cfgTemplateOfTraces O Qc Qm c seed.1)
    (fun seed => execTemplateOfTracesR0 O Qc Qm c h seed.1)
    (fun _ => rfl)

/-! ### The lifted chain over an arbitrary timestamp strategy (bodies verbatim) -/

/-- `StrategyOfTracesLift.familyDataOfTraces` over the timestamp strategy `Ts`. -/
def familyDataGen
    (Ts : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (tag : NodeEncoding.StateTagChar K)
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    AlphaMFamilyData Ts z hz α lmb where
  compNodeWidth := NodeEncoding.computeNodeWidth
  compNodeEncode := NodeEncoding.computeNodeEncode tag
  memNodeWidth := NodeEncoding.memoryNodeWidth
  memNodeEncode := NodeEncoding.memoryNodeEncode tag
  requests :=
    algebraMap K (IOField K)
      (∑ k : Fin 3,
          O.computePublic (6 + (k : ℕ)) • O.basis k)
  responses :=
    algebraMap K (IOField K)
      ((FamilyEnvCore.memorySourceEnvAt O c Qm
        ⟨O.family.problem.cfg.memRows - 1,
          Nat.pred_lt (Nat.pos_iff_ne_zero.mp
            O.family.problem.cfg.memRows_pos)⟩).trace 44)
  outMem :=
    algebraMap K (IOField K)
      ((FamilyEnvCore.memorySourceEnvAt O c Qm
        ⟨0, O.family.problem.cfg.memRows_pos⟩).trace 28)

/-- `StrategyOfTracesLift.tablesOfTraces` over `Ts`. -/
def tablesGen
    (Ts : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    RawTableArrays (familyDataGen O Ts tag Qm c z hz α lmb).base where
  compute := fun i =>
    if hj : i.val < O.family.problem.cfg.compRows then
      StrategyOfTracesLift.decodeEx
        (FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) ⟨i.val, hj⟩)
    else
      StrategyOfTracesLift.decodeEx (FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc)
        ⟨0, O.family.problem.cfg.compRows_pos⟩)
  memory := fun _ => 0

/-- `StrategyOfTracesLift.ioOfTraces` over `Ts`. -/
def ioGen
    (Ts : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    RawIOArrays (familyDataGen O Ts tag Qm c z hz α lmb).base (ringChar K) where
  multiplicity := fun j =>
    let i := j.val % O.family.problem.cfg.memRows
    if hlt : i < O.family.problem.cfg.memRows then
      if (FamilyEnvCore.memoryBaseEnvAt O c Qm ⟨i, hlt⟩).trace 2 = 1 then 1 else 0
    else
      0
  progAcc := fun i =>
    if hlt : i < O.family.problem.cfg.compRows then
      algebraMap K (IOField K)
        ((FamilyEnvCore.rowEnvAt O c (FamilyEnvCore.familyQc O c Qc) ⟨i, hlt⟩).toSourceEnv.trace
          accAfterIndex)
    else
      0
  memAcc := fun i =>
    if hlt : i < O.family.problem.cfg.memRows then
      algebraMap K (IOField K)
        ((FamilyEnvCore.memorySourceEnvAt O c Qm ⟨i, hlt⟩).trace 44)
    else
      0

/-- `StrategyOfTracesLift.afterAlphaMOfTraces` over `Ts`. -/
def afterAlphaMGen
    (Ts : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    AlphaMCommitment (p := ringChar K) Ts z hz α lmb where
  familyData := familyDataGen O Ts tag Qm c z hz α lmb
  tables := tablesGen O Ts tag Qc Qm c z hz α lmb
  io := ioGen O Ts tag Qc Qm c z hz α lmb

/-- `StrategyOfTracesLift.topologyOfTraces` over `Ts`. -/
def topologyGen
    (Ts : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    RawTopologyArrays (afterAlphaMGen O Ts tag Qc Qm c z hz α lmb).familyData.base where
  compute :=
    { childPayload := fun i slot =>
        match clabC O Qc c (i.val + 1) slot.val with
        | some child => ⟨child.2.2.1.s, child.2.2.1.f, child.2.2.1.e⟩
        | none => ComputeLinkPayload.zero }
  memory :=
    { childPayload := fun i slot =>
        match clabM O Qm c (i.val + 1) slot.val with
        | some child => child.2.2.pt
        | none => Cell.zero }

/-- `StrategyOfTracesLift.rawVerifierOfTraces` over `Ts`. -/
def rawVerifierGen
    (Ts : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    TemplateRawJointSoundness.Strategy F K (ringChar K) where
  timestamp := Ts
  afterAlphaM := afterAlphaMGen O Ts tag Qc Qm c
  afterCoins := fun _ _ _ => walksOfTraces O Qc Qm c

/-- `StrategyOfTracesLift.verifierOfTraces` over `Ts`. -/
def verifierGen
    (Ts : DataOnlyTemplateFixedStagedTimestampStrategy (F := F) (K := K))
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F) :
    ProductionRawVerifier.TemplateAdapter.Strategy F K (ringChar K) where
  raw := rawVerifierGen O Ts tag Qc Qm c
  topologyAfterAlphaM := topologyGen O Ts tag Qc Qm c

/-- Skeleton
and public claim are the lifted ones. -/
def strategyOfTracesR0
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    ProductionStrategy F K where
  verifier := verifierGen O (timestampOfTracesR0 O Qc Qm c h) tag Qc Qm c
  skeleton := decodedSkeletonOf O Qc Qm
  publicClaim_eq := rfl

/-- **Where the round-0 wrap and the lifted wrap differ, exactly**: the record exponent (`e` vs
`memExponent α ts`) and the stored axis (`a` vs the decoded slot); state and inputs agree. -/
theorem wrapMemoryLabelR0_eq_lifted (α : K) (e a : ℕ) (row : MState × DTmem K) :
    wrapMemoryLabelR0 e a row =
      { timestamp := { (StrategyOfTracesLift.wrapMemoryLabel α row).timestamp with
          recordExponent := e }
        placeholder := ((StrategyOfTracesLift.wrapMemoryLabel α row).placeholder.1,
          ((StrategyOfTracesLift.wrapMemoryLabel α row).placeholder.2.1,
          { (StrategyOfTracesLift.wrapMemoryLabel α row).placeholder.2.2 with
            mem := { (StrategyOfTracesLift.wrapMemoryLabel α row).placeholder.2.2.mem with
              axis := (a : K) } })) } := rfl

/-! ### Definitional facts -/

/-- The lifted strategy is the generic chain at the lifted timestamp strategy. -/
theorem strategyOfTraces_eq_gen
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    StrategyOfTracesLift.strategyOfTraces O tag Qc Qm c h =
      { verifier := verifierGen O (timestampOfTraces O Qc Qm c h) tag Qc Qm c
        skeleton := decodedSkeletonOf O Qc Qm
        publicClaim_eq := rfl } := rfl

/-- The specialized execution of the round-0 strategy is the round-0 template, specialized. -/
theorem specializedExec_R0_eq
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    (strategyOfTracesR0 O tag Qc Qm c h).specializedExec z hz α lmb =
      (execTemplateOfTracesR0 O Qc Qm c h z).specialize α lmb := rfl

/-- The round-0 and lifted strategies have the same skeleton. -/
theorem skeleton_R0_eq
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (strategyOfTracesR0 O tag Qc Qm c h).skeleton =
      (StrategyOfTracesLift.strategyOfTraces O tag Qc Qm c h).skeleton := rfl

/-- The round-0 and lifted strategies have the same specialized configuration. -/
theorem specializedCfg_R0_eq
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    (strategyOfTracesR0 O tag Qc Qm c h).specializedCfg z hz α lmb =
      (StrategyOfTracesLift.strategyOfTraces O tag Qc Qm c h).specializedCfg z hz α lmb := rfl

/-- The round-0 and lifted execution templates have the same compute tree. -/
theorem computeTree_R0_eq
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) (z : K) :
    (execTemplateOfTracesR0 O Qc Qm c h z).computeTree =
      (execTemplateOfTraces O Qc Qm c h z).computeTree := rfl

end

end Nock.NockVMROM.Thm54.StrategyOfTracesR0
