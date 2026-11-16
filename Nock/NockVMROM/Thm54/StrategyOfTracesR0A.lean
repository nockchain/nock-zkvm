/-
  Nock/NockVMROM/Thm54/StrategyOfTracesR0A.lean

  Additive: `strategyOfTracesR0`,
  `decodedSkeletonOf`, `decodeMemoryRowIn` and the lifted strategy stay; nothing is re-pointed.

  **Why.**  So the executed row correctly holds the Form R `T`, and it is the skeleton that must hold the Nock axis `a`.  Here the record axis
  is SUPPLIED: `decodeMemoryRowAx q forest ax` is `decodeMemoryRowIn q forest` with `axis := ax label`
  on the two active states, every other field verbatim; on the round-0 forest `ax` is the wrap's own
  recovered axis `certAxisOfEnvs (memRowExpOfEnvs …)` of the row (`axOfRowsR0`), read through the
  row's position in `lblMAt`.  `strategyOfTracesR0A` is `strategyOfTracesR0` with that skeleton: its
  verifier, compute skeleton tree, public claim and specialized execution are the round-0 strategy's
  (`rfl`).

  Paper: the paper (axis doubling), `:2117` (`mem_record` holds the address),
  `:2164-2166` (the paper-`⊥` record halves).
-/
import Nock.NockVMROM.Thm54.StrategyOfTracesR0

namespace Nock.NockVMROM.Thm54.StrategyOfTracesR0A

open scoped Polynomial
open Polynomial
open Nock
open Nock.Walk
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
open Nock.NockVMROM.Thm54.HostileSkeletonDecoding
open Nock.NockVMROM.Thm54.StrategyOfTracesLift
open Nock.NockVMROM.Thm54.StrategyOfTracesR0

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option quotPrecheck false

noncomputable section

/-! ## §A  The decoder with a supplied record axis -/

section Decoder

variable {K : Type} [Field K]

/-- `HostileSkeletonDecoding.decodeMemoryRowIn q forest` with the active record's `axis` supplied by
`ax` at the node's label (the a-bearing axis), every other field verbatim: the paper-`⊥` halves by `nounByFP`, the parent
and children by `decodeNoun`. -/
def decodeMemoryRowAx (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ) :
    NTree (MState × DTmem K) → MemoryRowSkeleton
  | .node (.halt, data) _ =>
      { state := .halt
        parent := Noun.atom (leafAtomOf q data.2.pt.noun.leaf)
        haltAtom := fun _ => leafAtomOf q data.2.pt.noun.leaf
        haltParent := fun _ => rfl
        child := fun i hi => False.elim (by
          simp [MemoryTable.fanoutMem] at hi)
        memoryRecord := fun h => False.elim (by
          simp [memoryMemRecKind] at h) }
  | .node (.decompose, _) [left, right] =>
      { state := .decompose
        parent := Noun.cell (decodeNoun q left) (decodeNoun q right)
        haltAtom := fun h => nomatch h
        haltParent := fun h => nomatch h
        child := fun i _hi =>
          if i.val = 0 then decodeNoun q left else decodeNoun q right
        memoryRecord := fun h => False.elim (by
          simp [memoryMemRecKind] at h) }
  | .node (.read_root, data) [child] =>
      { state := .read_root
        parent := decodeNoun q child
        haltAtom := fun h => nomatch h
        haltParent := fun h => nomatch h
        child := fun _ _ => decodeNoun q child
        memoryRecord := fun _ =>
          { root := decodeNoun q child
            child := HostileSkeletonDecoding.nounByFP q forest data.2.mem.child
            axis := ax (.read_root, data) } }
  | .node (.verify_child, data) [child] =>
      { state := .verify_child
        parent := decodeNoun q child
        haltAtom := fun h => nomatch h
        haltParent := fun h => nomatch h
        child := fun _ _ => decodeNoun q child
        memoryRecord := fun _ =>
          { root := HostileSkeletonDecoding.nounByFP q forest data.2.mem.root
            child := decodeNoun q child
            axis := ax (.verify_child, data) } }
  | _ =>
      { state := .halt
        parent := Noun.atom 0
        haltAtom := fun _ => 0
        haltParent := fun _ => rfl
        child := fun i hi => False.elim (by
          simp [MemoryTable.fanoutMem] at hi)
        memoryRecord := fun h => False.elim (by
          simp [memoryMemRecKind] at h) }

@[simp] theorem decodeMemoryRowAx_readRoot_state (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K) (child : NTree (MState × DTmem K)) :
    (decodeMemoryRowAx q forest ax (.node (.read_root, data) [child])).state = .read_root :=
  rfl

@[simp] theorem decodeMemoryRowAx_verifyChild_state (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K) (child : NTree (MState × DTmem K)) :
    (decodeMemoryRowAx q forest ax (.node (.verify_child, data) [child])).state = .verify_child :=
  rfl

/-- The supplied axis is what the active record carries. -/
theorem decodeMemoryRowAx_readRoot_axis (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K) (child : NTree (MState × DTmem K)) :
    ((decodeMemoryRowAx q forest ax (.node (.read_root, data) [child])).memoryRecord
      (by simp [memoryMemRecKind])).axis = ax (.read_root, data) :=
  rfl

theorem decodeMemoryRowAx_verifyChild_axis (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ)
    (data : DTmem K) (child : NTree (MState × DTmem K)) :
    ((decodeMemoryRowAx q forest ax (.node (.verify_child, data) [child])).memoryRecord
      (by simp [memoryMemRecKind])).axis = ax (.verify_child, data) :=
  rfl

/-- Tree form (`decodeMemoryTree` with the supplied axis). -/
def decodeMemoryTreeAx (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ) :
    NTree (MState × DTmem K) → NTree MemoryRowSkeleton
  | .node lbl ch =>
      .node (decodeMemoryRowAx q forest ax (.node lbl ch))
        (ch.map (decodeMemoryTreeAx q forest ax))

/-- Forest form (`decodedMemoryForest` with the supplied axis). -/
def decodedMemoryForestAx (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ) :
    List (NTree MemoryRowSkeleton) :=
  forest.map (decodeMemoryTreeAx q forest ax)

theorem decodedMemoryForestAx_length (q : ℕ)
    (forest : List (NTree (MState × DTmem K))) (ax : MState × DTmem K → ℕ) :
    (decodedMemoryForestAx q forest ax).length = forest.length := by
  simp [decodedMemoryForestAx]

end Decoder

/-! ## §B  Over `O`: the round-0 recovered axis of a decoded row, the a-bearing skeleton, the strategy -/

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F]
  [Fintype K] [DecidableEq K] [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ}

variable (O : OptimizedStrictNockVMROMPackage F K hOrb)

/-- `P.computeChip` at `O := P.optimized` (as in `StrategyOfTracesR0`). -/
local notation "CC[" O "]" =>
  ProductionNamedComputeRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.compRows_pos
    (OptimizedStrictNockVMROMPackage.computeNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.computeChallenge O)
    (OptimizedStrictNockVMROMPackage.computePublic O) (OptimizedStrictNockVMROMPackage.orbit O)

/-- `P.memoryChip` at `O := P.optimized` (as in `StrategyOfTracesR0`). -/
local notation "MC[" O "]" =>
  namedFinalMemoryRAP (OptimizedStrictNockVMROMPackage.family O).problem.cfg.memRows_pos
    (OptimizedStrictNockVMROMPackage.memoryNodes O) (OptimizedStrictNockVMROMPackage.basis O)
    (OptimizedStrictNockVMROMPackage.memoryChallenge O)
    (OptimizedStrictNockVMROMPackage.memoryPublic O) (OptimizedStrictNockVMROMPackage.orbit O)
    (OptimizedStrictNockVMROMPackage.family O).problem.cfg.kMem

open scoped Classical in
/-- **The round-0 recovered axis of a decoded memory row**: the axis the round-0 wrap stores at the
row's position — `certAxisOfEnvs (computeEnvsR0 …) (memRowExpOfEnvs (memoryEnvsR0 …) (k + 1))` for
a `k` with `lblMAt O Qm c k = row` (`Classical.choose`; `0` off the row list).  It reads round-0
columns only, through `wrapR0OfEnvs`'s metadata.  On accepted traces every `k` with
that label gives the same value (`Batch973.read_row_facts` / `verify_row_facts`). -/
def axOfRowsR0
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (row : MState × DTmem K) : ℕ :=
  if h : ∃ k : Fin O.family.problem.cfg.memRows, lblMAt O Qm c k = row then
    certAxisOfEnvs (computeEnvsR0 O Qc c)
      (memRowExpOfEnvs (memoryEnvsR0 O Qm c) O.family.problem.cfg.memRows_pos (h.choose.val + 1))
  else 0

/-- **Specification of `axOfRowsR0`** on a row of the list: it is the round-0 recovered axis at SOME
position `k` carrying that row. -/
theorem axOfRowsR0_spec
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (row : MState × DTmem K)
    (h : ∃ k : Fin O.family.problem.cfg.memRows, lblMAt O Qm c k = row) :
    ∃ k : Fin O.family.problem.cfg.memRows, lblMAt O Qm c k = row ∧
      axOfRowsR0 O Qc Qm c row =
        certAxisOfEnvs (computeEnvsR0 O Qc c)
          (memRowExpOfEnvs (memoryEnvsR0 O Qm c) O.family.problem.cfg.memRows_pos (k.val + 1)) :=
  ⟨h.choose, h.choose_spec, by unfold axOfRowsR0; rw [dif_pos h]⟩

/-- The recovered axis is the round-0 template row's stored axis, read back as a natural. -/
theorem axOfRowsR0_eq_lblMR0_axis
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (row : MState × DTmem K)
    (h : ∃ k : Fin O.family.problem.cfg.memRows, lblMAt O Qm c k = row) :
    ((axOfRowsR0 O Qc Qm c row : ℕ) : K) =
      (lblMR0 O Qc Qm c (h.choose.val + 1)).placeholder.2.2.mem.axis := by
  unfold axOfRowsR0
  rw [dif_pos h]
  rfl

/-- **The a-bearing skeleton of the round-0 strategy**: the lifted compute skeleton tree verbatim
(`decodedSkeletonOf`), and the memory forest decoded from the round-0 strategy's own specialized
forest — which IS the decoded forest of `execOfTraces` on accepted traces outside the event
(`Batch974.specialized_memoryForest_R0_eq`) — with the record axis `axOfRowsR0`. -/
def decodedSkeletonR0A
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) : SemanticSkeleton where
  computeTree := (decodedSkeletonOf O Qc Qm).computeTree
  memoryForest :=
    decodedMemoryForestAx (ringChar K) (execOfTraces O Qc Qm c h).memoryForest
      (axOfRowsR0 O Qc Qm c)

theorem decodedSkeletonR0A_computeTree
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (decodedSkeletonR0A O Qc Qm c h).computeTree = (decodedSkeletonOf O Qc Qm).computeTree := rfl

theorem decodedSkeletonR0A_publicClaim
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (decodedSkeletonR0A O Qc Qm c h).publicClaim = publicClaimOf O Qc Qm := rfl

/-- **The round-0 built strategy with the a-bearing skeleton**: `strategyOfTracesR0`'s verifier, the
skeleton `decodedSkeletonR0A`.  The one strategy of the traces on which `BindsAtCoin`'s memory
conjunct can hold. -/
def strategyOfTracesR0A
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    ProductionStrategy F K where
  verifier := (strategyOfTracesR0 O tag Qc Qm c h).verifier
  skeleton := decodedSkeletonR0A O Qc Qm c h
  publicClaim_eq := rfl

/-! ### Definitional facts -/

theorem strategyOfTracesR0A_verifier
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (strategyOfTracesR0A O tag Qc Qm c h).verifier = (strategyOfTracesR0 O tag Qc Qm c h).verifier :=
  rfl

theorem strategyOfTracesR0A_skeleton
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c) :
    (strategyOfTracesR0A O tag Qc Qm c h).skeleton = decodedSkeletonR0A O Qc Qm c h :=
  rfl

/-- The specialized execution is the round-0 strategy's (same verifier). -/
theorem specializedExec_R0A_eq
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    (strategyOfTracesR0A O tag Qc Qm c h).specializedExec z hz α lmb =
      (strategyOfTracesR0 O tag Qc Qm c h).specializedExec z hz α lmb := rfl

/-- The specialized configuration is the round-0 strategy's. -/
theorem specializedCfg_R0A_eq
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    (strategyOfTracesR0A O tag Qc Qm c h).specializedCfg z hz α lmb =
      (strategyOfTracesR0 O tag Qc Qm c h).specializedCfg z hz α lmb := rfl

/-- The specialized configuration's seed is the specialization's `z` (what `BindsAt.sampledSeed`
reads). -/
theorem specializedCfg_R0A_z
    (tag : NodeEncoding.StateTagChar K)
    (Qc : Fin (CC[O]).rap.w → F[X])
    (Qm : Fin (MC[O]).rap.w → F[X])
    (c : OptimizedProductionChallengeTuple K F)
    (h : TracesWalkHyps O Qc Qm c)
    (z : K) (hz : z ≠ 0) (α lmb : K) :
    ((strategyOfTracesR0A O tag Qc Qm c h).specializedCfg z hz α lmb).challenges.z = z := rfl

end

end Nock.NockVMROM.Thm54.StrategyOfTracesR0A
