/-
  Nock/RedTeam/Batch441Thm54MemoryEncoder.lean

  **Encoder `33 → 6`, label determination, roots through LIO.**

  * `NodeEncoding.memoryNodeEncode` is the `x^mem` projection, width `6`;
    the retired full-row encoder is `memoryFullRowEncode` (`33`, injective, unread).
  * Label determination (`memoryNodeEncode_labelOf_eq`) replaces injectivity; the memory
    consumers run through the `_of_label` variants (`Walk.lean`, `NockVM.lean`,
    `SeedFibers.lean`, `SharedTableWalkRow.lean`); `MemoryTable.Fmem_respects_labelOf`.
  * `ε_RLC`'s `node_size − 1` goes `32 → 5`; `Batch345`'s memory twin flipped
    (`memoryWalkBound_le_topologyMemory : 6M ≤ 8M`).
  * `memory_roots_bound_by_LIO` (`MemoryWalkRoots`): the seed stays prover-committed; every
    `ver`-selected `read_root` row's `x^mem` noun is a compute request record's root.  The
    compute-side decode bridge is disclosed (`COMPUTE_ROOT_PIN_REMAINING`).
  * The K side keeps the memory topology RAP (consumers listed) — as compute did at `Batch455`.
-/
import Nock.NockVMROM.Thm54.NodeEncoding
import Nock.NockVMROM.Thm54.MemoryWalkRoots
import Nock.NockVMROM.Thm54.Walk37.OptimizedStrictFullPackage
import Nock.RedTeam.Batch345Thm54WalkBound
open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

set_option autoImplicit false

namespace Nock.RedTeam.Batch441

open Nock
open Nock.MemoryTable
open Nock.NockVMROM.Thm54

section Encoder

variable {K : Type} [Field K]

theorem width_six : NodeEncoding.memoryNodeWidth = 6 := rfl

theorem encoder_is_label_vec (hchar : NodeEncoding.StateTagChar K) :
    NodeEncoding.memoryNodeEncode hchar = NodeEncoding.memoryLabelVec :=
  NodeEncoding.memoryNodeEncode_eq_labelVec hchar

/-- Label determination: equal encodings, equal `x^mem` projections. -/
theorem label_determination (hchar : NodeEncoding.StateTagChar K)
    {a b : MState × DTmem K}
    (h : NodeEncoding.memoryNodeEncode hchar a = NodeEncoding.memoryNodeEncode hchar b) :
    memoryLabelOf a = memoryLabelOf b :=
  NodeEncoding.memoryNodeEncode_labelOf_eq hchar h

/-- The encoder reads none of the record, `intermediate`, child cells or child states. -/
theorem encoder_ignores_record (hchar : NodeEncoding.StateTagChar K)
    (st : MState) (inp : Inputs K) (pub : Pub K) (mem' : ComputeTable.MemRec K) :
    NodeEncoding.memoryNodeEncode hchar (st, (inp, pub)) =
      NodeEncoding.memoryNodeEncode hchar (st, (inp, { pub with mem := mem' })) :=
  NodeEncoding.memoryNodeEncode_ignores_mem hchar st inp pub mem'

/-- `Fmem` reads children through the projection only (the `_of_label` premise). -/
theorem fmem_respects (lbl : MState × DTmem K)
    {xout xout' : Fin 2 → Option (MState × DTmem K)}
    (h : ∀ j, (xout j).map memoryLabelOf = (xout' j).map memoryLabelOf)
    (hF : Fmem lbl xout) : Fmem lbl xout' :=
  Fmem_respects_labelOf lbl h hF

/-- `RespectsChildLabels`, as the walk theorems take it. -/
theorem respects_child_labels :
    Walk.RespectsChildLabels (Fmem (K := K)) memoryLabelOf :=
  fun lbl _ _ h hF => Fmem_respects_labelOf lbl h hF

/-- The retired encoder is kept, injective, under its own name. -/
theorem full_row_encoder_kept (hchar : NodeEncoding.StateTagChar K) :
    Function.Injective (NodeEncoding.memoryFullRowEncode hchar) :=
  NodeEncoding.memoryFullRowEncode_injective hchar

end Encoder

/-! ## The bound function moved at the memory walk summand -/

theorem memory_walk_numerator (M : ℕ) :
    M + M * (NodeEncoding.memoryNodeWidth - 1) = M * 6 :=
  Batch345.production_memoryWalk_numerator M

/-- `Batch345`'s memory twin FLIPPED: `6M ≤ 8M` (was `¬ 33M ≤ 8M`). -/
theorem memory_walk_le_topology (M : ℕ) :
    M + M * (NodeEncoding.memoryNodeWidth - 1) ≤ M * 2 * 4 :=
  Batch345.memoryWalkBound_le_topologyMemory M

/-! ## Roots through LIO -/

section Roots

variable {F K : Type} [Field F] [Field K] [Algebra F K]
  [Fintype F] [DecidableEq F] [Fintype K] [DecidableEq K]
  [CharP K (ringChar K)] [FiniteDimensional F K]
  {hOrb : ℕ} (P : OptimizedStrictFullPackage.OptimizedFullStrictNockVMROMPackage F K hOrb)

/-- `:2067` at the deployed chip (re-export). -/
theorem read_root_noun_is_record_root
    (c : OptimizedStrictPackage.OptimizedProductionChallengeTuple K F)
    (Qm : Fin (P.memoryChipAt c).rap.w → Polynomial F)
    (hsat : Nock.Framework.RAP.SatisfiesWithPreprocessing (P.memoryChipAt c) Qm)
    (hchar : FamilyMemoryRows.MemStateTagChar F)
    (i : Fin P.optimized.family.problem.cfg.memRows)
    (hst : StrategyOfTraces.memoryStateOf
      (FamilyComputeRows.memoryBaseEnvAt P c (FamilyMemoryRows.honestQm P c Qm) i) = .read_root) :
    MemoryWalkRoots.rowLabelNoun P (FamilyMemoryRows.honestQm P c Qm) i =
      MemoryWalkRoots.rowRecordRoot P (FamilyMemoryRows.honestQm P c Qm) i :=
  MemoryWalkRoots.read_root_noun_eq_record_root P c Qm hsat hchar i hst

theorem compute_root_pin_remaining :
    MemoryWalkRoots.COMPUTE_ROOT_PIN_REMAINING.length = 2 :=
  MemoryWalkRoots.compute_root_pin_remaining_length

end Roots

/-! ## The K side keeps the memory topology RAP (as `Batch455` kept compute's) -/

def ksideMemoryTopologyConsumers : List String :=
  ["SharedTableWalkRow.hfo_memory / harity_memory / hFcommit_memory (hbind.2)",
   "OptimizedStrictFullPackage.memoryWalk_bound (P.topologyBinding)",
   "RawTopologySoundness.memoryBinding_of_exactTopology (honest side)",
   "ProductionRawVerifier.VerifierGeneratedSegmentedTopologyChecks (memory arrays)"]

theorem kside_memory_consumers_length : ksideMemoryTopologyConsumers.length = 4 := by decide

def MEMORY_TOPOLOGY_RAP_STATUS : String :=
  "kept on the K side; the deployed chip binds topology through the in-gate walk (Batch443)"

end Nock.RedTeam.Batch441

#print axioms Nock.RedTeam.Batch441.label_determination
#print axioms Nock.RedTeam.Batch441.read_root_noun_is_record_root
#print axioms Nock.NockVMROM.Thm54.MemoryWalkRoots.memory_roots_bound_by_LIO
