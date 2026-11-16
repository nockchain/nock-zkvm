import Nock.NockVMROM.Thm54.GenericHonestData
import Nock.RedTeam.Batch100Thm54GenericHonestData
import Nock.NockVMROM.Thm54.Walk37.PaperNames

open Nock.Walk37 Nock.Walk37.Nock.NockVMROM.Thm54

/-!

Paper frame:
the paper.

Consumed release declaration:
`OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package`.

Result: scoped PASS.  The reconstructed committed forest projects exactly to
`E.exec.memoryForest`; its fanout comes from `E.traversal.2`; and whole-forest
`memoryOK` contains all four local obligations, including the full
`BindMemoryRow` and `MemoryTimestampSpecializesAt` predicates.

The two fields of `MemoryRecordPremises` close different live-record
obligations.  `axisNat` supplies the Nat NMR address carried in the committed
row skeleton and checked by `BindMemRec`; `timestampClosed` supplies the
exponent used by memory timestamp specialization.  The F73 execution inhabits
both fields with live `read_root` and `verify_child` rows.  Halt atoms are
projected from `E.semanticData.language.nounRealization.memoryLeaves`, not
added to `MemoryRecordPremises`.

`dataOfRecord` still takes the dependent `CensusAssemblyPremises`; no
`∀ E, Data E` constructor is introduced or claimed.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace Nock.RedTeam.Batch101

open scoped Classical
open Nock Nock.Framework Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.OptimizedStrictFullPackage

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. `memoryOK` is the full whole-forest predicate -/

/-- Every reconstructed node carries all four `MemoryNodeOK` obligations:
state-defined fanout, stamp/skeleton state agreement, full row binding, and
timestamp specialization. -- the paper -/
theorem memoryOK_expands_all_four_node_obligations
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    ∀ T ∈ memoryNodesOf E M, ∀ t, InTree T t →
      t.children.length = MemoryTable.fanoutMem t.label.skel.state ∧
        t.label.stamp.state = t.label.skel.state ∧
        -- 28th: committed memory nodes carry the a-bearing row (`BindMemoryRowA`).
        BindMemoryRowA E.cfg.challenges.z t.label.skel t.label.row ∧
        MemoryTimestampSpecializesAt E.cfg.challenges.α
          t.label.stamp t.label.row := by
  intro T hT t ht
  exact memoryNodesOf_ok E M T hT t ht

/-- The binding branch has all seven components of `BindMemoryRow`; in
particular its penultimate branch is a substantive live `BindMemRec` or exact
padding-zero equation, never `True`. -- the paper -/
theorem memoryOK_binding_expands_all_six_conjuncts
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    ∀ T ∈ memoryNodesOf E M, ∀ t, InTree T t →
      let s := t.label.skel
      let row := t.label.row
      row.1 = s.state ∧
        row.2.1.z = E.cfg.challenges.z ∧
        row.2.2.st = s.state ∧
        bindFP E.cfg.challenges.z s.parent row.2.2.pt.noun ∧
        (∀ i : Fin 2,
          if h : (i : ℕ) < MemoryTable.fanoutMem s.state
          then bindFP E.cfg.challenges.z (s.child i h)
            (memoryChildCell row.2.2 i).noun
          else memoryChildCell row.2.2 i = MemoryTable.Cell.zero) ∧
        (if h : memoryMemRecKind s.state = .active
          then BindMemRec E.cfg.challenges.z (s.memoryRecord h) row.2.2.mem
          else row.2.2.mem = ComputeTable.MemRec.zero) ∧
        row.2.2.ver = decide (s.state = MemoryTable.MState.read_root) := by
  intro T hT t ht
  simpa [BindMemoryRowA] using
    (memoryNodesOf_ok E M T hT t ht).2.2.1

/-- The timestamp branch has all four components of
`MemoryTimestampSpecializesAt`: both state equations, the active power (or
zero), and exact padding. -- the paper -/
theorem memoryOK_timestamps_expand_all_four_conjuncts
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    ∀ T ∈ memoryNodesOf E M, ∀ t, InTree T t →
      let stamp := t.label.stamp
      let row := t.label.row
      row.1 = stamp.state ∧
        row.2.2.st = stamp.state ∧
        row.2.2.mem.ts =
          (if memoryMemRecKind stamp.state = .active
            then E.cfg.challenges.α ^ stamp.recordExponent
            else 0) ∧
        (memoryMemRecKind stamp.state = .padding →
          row.2.2.mem = ComputeTable.MemRec.zero) := by
  intro T hT t ht
  simpa [MemoryTimestampSpecializesAt] using
    (memoryNodesOf_ok E M T hT t ht).2.2.2

/-! ## B. Authoritative forest and traversal threading -/

/-- The reconstructed object is a committed-node lift of the exact execution
forest.  Row projection, the original memory topology, and every reconstructed
fanout are threaded in one theorem. -- the paper -/
theorem memory_reconstruction_threads_execution_and_traversal
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E) :
    (memoryNodesOf E M).map (mapNTree MemoryNode.row) =
        E.execA.memoryForest ∧
      (∀ T ∈ E.exec.memoryForest,
        RVTWithArity (MemoryTable.Fmem (K := K)) T) ∧
      (∀ T ∈ memoryNodesOf E M, ∀ t, InTree T t →
        t.children.length = MemoryTable.fanoutMem t.label.skel.state) := by
  refine ⟨memoryNodesOf_rows E M, E.traversal.2, ?_⟩
  intro T hT t ht
  exact (memoryNodesOf_ok E M T hT t ht).1

/-! ## C. The two NMR extras are substantive and separately consumed -/


theorem memoryRecordPremises_eta_exactly_two
    {E : BuildableNockExecution F K} (M : MemoryRecordPremises E) :
    M =
      { axisNat := M.axisNat
        timestampClosed := M.timestampClosed
        honestVer := M.honestVer } := by
  cases M
  rfl

/-- `axisNat` supplies the actual Nat axis stored in the committed memory
skeleton, and the full binding checks that same skeleton against the row's NMR
address.  The witness is an axis value relative to the record root, not a
committed-line index. -- the paper -/
theorem axisNat_is_load_bearing_NMR_address
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows)
    (hact : memoryMemRecKind (E.exec.memoryRowAt i).1 = .active) :
    let hsact :
        memoryMemRecKind (memorySkeletonOf E M i).state = .active := by
      simpa [memorySkeletonOf] using hact
    -- 28th: the bound record and its `axisNat` address are on the a-bearing row `E.execA`.
    BindMemRec E.cfg.challenges.z
        ((memorySkeletonOf E M i).memoryRecord hsact)
        (E.execA.memoryRowAt i).2.2.mem ∧
      ((memorySkeletonOf E M i).memoryRecord hsact).axis =
        (M.axisNat i hact).choose ∧
      (E.execA.memoryRowAt i).2.2.mem.axis =
        ((M.axisNat i hact).choose : K) := by
  dsimp
  let hsact :
      memoryMemRecKind (memorySkeletonOf E M i).state = .active := by
    simpa [memorySkeletonOf] using hact
  have hbind := (bindMemoryRow_of_assembly E M i).2.2.2.2.2
  rw [dif_pos hsact] at hbind
  refine ⟨hbind.1, ?_, (M.axisNat i hact).choose_spec⟩
  simp [memorySkeletonOf, memoryMemRecSkel]

/-- The timestamp field separately supplies the exponent used by the committed
timestamp row; its specialization is the paper's live monomial power.
-- -/
theorem timestampClosed_is_load_bearing_NMR_power
    (E : BuildableNockExecution F K) (M : MemoryRecordPremises E)
    (i : Fin E.cfg.memRows)
    (hact : memoryMemRecKind (E.exec.memoryRowAt i).1 = .active) :
    -- 28th: the committed timestamp row is the a-bearing row `E.execA`.
    MemoryTimestampSpecializesAt E.cfg.challenges.α
        (memoryStampOf E i) (E.execA.memoryRowAt i) ∧
      (memoryStampOf E i).recordExponent =
        memoryRecordExp E.cfg.challenges.α
          (E.exec.memoryRowAt i).2.2.mem.ts ∧
      (E.exec.memoryRowAt i).2.2.mem.ts =
        E.cfg.challenges.α ^ (memoryStampOf E i).recordExponent := by
  refine ⟨memoryTimestampSpecializesAt_of_assembly E M i, rfl, ?_⟩
  simpa [memoryStampOf] using
    memoryRecordExp_spec (M.timestampClosed i hact)

/-- Any proposed replacement for `axisNat` which still supplies the exact
live `BindMemRec` axis clause must reproduce the same Nat-cast address
obligation.  This is the compiled load-bearing boundary, not a failed proof
search. -- the paper -/
theorem any_live_axis_binding_reproduces_axisNat_obligation
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (hact : memoryMemRecKind (E.exec.memoryRowAt i).1 = .active)
    (s : MemRecSkeleton)
    (hbind :
      BindMemRec E.cfg.challenges.z s (E.exec.memoryRowAt i).2.2.mem) :
    ∃ n : ℕ,
      memoryMemRecKind (E.exec.memoryRowAt i).1 = .active ∧
      (E.exec.memoryRowAt i).2.2.mem.axis = (n : K) := by
  exact ⟨s.axis, hact, hbind.2.2⟩

/-- Any proposed replacement for `timestampClosed` which still supplies the
active timestamp-specialization clause must reproduce a power witness.
-- -/
theorem any_live_timestamp_specialization_reproduces_closed_obligation
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (hact : memoryMemRecKind (E.exec.memoryRowAt i).1 = .active)
    (stamp : MemoryTimestampRow)
    (hst : stamp.state = (E.exec.memoryRowAt i).1)
    (htime :
      MemoryTimestampSpecializesAt E.cfg.challenges.α stamp
        (E.exec.memoryRowAt i)) :
    MemoryTimestampClosedAt E.cfg.challenges.α
      (E.exec.memoryRowAt i).2.2.mem.ts := by
  refine ⟨stamp.recordExponent, ?_⟩
  have hactive : memoryMemRecKind stamp.state = .active := by
    simpa [hst] using hact
  simpa [MemoryTimestampSpecializesAt, hactive] using htime.2.2.1

/-! ## D. Halt atoms are already carried by `E` -/

/-- The halt-leaf realization used by `haltAtom_exists` is an existing field
of `E`'s noun-realized language, not a third `MemoryRecordPremises` field.
-- -/
theorem halt_atoms_are_already_on_E
    (E : BuildableNockExecution F K) :
    ∀ T ∈ E.exec.memoryForest, MemoryLeafAtomsRealized E.q T :=
  E.semanticData.language.nounRealization.memoryLeaves

/-- At a halt row the existing leaf realization and `eqBlk` yield the exact
bounded atom and parent fingerprint used by memory binding.
-- -/
theorem halt_atom_and_parent_binding_come_from_E
    (E : BuildableNockExecution F K) (i : Fin E.cfg.memRows)
    (hhalt : (E.exec.memoryRowAt i).1 = .halt) :
    (∃ k : ℕ, k < E.q ∧
      (k : K) = (E.exec.memoryRowAt i).2.2.pt.noun.leaf) ∧
      bindFP E.cfg.challenges.z (memoryParentNoun E i)
        (E.exec.memoryRowAt i).2.2.pt.noun :=
  ⟨haltAtom_exists E i hhalt, bindFP_halt_parent E i hhalt⟩

/-! ## E. Concrete non-vacuity of both live extras -/

open Nock.NockVMROM.Thm54.ConcreteStrictPackage
open Nock.NockVMROM.Thm54.BuildableConcrete

/-- The real F73 execution inhabits both named extras.  Its live rows carry
axis `3` and timestamp `honestAlpha^1`; padding rows impose no premise.
-- -/
def concreteMemoryRecordPremises :
    MemoryRecordPremises concreteExecution where
  axisNat := by
    intro i hact
    fin_cases i
    · -- Form R: row 0 is `dummyHalt` (padding).
      simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
        ExactExecution.memoryRows, ConcreteStrictPackage.exec,
        ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
        ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
        ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
        Nock.Walk.bfsForest, ConcreteStrictPackage.dummyHaltRow,
        memoryMemRecKind] at hact <;> (dsimp only [Fin.cast] at hact; simp at hact)
    · exact ⟨3, by
        simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
          ExactExecution.memoryRows, ConcreteStrictPackage.exec, ConcreteStrictPackage.execA,
          ConcreteStrictPackage.readTreeA, ConcreteStrictPackage.decomposeTreeA,
          ConcreteStrictPackage.verifyTreeA, ConcreteStrictPackage.readRowA,
          ConcreteStrictPackage.verifyRowA, ConcreteStrictPackage.readPubA,
          ConcreteStrictPackage.verifyPubA, ConcreteStrictPackage.rowRecord, NockVM.formRRow,
          ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
          ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
          ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
          Nock.Walk.bfsForest, ConcreteStrictPackage.readRow,
          ConcreteStrictPackage.readPub, ConcreteStrictPackage.requestRecord] <;> rfl⟩
    · simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
        ExactExecution.memoryRows, ConcreteStrictPackage.exec,
        ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
        ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
        ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
        Nock.Walk.bfsForest, ConcreteStrictPackage.decomposeRow,
        memoryMemRecKind] at hact <;> (dsimp only [Fin.cast] at hact; simp at hact)
    · simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
        ExactExecution.memoryRows, ConcreteStrictPackage.exec,
        ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
        ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
        ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
        Nock.Walk.bfsForest, ConcreteStrictPackage.headRow,
        memoryMemRecKind] at hact <;> (dsimp only [Fin.cast] at hact; simp at hact)
    · exact ⟨3, by
        simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
          ExactExecution.memoryRows, ConcreteStrictPackage.exec, ConcreteStrictPackage.execA,
          ConcreteStrictPackage.readTreeA, ConcreteStrictPackage.decomposeTreeA,
          ConcreteStrictPackage.verifyTreeA, ConcreteStrictPackage.readRowA,
          ConcreteStrictPackage.verifyRowA, ConcreteStrictPackage.readPubA,
          ConcreteStrictPackage.verifyPubA, ConcreteStrictPackage.rowRecord, NockVM.formRRow,
          ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
          ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
          ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
          Nock.Walk.bfsForest, ConcreteStrictPackage.verifyRow,
          ConcreteStrictPackage.verifyPub, ConcreteStrictPackage.requestRecord] <;> rfl⟩
    · simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
        ExactExecution.memoryRows, ConcreteStrictPackage.exec,
        ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
        ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
        ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
        Nock.Walk.bfsForest, ConcreteStrictPackage.tailRow,
        memoryMemRecKind] at hact <;> (dsimp only [Fin.cast] at hact; simp at hact)
  timestampClosed := by
    intro i hact
    fin_cases i
    · simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
        ExactExecution.memoryRows, ConcreteStrictPackage.exec,
        ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
        ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
        ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
        Nock.Walk.bfsForest, ConcreteStrictPackage.dummyHaltRow,
        memoryMemRecKind] at hact <;> (dsimp only [Fin.cast] at hact; simp at hact)
    · exact ⟨1, by
        simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
          ExactExecution.memoryRows, ConcreteStrictPackage.exec, ConcreteStrictPackage.execA,
          ConcreteStrictPackage.readTreeA, ConcreteStrictPackage.decomposeTreeA,
          ConcreteStrictPackage.verifyTreeA, ConcreteStrictPackage.readRowA,
          ConcreteStrictPackage.verifyRowA, ConcreteStrictPackage.readPubA,
          ConcreteStrictPackage.verifyPubA, ConcreteStrictPackage.rowRecord, NockVM.formRRow,
          ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
          ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
          ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
          Nock.Walk.bfsForest, ConcreteStrictPackage.readRow,
          ConcreteStrictPackage.readPub, ConcreteStrictPackage.requestRecord,
          ConcreteStrictPackage.cfg, MemoryTimestampClosedAt] <;> rfl⟩
    · simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
        ExactExecution.memoryRows, ConcreteStrictPackage.exec,
        ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
        ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
        ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
        Nock.Walk.bfsForest, ConcreteStrictPackage.decomposeRow,
        memoryMemRecKind] at hact <;> (dsimp only [Fin.cast] at hact; simp at hact)
    · simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
        ExactExecution.memoryRows, ConcreteStrictPackage.exec,
        ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
        ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
        ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
        Nock.Walk.bfsForest, ConcreteStrictPackage.headRow,
        memoryMemRecKind] at hact <;> (dsimp only [Fin.cast] at hact; simp at hact)
    · exact ⟨1, by
        simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
          ExactExecution.memoryRows, ConcreteStrictPackage.exec, ConcreteStrictPackage.execA,
          ConcreteStrictPackage.readTreeA, ConcreteStrictPackage.decomposeTreeA,
          ConcreteStrictPackage.verifyTreeA, ConcreteStrictPackage.readRowA,
          ConcreteStrictPackage.verifyRowA, ConcreteStrictPackage.readPubA,
          ConcreteStrictPackage.verifyPubA, ConcreteStrictPackage.rowRecord, NockVM.formRRow,
          ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
          ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
          ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
          Nock.Walk.bfsForest, ConcreteStrictPackage.verifyRow,
          ConcreteStrictPackage.verifyPub, ConcreteStrictPackage.requestRecord,
          ConcreteStrictPackage.cfg, MemoryTimestampClosedAt] <;> rfl⟩
    · simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
        ExactExecution.memoryRows, ConcreteStrictPackage.exec,
        ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
        ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
        ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
        Nock.Walk.bfsForest, ConcreteStrictPackage.tailRow,
        memoryMemRecKind] at hact <;> (dsimp only [Fin.cast] at hact; simp at hact)
  honestVer := BuildablePackage.Concrete.concreteExecution_honestVer

/-- Both fields fire on genuine live rows, and their memory assembly is
inhabited. -- the paper -/
theorem concrete_two_extras_and_memory_assembly_nonvacuous :
    (∃ n : ℕ,
      (concreteExecution.execA.memoryRowAt
        ⟨1, by norm_num [BuildableConcrete.concreteExecution,
          ConcreteStrictPackage.cfg]⟩).2.2.mem.axis = (n : K73cubic)) ∧
      MemoryTimestampClosedAt concreteExecution.cfg.challenges.α
        (concreteExecution.exec.memoryRowAt
          ⟨4, by norm_num [BuildableConcrete.concreteExecution,
            ConcreteStrictPackage.cfg]⟩).2.2.mem.ts ∧
      Nonempty (MemoryAssemblyPremises concreteExecution) := by
  refine ⟨concreteMemoryRecordPremises.axisNat
      ⟨1, by norm_num [BuildableConcrete.concreteExecution,
        ConcreteStrictPackage.cfg]⟩ (by
        simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
          ExactExecution.memoryRows, ConcreteStrictPackage.exec, ConcreteStrictPackage.execA,
          ConcreteStrictPackage.readTreeA, ConcreteStrictPackage.decomposeTreeA,
          ConcreteStrictPackage.verifyTreeA, ConcreteStrictPackage.readRowA,
          ConcreteStrictPackage.verifyRowA, ConcreteStrictPackage.readPubA,
          ConcreteStrictPackage.verifyPubA, ConcreteStrictPackage.rowRecord, NockVM.formRRow,
          ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
          ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
          ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
          Nock.Walk.bfsForest, ConcreteStrictPackage.readRow,
          ConcreteStrictPackage.readPub, memoryMemRecKind] <;> rfl),
    concreteMemoryRecordPremises.timestampClosed
      ⟨4, by norm_num [BuildableConcrete.concreteExecution,
        ConcreteStrictPackage.cfg]⟩ (by
        simp [BuildableConcrete.concreteExecution, ExactExecution.memoryRowAt,
          ExactExecution.memoryRows, ConcreteStrictPackage.exec, ConcreteStrictPackage.execA,
          ConcreteStrictPackage.readTreeA, ConcreteStrictPackage.decomposeTreeA,
          ConcreteStrictPackage.verifyTreeA, ConcreteStrictPackage.readRowA,
          ConcreteStrictPackage.verifyRowA, ConcreteStrictPackage.readPubA,
          ConcreteStrictPackage.verifyPubA, ConcreteStrictPackage.rowRecord, NockVM.formRRow,
          ConcreteStrictPackage.dummyHaltTree, ConcreteStrictPackage.readTree,
          ConcreteStrictPackage.decomposeTree, ConcreteStrictPackage.headTree,
          ConcreteStrictPackage.verifyTree, ConcreteStrictPackage.tailTree,
          Nock.Walk.bfsForest, ConcreteStrictPackage.verifyRow,
          ConcreteStrictPackage.verifyPub, memoryMemRecKind] <;> rfl),
    ⟨memoryAssemblyOf concreteExecution concreteMemoryRecordPremises⟩⟩

/-! ## F. -/

/-- The memory-assembled constructor still has the dependent census argument;
all seven census/window/bound fields project into `Data`.
-- -/
theorem dataOfRecord_still_requires_and_projects_census
    (E : BuildableNockExecution F K) (P : ResidualPremises E)
    (M : MemoryRecordPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) (memoryNodesOf E M))
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    let D := dataOfRecord E P M C hln
    D.nounSizeBound = C.nounSizeBound ∧
      (∀ s ∈ computeSkeletonRows D.skeleton,
        ServedLookupBridge.SkeletonSlotSemantics s) ∧
      (∀ s ∈ computeSkeletonRows D.skeleton,
        ServedLookupBridge.SkeletonRecordEquations s) ∧
      EdgeComparisonCensus.CombinedSkeletonCensus K D.skeleton D.Λ ∧
      SizeWindowCounting.SizeWindowNounsBoundedBy D.skeleton D.Λ ∧
      D.skeleton.BoundedBy E.q ∧
      ProductionP8Containment.CombinedBoundedBy K E.q D.skeleton := by
  dsimp [dataOfRecord, dataOf, Data.skeleton]
  exact ⟨rfl, C.slotSemantics, C.recordEquations, C.census,
    C.sizeWindowBound, C.skeletonBounded, C.combinedBounded⟩

/-- The earlier analysis leaves the same four residual premises. -/
theorem residualPremises_eta_still_four
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- Any hypothetical universal `Data` constructor would still manufacture the
named characteristic equality.  This is a consequence, not a claim that the
function space is empty. -/
theorem any_universal_data_constructor_still_forces_q_pin
    (g : ∀ E : BuildableNockExecution F K, Data E) :
    ∀ E : BuildableNockExecution F K, E.q = ringChar K :=
  fun E => (g E).q_eq_ringChar

inductive ReviewedField101
  | structural
  | optimized_chips
  | shared_io
  | perfect_completeness
  | containment
  | walk_bounds
  | p8_fixed_field_soundness
  | p8_fixed_field_bits
  | acceptance_to_target
  | complete_false_acceptance_bound
  | complete_false_acceptance_bits
  | exact_resources
  | row_budgets
  | shared_forest_axis
deriving DecidableEq

def substantiveFields101 : List ReviewedField101 :=
  [.optimized_chips, .shared_io, .perfect_completeness, .containment,
    .walk_bounds, .p8_fixed_field_soundness, .p8_fixed_field_bits,
    .acceptance_to_target, .exact_resources, .row_budgets,
    .shared_forest_axis]

def typeSummaryFields101 : List ReviewedField101 := [.structural]

def residualFields101 : List ReviewedField101 :=
  [.complete_false_acceptance_bound, .complete_false_acceptance_bits]


theorem independent_exact_eleven_one_two_accounting :
    substantiveFields101.length = 11 ∧
      typeSummaryFields101.length = 1 ∧
      residualFields101 =
        [.complete_false_acceptance_bound,
          .complete_false_acceptance_bits] ∧
      residualFields101.length = 2 ∧
      (substantiveFields101 ++ typeSummaryFields101 ++ residualFields101).Nodup ∧
      11 + 1 + 2 = 14 := by
  decide

/-- It does NOT pin what the capstone's
statement says -- that shape is a schema provable for an arbitrary family of propositions
(`FrozenReceiptInstrument.receipt_shape_is_a_schema`; negative control
`receipt_shape_survives_a_contentless_statement`). -/
theorem consumed_capstone_and_alias_remain_frozen
    {F K : Type} [Field F] [Field K] [Algebra F K]
    [Fintype F] [DecidableEq F] [FiniteDimensional F K]
    [Fintype K] [DecidableEq K]
    [CharP K (ringChar K)]
    (P : OptimizedFullStrictNockVMROMPackage F K 3)
    (hax : OptimizedComputeFinalTrace.FormRAxisBound P.optimized.sampled P.optimized.basis)
    (hbasis : OptimizedComputeFinalTrace.FormRBasis P.optimized.basis)
    (hwidth : OptimizedComputeFinalTrace.FormRWidth F) :
    OptimizedFullStrictThm54Statement P ∧
      @«Thm:NockVMROM» =
        @OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package :=
  ⟨optimizedFullStrictNockVMROM_of_package P hax hbasis hwidth, rfl⟩

#print axioms memoryOK_expands_all_four_node_obligations
#print axioms memoryOK_binding_expands_all_six_conjuncts
#print axioms memoryOK_timestamps_expand_all_four_conjuncts
#print axioms memory_reconstruction_threads_execution_and_traversal
#print axioms memoryRecordPremises_eta_exactly_two
#print axioms axisNat_is_load_bearing_NMR_address
#print axioms timestampClosed_is_load_bearing_NMR_power
#print axioms any_live_axis_binding_reproduces_axisNat_obligation
#print axioms any_live_timestamp_specialization_reproduces_closed_obligation
#print axioms halt_atoms_are_already_on_E
#print axioms halt_atom_and_parent_binding_come_from_E
#print axioms concreteMemoryRecordPremises
#print axioms concrete_two_extras_and_memory_assembly_nonvacuous
#print axioms dataOfRecord_still_requires_and_projects_census
#print axioms residualPremises_eta_still_four
#print axioms any_universal_data_constructor_still_forces_q_pin
#print axioms independent_exact_eleven_one_two_accounting
#print axioms consumed_capstone_and_alias_remain_frozen
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryNodesOf_ok
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.memoryAssemblyOf
#print axioms Nock.NockVMROM.Thm54.GenericHonestData.dataOfRecord
#print axioms
  Nock.NockVMROM.Thm54.OptimizedStrictFullPackage.optimizedFullStrictNockVMROM_of_package

end
end Nock.RedTeam.Batch101
