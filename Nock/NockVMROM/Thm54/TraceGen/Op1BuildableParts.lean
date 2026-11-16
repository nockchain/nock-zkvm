/-
  Nock/NockVMROM/Thm54/TraceGen/Op1BuildableParts.lean

  The non-semantic side-obligations of a
  `BuildableNockExecution (ZMod 97) (ZMod 97)` for `*[0 [1 5]] = 5`, discharged for the concrete
  `Op1Config.exec`.

  `BuildableNockExecution` has fourteen fields (`BuildableExecution.lean:61`).  Two of them —
  `semanticData : SemanticTrace.ExactExecutionSemanticData` and
  `memoryTrace : ServedMemoryTrace.ExactServedMemoryTrace` — are the deep semantic CORE machinery
  (the `NounRealizedTraversableChainedSemanticExactLanguage` bundle, the per-row
  `ComputeRowSemanticData`, and the recursively generated served forest trace).  Those two remain
  the open obligation for gate #1; see the final `#check`ed remaining-obligation note.

  Everything else — the finite request-uniqueness, the `M + 2L` record balance, the finite-field
  range/nondegeneracy conditions, and the two orbit IO-capacity bounds — depends only on `cfg`/`exec`
  and is discharged here, over `K = ZMod 97`, `q = 97`, `Λ = 3`.  This mirrors the shape of the F97
  fixture `DistinctCensusExecution.distinctCensusExecution`'s non-semantic fields at minimal size.
-/
import Nock.NockVMROM.Thm54.TraceGen.Op1Config
import Nock.NockVMROM.Thm54.Language
import Nock.NockVMROM.Thm54.MemoryMplus2L
import Nock.NockVMROM.Thm54.TraceGen.RowEncode

namespace Nock.NockVMROM.Thm54.TraceGen.Op1Config

open Nock Nock.Walk
open Nock.NockVMROM.Thm54

/-! ## The two authoritative BFS row lists, explicitly -/

/-- The single compute row in BFS order. -/
theorem computeRows_eq (z α : F) :
    (exec z α).computeRows = [computeRow z α] := by
  simp [ExactExecution.computeRows, exec, bfsForest]

/-- The six memory rows in BFS order `halt_seed, read, dec, halt_1, verify, halt_r`. -/
theorem memoryRows_eq (z α : F) :
    (exec z α).memoryRows =
      [dummyHaltRow z, readRow z α, decomposeRow z α, headRow z, verifyRow z α, tailRow z] := by
  simp [ExactExecution.memoryRows, exec, dummyHaltTree, readTree, decomposeTree, headTree,
    verifyTree, tailTree, bfsForest]

/-! ## Raw canonical IO projections of the slice -/

/-- The one active request emitted by the `OP_1` row (its single live record). -/
theorem rawRequests_eq (z α : F) :
    (exec z α).rawRequests = [requestRecord z α] := by
  simp [ExactExecution.rawRequests, computeRows_eq, computeRow, computePub,
    NockVM.activeRequestRecords]

/-- The one served response emitted by the `read_root` row. -/
theorem rawResponses_eq (z α : F) :
    (exec z α).rawResponses = [rowRecord z α] := by
  simp [ExactExecution.rawResponses, memoryRows_eq, dummyHaltRow, readRow, decomposeRow, headRow,
    verifyRow, tailRow, dummyHaltPub, readPub, decomposePub, headPub, verifyPub, tailPub,
    MemoryTable.responseRecords]

/-! ## The twelve non-semantic `BuildableNockExecution` fields -/

/-- `requestNodup`: the execution-derived requests are unique. -/
theorem requestNodup (z α : F) : (exec z α).derivedRequestIO.Nodup := by
  simp [ExactExecution.derivedRequestIO, rawRequests_eq]

/-- Both wrapper counts are one: one `read_root` row and one `verify_child` row. -/
theorem memoryStateCounts (z α : F) :
    RowLayout.memoryStateCount (exec z α) .read_root = 1 ∧
      RowLayout.memoryStateCount (exec z α) .verify_child = 1 := by
  constructor <;>
    simp [RowLayout.memoryStateCount, RowLayout.fibreCount, memoryRows_eq,
      dummyHaltRow, dummyHaltPub, readRow, decomposeRow, headRow, verifyRow, tailRow,
      readPub, decomposePub, headPub, verifyPub, tailPub]

/-- `recordCountBalance`: one `verify_child` wrapper per `read_root` wrapper. -/
theorem recordCountBalance (z α : F) : RowLayout.RecordCountBalanced (exec z α) := by
  rw [RowLayout.RecordCountBalanced, (memoryStateCounts z α).1, (memoryStateCounts z α).2]

/-- `q_le_ringChar`: the Nat atom bound `q = 97` embeds without wraparound in `ZMod 97`. -/
theorem q_le_ringChar : (97 : ℕ) ≤ ringChar (ZMod 97) := by
  rw [ZMod.ringChar_zmod_n]

/-- `two_ne_zero`: the binary Nock-axis recurrence is nondegenerate over `ZMod 97`. -/
theorem two_ne_zero : (2 : ZMod 97) ≠ 0 := by decide

/-- `Ksz_lt_ringChar`: the IO count bound `Ksz = 4` is below the field characteristic. -/
theorem Ksz_lt_ringChar (z α : F) : (cfg z α).Ksz < ringChar (ZMod 97) := by
  rw [ZMod.ringChar_zmod_n]; norm_num [cfg]

/-- `programIOCapacity`: the request accumulator's active prefix fits the `h = 3` orbit. -/
theorem programIOCapacity (z α : F) :
    (exec z α).derivedRequestIO.length + 1 ≤ 2 ^ (cfg z α).orbit.h := by
  simp only [ExactExecution.derivedRequestIO, List.length_map, rawRequests_eq]
  norm_num [cfg, executionOrbit]

/-- The row-level record is not the padding record (its `axis = T = 2 ≠ 0`). -/
theorem rowRecord_ne_zero (z α : F) : rowRecord z α ≠ ComputeTable.MemRec.zero := by
  intro h
  have hax := congrArg ComputeTable.MemRec.axis h
  have h2 : (2 : F) ≠ 0 := two_ne_zero
  simp [rowRecord, NockVM.formRRow, ComputeTable.MemRec.zero, MemoryTable.formRT,
    MemoryTable.formRDefault, h2] at hax

open scoped Classical in
theorem memory_cprime_eq (z α : F) :
    ∀ row ∈ (exec z α).memoryRows, row.2.2.cprime =
      (fun m => if m = rowRecord z α then rowCprime z α else 1) row.2.2.mem := by
  have hne := rowRecord_ne_zero z α
  intro row hmem
  rw [memoryRows_eq] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp [dummyHaltRow, readRow, decomposeRow, headRow, verifyRow, tailRow,
      dummyHaltPub, readPub, decomposePub, headPub, verifyPub, tailPub,
      MemoryTable.Pub.cprime, Ne.symm hne]

open scoped Classical in
theorem memory_cprimeCoherent (z α : F) : (exec z α).CprimeCoherent :=
  ExactExecution.cprimeCoherent_of_fun (fun m => if m = rowRecord z α then rowCprime z α else 1)
    (memory_cprime_eq z α)

/-- The executed trace is the Form R row encode of the a-bearing view
(`BuildableNockExecution.exec_encode`). -/
theorem exec_encode (z α : F) : exec z α = (execA z α).encodeMem :=
  RowEncode.eq_encodeMem_of rfl (by
    simp [exec, execA, mapNTree, dummyHaltTree, readTree, decomposeTree, headTree, verifyTree,
      tailTree, dummyHaltTreeA, readTreeA, decomposeTreeA, headTreeA, verifyTreeA, tailTreeA,
      dummyHaltRow, readRow, decomposeRow, headRow, verifyRow, tailRow, dummyHaltRowA, readRowA,
      decomposeRowA, headRowA, verifyRowA, tailRowA, dummyHaltPubA, readPubA, decomposePubA,
      headPubA, verifyPubA, tailPubA, dummyHaltPub, readPub, decomposePub, headPub, verifyPub,
      tailPub, rowRecord, rowCprime])

/-- `memoryIOCapacity`: the response accumulator's active prefix fits the `h = 3` orbit. -/
theorem memoryIOCapacity (z α : F) :
    (exec z α).derivedResponseIO.length + 1 ≤ 2 ^ (cfg z α).orbit.h := by
  rw [ExactExecution.derivedResponseIO_eq_map_encRecC (exec z α) (memory_cprimeCoherent z α)]
  simp only [List.length_map, rawResponses_eq]
  norm_num [cfg, executionOrbit]

end Nock.NockVMROM.Thm54.TraceGen.Op1Config

#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.requestNodup
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.recordCountBalance
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.q_le_ringChar
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.Ksz_lt_ringChar
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.programIOCapacity
#print axioms Nock.NockVMROM.Thm54.TraceGen.Op1Config.memoryIOCapacity
