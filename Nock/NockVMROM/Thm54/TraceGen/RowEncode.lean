import Nock.NockVMROM.Thm54.SemanticTimestampStrategy

/-!
# Downstream row-encode worker for hand-built and generated fixtures

It adds no field, no hypothesis and no carrier change.
-/

namespace Nock.NockVMROM.Thm54.TraceGen.RowEncode

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- An execution is the row encode of an a-bearing one when the compute trees agree and the
memory forest is the label-wise encode. -/
theorem eq_encodeMem_of {cfg : ExactConfig F K} {exec execA : ExactExecution cfg}
    (hc : exec.computeTree = execA.computeTree)
    (hm : exec.memoryForest = execA.memoryForest.map (mapNTree (MemoryRowTemplate.encodeRow cfg.challenges.lam))) :
    exec = execA.encodeMem := by
  cases exec
  cases execA
  simp only [ExactExecution.encodeMem] at hc hm ⊢
  subst hc
  subst hm
  rfl

/-- The encode of an active (`read_root`) row. -/
@[simp] theorem encodeRow_read_root (lmb : K) (i : MemoryTable.Inputs K) (p : MemoryTable.Pub K) :
    MemoryRowTemplate.encodeRow lmb (.read_root, i, p) =
      (.read_root, i,
        { p with
          mem := NockVM.formRRow p.mem lmb
          cprime? := some (NockVM.formRCprime p.mem lmb)
          lambda? := some lmb }) := by
  simp [MemoryRowTemplate.encodeRow, memoryMemRecKind]

/-- The encode of an active (`verify_child`) row. -/
@[simp] theorem encodeRow_verify_child (lmb : K) (i : MemoryTable.Inputs K) (p : MemoryTable.Pub K) :
    MemoryRowTemplate.encodeRow lmb (.verify_child, i, p) =
      (.verify_child, i,
        { p with
          mem := NockVM.formRRow p.mem lmb
          cprime? := some (NockVM.formRCprime p.mem lmb)
          lambda? := some lmb }) := by
  simp [MemoryRowTemplate.encodeRow, memoryMemRecKind]

/-- The encode of a `decompose` row only writes the package `λ` (`lmb`). -/
@[simp] theorem encodeRow_decompose (lmb : K) (i : MemoryTable.Inputs K) (p : MemoryTable.Pub K) :
    MemoryRowTemplate.encodeRow lmb (.decompose, i, p) =
      (.decompose, i, { p with lambda? := some lmb }) := by
  simp [MemoryRowTemplate.encodeRow, memoryMemRecKind]

/-- The encode of a `halt` row only writes the package `λ` (`lmb`). -/
@[simp] theorem encodeRow_halt (lmb : K) (i : MemoryTable.Inputs K) (p : MemoryTable.Pub K) :
    MemoryRowTemplate.encodeRow lmb (.halt, i, p) =
      (.halt, i, { p with lambda? := some lmb }) := by
  simp [MemoryRowTemplate.encodeRow, memoryMemRecKind]

/-- Encoding commutes with tree relabelling (`mapNTree` functoriality). -/
theorem mapNTree_encodeRow_node (lmb : K) (lbl : MemoryTable.MState × MemoryTable.DTmem K)
    (cs : List (NTree (MemoryTable.MState × MemoryTable.DTmem K))) :
    mapNTree (MemoryRowTemplate.encodeRow lmb) (.node lbl cs) =
      .node (MemoryRowTemplate.encodeRow lmb lbl) (cs.map (mapNTree (MemoryRowTemplate.encodeRow lmb))) := by
  simp [mapNTree]

end Nock.NockVMROM.Thm54.TraceGen.RowEncode
