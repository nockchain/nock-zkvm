import Nock.Framework
import Nock.NMRMEF
import Nock.NockVMROM.Language

/-!
# S1 — `nock_uniqueMES` : NockVMROM is `UniqueMemoryExecutionSeparable` over `nmrMEF`

Exact over `nmrMEF`; `1-1*` w.r.t.
the paper's field-timestamped `NMR^{α,β}` (SC18), bridged by `NMRRecordEncoding` (P3a).

The stronger *operational-faithfulness* companion (RVT/walk reconstruction, `equiv_compute`, WF,
shared-witness IO) is deferred to `OperationalFaithfulness.lean` (T5.6) and does NOT gate this.
-/

namespace Nock.NockVMROM

open Nock Nock.Framework

variable {F K : Type} [Field F] [Field K]

/-- Statement split `x ↦ (x_compute, x_memory)` — the product bijection. -/
def stmtSplit (F K : Type) [Field F] [Field K] :
    Stmt F K ≃ (List (ComputeTable.Inputs K × ComputeTable.Pub K)) ×
      (List (MemoryTable.Inputs K × MemoryTable.Pub K)) where
  toFun x := (x.compute, x.memory)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Witness split `w ↦ ((computeDec, progIO), memIO)` — the product bijection. -/
def witSplit (F K : Type) [Field F] [Field K] :
    Wit F K ≃ (List (ComputeTable.Dec K) × List ((nmrMEF F K).Rec)) ×
      List ((nmrMEF F K).Rec) where
  toFun w := ((w.computeDec, w.progIO), w.memIO)
  invFun p := ⟨p.1.1, p.1.2, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- **S1: NockVMROM is uniquely memory-execution separable over `nmrMEF` (no `hcorrect`, SC14).** -/
noncomputable instance nock_uniqueMES (F K : Type) [Field F] [Field K] (α β : K) (Ksz : ℕ) :
    UniqueMemoryExecutionSeparable (Tag F K α β Ksz) (nmrMEF F K) where
  ProgStatement := List (ComputeTable.Inputs K × ComputeTable.Pub K)
  MemStatement := List (MemoryTable.Inputs K × MemoryTable.Pub K)
  ProgWitness := List (ComputeTable.Dec K) × List ((nmrMEF F K).Rec)
  MemWitness := List ((nmrMEF F K).Rec)
  ProgIO := List ((nmrMEF F K).Rec)
  MemIO := List ((nmrMEF F K).Rec)
  splitStatement := stmtSplit F K
  splitWitness := witSplit F K
  computeAccepts ps pw io := ComputeTableAccepts ps pw.1 ∧ io = pw.2
  memoryAccepts ms mw io := MemoryTableAccepts ms ∧ io = mw
  ioRecords ioP ioM := (ioP, ioM)
  K := Ksz
  correct := by
    intro x
    rw [language_unfold]
    constructor
    · rintro ⟨w, hCTA, hMTA, hLmIO⟩
      exact ⟨w, w.progIO, w.memIO, ⟨hCTA, rfl⟩, ⟨hMTA, rfl⟩, hLmIO⟩
    · rintro ⟨w, ioP, ioM, ⟨hCTA, rfl⟩, ⟨hMTA, rfl⟩, hLmIO⟩
      exact ⟨w, hCTA, hMTA, hLmIO⟩

end Nock.NockVMROM

#print axioms Nock.NockVMROM.nock_uniqueMES
