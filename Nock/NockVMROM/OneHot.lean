import Nock.Framework
import Nock.NMRMEF
import Nock.NockVMROM.Language
import Nock.NockVMROM.Separation
import Nock.ComputeTable
import Nock.NockVM

/-!
# S3 — `nock_opcodeMemoryOneHot` : opcode one-hot of size 10, arity 3

Corrected reading (SC3/SC13): the compute row selects exactly one action among the **10 numeric ROM
opcodes** `OP_0..OP_9` **and** the separately-typed structural `cons` action; their combined sum is
`1`.  We do NOT claim a bare 10-column sum (which is false on `cons` rows) — the `Fin 11` invariant
`nock_opcode_oneHot` is split as `Fin 10 (numeric) + cons`.  Every row opens `≥ 1` memory record
(`record_pos`, `OP_IO = OP`), so the paper's cond-4b `io_zero` antecedent is unsatisfiable — vacuous
by design (SC9), disclosed, not proved as a non-trivial constraint.  Arity `MOP = 3` is
`mem_record_arity` (cond-3, `record_arity_le`).
-/

namespace Nock.NockVMROM

open Nock Nock.Framework Nock.ComputeTable

/-- **S3: NockVMROM opcode/memory one-hot of size 10 and arity 3.** -/
noncomputable instance nock_opcodeMemoryOneHot (F K : Type) [Field F] [Field K]
    (α β : K) (Ksz : ℕ) :
    OpcodeMemoryOneHot (Tag F K α β Ksz) (nmrMEF F K) K 10 3 where
  Row := State
  numericSelector st op := ComputeTable.opSel (K := K) st (sfin op.castSucc)
  structuralSelector st := ComputeTable.opSel (K := K) st (sfin (Fin.last 10))
  recordCount := Nock.Framework.recordCount
  numeric_boolean st op := ComputeTable.opSel_boolean (K := K) st (sfin op.castSucc)
  structural_boolean st := ComputeTable.opSel_boolean (K := K) st (sfin (Fin.last 10))
  exactly_one_action_per_compute_row st := by
    rw [← Fin.sum_univ_castSucc (f := fun j => ComputeTable.opSel (K := K) st (sfin j))]
    exact (nock_opcode_oneHot K st).2
  record_arity_le st := recordCount_le st
  record_pos st := recordCount_pos st

end Nock.NockVMROM

#print axioms Nock.NockVMROM.nock_opcodeMemoryOneHot
