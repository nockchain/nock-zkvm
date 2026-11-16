/-
  Nock/NockVMROM/Thm54/HonestCommitmentNodes.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.HonestCommitment`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/HonestCommitment.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.SemanticTimestampStrategy

namespace Nock.NockVMROM.Thm54

namespace HonestCommitment

open Nock Nock.Walk Nock.NockVMROM
open SemanticStrategy SemanticTimestampStrategy

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- A committed compute node. -/
structure ComputeNode (K : Type) [Field K] where
  skel : ComputeRowSkeleton
  stamp : ComputeTimestampRow
  row : ComputeTable.State × ComputeTable.DTcomp K

/-- A committed memory node. -/
structure MemoryNode (K : Type) [Field K] where
  skel : MemoryRowSkeleton
  stamp : MemoryTimestampRow
  row : MemoryTable.MState × MemoryTable.DTmem K

end

end HonestCommitment

end Nock.NockVMROM.Thm54
