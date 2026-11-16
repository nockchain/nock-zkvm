/-
  Nock/NockVMROM/Thm54/P8Core/TraceGen/GenTierAComputeLink.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.TraceGen.GenTierAComputeLink`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/TraceGen/GenTierAComputeLink.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.NockVMROM.Thm54.SemanticStrategy

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun Nock.NockVM
open Nock.ComputeTable
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
variable {K : Type} [Field K]

omit [Field K] in
theorem bfsForest_mapNTree_singleton {α β : Type*} (f : α → β) (t : NTree α) :
    bfsForest [mapNTree f t] = (bfsForest [t]).map (mapNTree f) := by
  simpa using bfsForest_mapNTree f [t]

end Nock.NockVMROM.Thm54.TraceGen
