/-
  Nock/NockVMROM/Thm54/P8Core/TraceGen/GenTierAMemAccept.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.TraceGen.GenTierAMemAccept`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/TraceGen/GenTierAMemAccept.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.NockVMROM.Thm54.MonolithicRowLayout
import Nock.NockVMROM.Thm54.SemanticStrategy

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk Nock.Noun
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.NockVMROM.Thm54.RowLayout
open MemoryTable
variable {K : Type} [Field K]
variable {lmb : K}

omit [Field K] in
theorem mapNTree_inTree {α β} (f : α → β) :
    ∀ {u v : NTree α}, InTree u v → InTree (mapNTree f u) (mapNTree f v)
  | _, _, InTree.here _ => InTree.here _
  | _, _, InTree.sub hs ht =>
      InTree.sub (by
          simpa [mapNTree_children] using List.mem_map.mpr ⟨_, hs, rfl⟩)
        (mapNTree_inTree f ht)

end Nock.NockVMROM.Thm54.TraceGen
