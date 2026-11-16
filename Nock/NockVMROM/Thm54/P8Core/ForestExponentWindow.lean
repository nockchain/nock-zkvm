/-
  Nock/NockVMROM/Thm54/P8Core/ForestExponentWindow.lean

  Relocated below the statement file: declarations of
  `Nock.NockVMROM.Thm54.ForestExponentWindow`,
  moved verbatim by `scripts/move-decls.py` (names, docstrings, attributes, statements and
  proofs unchanged; only the namespace / `open` / `variable` context is re-opened here).  The
  remaining declarations stay in `Nock/NockVMROM/Thm54/ForestExponentWindow.lean`, which imports this module.
  This module must not import `Nock.NockVMROM.Thm54.OptimizedStrictFullPackage`.
-/
import Nock.NockVMROM.Thm54.ExactTraversal
import Nock.AxisBatching
import Nock.AxisBridge
import Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
import Nock.NockVMROM.Thm54.SemanticStrategy
import Nock.NockVMROM.Thm54.SemanticTimestampStrategy
import Nock.NockVMROM.Thm54.TemplateAxisCounting
import Nock.NockVMROM.Thm54.TemplateAxisStructure

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.NockVMROM.Thm54.ForestExponentWindow

open scoped Classical
open Nock Nock.Walk
open Nock.NockVMROM
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ProductionAxisStructureVerifier
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.TemplateAxisCounting
open Nock.NockVMROM.Thm54.TemplateAxisStructure
open Nock.AxisBridge
open Nock.AxisBatching

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]
variable [FiniteDimensional F K] [Fintype K] [DecidableEq K]
variable [CharP K (ringChar K)]
variable {base : SemanticStrategy.SemanticSkeleton}

/-- Relabelling twice is relabelling once. -/
theorem mapNTree_comp {A B C : Type} (f : A → B) (g : B → C) (t : NTree A) :
    mapNTree g (mapNTree f t) = mapNTree (fun a => g (f a)) t := by
  let P := fun t : NTree A => mapNTree g (mapNTree f t) = mapNTree (fun a => g (f a)) t
  change P t
  apply NTree.rec (motive_1 := P) (motive_2 := fun ts => ∀ c ∈ ts, P c)
  · intro lbl children ih
    simp only [P, mapNTree, List.map_map]
    refine congrArg (NTree.node (g (f lbl))) ?_
    apply List.map_congr_left
    intro c hc
    exact ih c hc
  · intro c hc; simp at hc
  · intro head tail ihHead ihTail c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact ihHead
    · exact ihTail c hc

end

end Nock.NockVMROM.Thm54.ForestExponentWindow
