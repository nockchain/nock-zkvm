/-
  Nock/RedTeam/Batch192Thm54DataAtTierA.lean

  **`HonestCommitment.Data` inhabited at the generated carrier.**

  That is not idle: each premise had been justified separately, and a conjunction of
  individually-satisfiable premises can still be empty.  `GA` settled the same question for `mt` and
  `Batch221` for `BuildableNockExecution`; both were settled by **compiling a term**, and this does
  the same for `Data`.

  `GG` retired two premises rather than assuming them — `skeletonBounded`, which had **no supplier**
  at all before it (`EP.1`), and `SkeletonAxisRange`.  Their replacements are conditions on the
  *program*: `1 < q`, `subject`/`formula` `q`-bounded, and `evalGBy q fuel subject formula = some
  result`.  The last of those did not exist at `769` for this program; `b192_evalG` supplies it with
  the same simp set `dot_evalFBy` (`GenTierA.lean:159`) uses at `97`.

  **Scope.**  One program, one configuration.  Tier A's eight rows reach three of the eleven
  `ComputeTable.State` values, so this witnesses the chain at those three and no others — the
  evidence-base problem `GG` §4 recorded, where `SkeletonAxisRange`'s OP0 conjunct turned out to
  have held vacuously here because Tier A has no `.s0` row.  Nothing here is a capstone: `Inputs`,
  `buildFullPackage` and `claimedResult = result` are untouched.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenHonestData
import Nock.RedTeam.Batch221Thm54BuildableAtTierA

set_option autoImplicit false
set_option maxHeartbeats 2000000

namespace Nock.RedTeam.Batch192

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54
open Nock.RedTeam

abbrev DK := DotConfig769.K
abbrev DF := DotConfig769.F
noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

noncomputable section

/-! ## 1. The one piece `GG`'s retirement of `skeletonBounded` needs and the tree lacked

`dot_evalFBy` (`GenTierA.lean:159`) is the `evalFBy` form at `97`.  `genComputeSkeleton_skeletonBounded`
wants `evalGBy` at the package's own `q`.  Same simp set. -/

theorem b192_evalG :
    FieldEmbedding.evalGBy 769 8 dotSubject dotFormula = some dotResult := by
  simp [FieldEmbedding.evalGBy, dotSubject, dotFormula, dotParentTail,
    dotBranchPair, dotCondFormula, dotThenFormula, dotElseFormula,
    dotThenTail, dotOp2B, dotOp2C, dotOp9Formula, dotOp9Tail, dotCoreFormula,
    dotCore, dotElem0, dotElem1, dotResult, Noun.slot]

/-! ## 2. `Data` at the generated carrier -/



/-- **`Data` inhabited**, over exactly `Batch221`'s `BuildableNockExecution`. -/
def b192Data : Data Batch221.b221Buildable :=
  genData (F := DF) seedZ alphaA 0 0 0
    Batch216.b216Chal Batch180.dot_hinp
    64 executionOrbit Batch216.b216_horb (genComputeSkeleton_dot 0)
    Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
    769 (by norm_num) DotConfig769.Λ (by norm_num [DotConfig769.Λ])
    Batch180.dot_air_traceConfined
    Batch180.dot_hb (by norm_num) DotConfig769.ringChar_K.symm Batch180.dot_haxis
    _ _
    (genExactExecution_requestNodup (F := DF) seedZ alphaA Batch216.b216Chal 64
      executionOrbit Batch216.b216_horb 0 0 0 (dotTree (K := DK))
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
      Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
      (by have := Batch180.dot_accAt_le
          have h192 := Batch180.alphaA_order_eq_192
          omega))
    (genBuildable_hbal (F := DF) Batch216.b216Chal 64 executionOrbit Batch216.b216_horb
      seedZ alphaA 0 0 0 (memInputs seedZ) _ (dotTree (K := DK))
      Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le)
    (le_of_eq DotConfig769.ringChar_K.symm) two_ne_zero Batch221.b221_hKszChar
    (genBuildable_hprog (F := DF) seedZ alphaA Batch216.b216Chal 64 executionOrbit
      Batch216.b216_horb 0 0 0 (dotTree (K := DK))
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
      Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
      Batch221.b221_hprogCap)
    (genBuildable_hresp (F := DF) Batch216.b216Chal 64 executionOrbit Batch216.b216_horb
      0 0 0 (genComputeRows seedZ alphaA (dotTree (K := DK)))
      (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
      Batch216.b216_mempos Batch216.b216_comp_le Batch216.b216_mem_le
      Batch221.b221_hmemCap)

/-! ## 3. Read off the assembled object -/

theorem b192_data_Λ : b192Data.Λ = DotConfig769.Λ := rfl

theorem b192_computeNodes :
    b192Data.computeNodes = genComputeNodes seedZ alphaA 0 0 0 (dotTree (K := DK)) := rfl

/-- The committed rows really are the execution's — the field, not a restatement. -/
theorem b192_compute_rows :
    mapNTree ComputeNode.row b192Data.computeNodes =
      Batch221.b221Buildable.exec.computeTree :=
  b192Data.compute_rows

/-- And the memory side likewise. -/
theorem b192_memory_rows :
    b192Data.memoryNodes.map (mapNTree MemoryNode.row) =
      Batch221.b221Buildable.execA.memoryForest :=
  b192Data.memory_rows

end

#print axioms Nock.RedTeam.Batch192.b192_evalG
#print axioms Nock.RedTeam.Batch192.b192Data
#print axioms Nock.RedTeam.Batch192.b192_compute_rows
#print axioms Nock.RedTeam.Batch192.b192_memory_rows

end Nock.RedTeam.Batch192
