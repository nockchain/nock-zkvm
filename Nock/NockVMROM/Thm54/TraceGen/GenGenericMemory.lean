/-
  Nock/NockVMROM/Thm54/TraceGen/GenGenericMemory.lean

  **`MemoryNodesOK` on the generated memory forest, for an arbitrary program.**

  `Data.memoryOK` asks for `MemoryNodesOK` at every root of the committed memory forest.  Until
  now that was available only at fixed configurations -- `dotMemForest_OK` /
  `assignedMemForest_OK_air` (Tier A, by an eight-way BFS index split) and `mmMemForest_OK`
  (matmul) -- with, in between, twelve per-opcode-arm lemmas `gen_op*_mem_OK` that cover OP0, OP1,
  OP4, OP5, OP6, OP7, OP9 and `cons` but **not** OP2, OP3 or OP8.

  No new mathematics is needed, and none is done here.  Every ingredient was already generic in the
  program; only the composition was missing:

  1. `genComputeSkeleton_tree_requests_wf` (`GenMatmulMem.lean:1226`) gives `treeRequestsWF t` for
     an arbitrary accepted program, and its induction covers **every** arm -- OP2, OP3 and OP8
     included -- so it supersedes the incomplete per-arm family.
  2. `bfsAssign_extract_requests_wf` (`:1539`) turns that into the per-request well-formedness
     `lsbTarget r.root r.axis = r.child` on the BFS-assigned tree.
  3. `genRowMemForest_wf_OK` (`:830`) discharges one row's forest from those, for an
     arbitrary-length request list.
  4. `genMemForestFromTree_of_rowOK` (`GenTierAMem.lean:686`) lifts the per-row obligation to the
     whole forest, for an arbitrary tree.

  The existing fixture results are literally this composition with step 1 instantiated at
  `mmTree_gen` or at the Tier A run, so generalizing costs nothing.

  Worth recording, because it is the opposite of the compute side: the memory obligations
  (`BindMemoryRow`, fan-out, timestamp specialization) are seed-**polynomial identities**, so they
  hold for every program and seed.  The three remaining compute-side obligations of
  `genComputeSkeleton_inTree_Vcomp` (`hdyck`, `hncol`, `hsz`) are seed-**non-vanishing** conditions,
  which is why they have no generic discharge.

  Scope: `∀ program accepted by genComputeSkeleton`, not `∀ E`.  This is `Data.memoryOK`'s
  obligation on generated forests; it discharges no other premise and moves no `§J` box.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenMatmulMem
import Nock.NockVMROM.Thm54.TraceGen.GenTierAMem

-- A missing import otherwise becomes a silent type variable rather than an error;
-- that cost real debugging time on this module family.
set_option autoImplicit false

namespace Nock.NockVMROM.Thm54.TraceGen

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.HonestCommitment

variable {K : Type} [Field K]

variable {lmb : K}

/-! ## The per-row obligation, generically -/

/-- Every row of an accepted program's BFS-assigned tree has a locally valid memory forest. -/
theorem genComputeSkeleton_bfsAssign_rowOK (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result))
    (n : NTree (GenComputeRow K)) (hn : InTree (bfsAssign t) n) :
    ∀ u ∈ genRowMemForest (encC z) z α lmb (extractNodeReqs n.label),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  genRowMemForest_wf_OK z α _
    (bfsAssign_extract_requests_wf t (genComputeSkeleton_tree_requests_wf h) n hn)

/-! ## The whole generated forest, generically -/

/-- **`MemoryNodesOK` at every root of the generated memory forest, for every program the
generator accepts.**

At `Data.memoryOK`'s obligation shape on the BFS-assigned tree.  Previously available only at
Tier A and matmul. -/
theorem genComputeSkeleton_memForest_OK (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign t),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  genMemForestFromTree_of_rowOK z α _ (genComputeSkeleton_bfsAssign_rowOK z α h)

/-- The same on the **AIR-ordered** tree, which is the order every live configuration commits.
`treeRequestsWF` survives the reordering by `treeRequestsWF_airReorder`. -/
theorem genComputeSkeleton_memForest_OK_air (z α : K)
    {fuel : ℕ} {subject formula : Noun}
    {t : NTree (GenComputeRow K)} {result : Noun}
    (h : genComputeSkeleton (K := K) fuel subject formula = .ok (t, result)) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (airReorder t)),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  genMemForestFromTree_of_rowOK z α _
    (fun n hn =>
      genRowMemForest_wf_OK z α _
        (bfsAssign_extract_requests_wf (airReorder t)
          (treeRequestsWF_airReorder (genComputeSkeleton_tree_requests_wf h)) n hn))

/-! ## Not provided: the unassigned tree

There is deliberately no variant for `genMemForestFromTree … t` on the *unassigned* tree.
`treeRequestsWF` is stated over `n.label.requests` (`ServiceReq`), while `genRowMemForest` consumes
`extractNodeReqs n.label` (`MemRecordReq`); bridging the two is exactly the work
`bfsAssign_extract_requests_wf` does via `bfsAssign_bfsForest_labels`, and it has no counterpart on
the unassigned tree.  `extractNodeReqsAux_mem` (`GenMatmulMem.lean:1211`) is the missing ingredient
if it is ever wanted.  No live configuration commits an unassigned forest, so it is not needed.

## Non-vacuity

Instantiated at the Tier A dot-product run -- a witness that the hypothesis is satisfiable at a real
program.

**Not** the forest `DotConfig769` commits: that is
`threadGenForest (memInputs z) 0 (genMemForestFromTree (encC z) z α (bfsAssign (dotTreeAir)))`
(`GenTierAMemAccept.lean:1026`), which differs on two counts -- the AIR-reordered tree rather than
the DFS one, and threaded rather than unthreaded.  Use `genComputeSkeleton_memForest_OK_air` plus
`MemoryNodesOK_threadGenForest` (`GenTierAHonestData.lean:120`) to reach the committed forest. -/

/-- The generic forest result applied to the Tier A program's DFS emission. -/
theorem genGenericMemory_nonvacuous (z α : K) :
    ∀ u ∈ genMemForestFromTree (encC z) z α lmb (bfsAssign (dotTree (K := K))),
      MemoryNodesOK z α (mapNTree GenMemoryRow.node u) :=
  genComputeSkeleton_memForest_OK z α (genComputeSkeleton_dot 0)

end Nock.NockVMROM.Thm54.TraceGen

#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_bfsAssign_rowOK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_memForest_OK
#print axioms Nock.NockVMROM.Thm54.TraceGen.genComputeSkeleton_memForest_OK_air
#print axioms Nock.NockVMROM.Thm54.TraceGen.genGenericMemory_nonvacuous
