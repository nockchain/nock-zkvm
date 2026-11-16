/-
  Nock/RedTeam/Batch196Thm54GenericRootsAtTierA.lean

  **`genRoots` instantiated at `DotConfig769`, and shown non-vacuous.**

  `TraceGen/GenServedRoots.lean` §C builds `ExactServedMemoryTrace.roots` for the generated
  carrier: a `RootTrace` at *every* forest index of `genExactExecution`, for any program
  `genComputeSkeleton` accepts.

  So this module discharges **every** hypothesis of `exists_rootTrace_gen` at Tier A
  (`GaloisField 769 3`, seed `φ(8)`, `α = φ(4)`, coins `(0,0,0)`, `Ksz = 64`) and then measures the
  result.  Three things are worth stating, because each is a way the exercise could have been
  hollow and is not:

  1. **The memory forest is Tier A's own.**  `genMemoryForest seedZ alphaA (memInputs seedZ) dotTree`
     is *definitionally* `threadGenForest (memInputs seedZ) 0 (assignedForest seedZ alphaA)`, i.e.
     `Batch167.tierAMemory` = `DotConfig769.threadedForest`, once `airReorder_dotTree` identifies
     the two orderings.  Nothing is rebuilt to fit.
  2. **The orbit-capacity hypothesis is real and it is met, not assumed away.**  `horb` is
     `accAt … < orderOf α`; at Tier A that is `≤ 24 < 192` (`Batch180.dot_accAt_le`,
     `Batch180.alphaA_order_eq_192`).  It is exactly the premise the chain builder's `hne` needs
     and cannot do without: `timestampExp α ·` sees only the field value, so at `α = 1` distinct
     exponents give the *same* term.
  3. **The witness carries records.**  There are ten forest roots, each built root carries one or
     two `Service`s, and therefore each root's `rootResponseRecords` is non-empty.  An opaque
     `Nonempty.some` would have given none of that.

  **Not claimed.**  `ExactServedMemoryTrace` is *not* assembled here: `roots` is one of its four
  fields and the other three (`timestampPowersNodup`, `forestIndexRange`, `semanticCoverage`) are
  not filled at the generated carrier.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenServedRoots
import Nock.RedTeam.Batch167Thm54GenericCarrierAtTierA
import Nock.RedTeam.Batch180Thm54GenericSemanticDataAtTierA

set_option autoImplicit false

namespace Nock.RedTeam.Batch196

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.ServedMemoryTrace
open Nock.NockVMROM.Thm54.TraceGen hiding seedZ alphaA
open Nock.NockVMROM.Thm54.TraceGen.DotConfig769
open Nock.Framework.Thm54

noncomputable section

/-- Tier A's table field. -/
abbrev DK := DotConfig769.K

/-- Tier A's base field. -/
abbrev DF := DotConfig769.F

/-! ## 1. The generated memory forest at Tier A's inputs IS Tier A's threaded forest

`genMemoryForest` threads `genMemForestFromTree … (bfsAssign (airReorder t))`;
`DotConfig769.threadedForest` threads `genMemForestFromTree … (bfsAssign dotTreeAir)`.
`airReorder_dotTree` is the only step. -/

theorem genMemoryForest_dot :
    genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK))
      = Batch167.tierAMemory := by
  unfold genMemoryForest Batch167.tierAMemory threadedForest assignedForest
  rw [airReorder_dotTree]

/-! ## 2. Every hypothesis of `exists_rootTrace_gen`, discharged -/

theorem b196_horb : 1 ≤ executionOrbit.h := by
  norm_num [executionOrbit]

theorem b196_mempos :
    0 < (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))).length := by
  rw [genMemoryForest_dot]; exact Batch167.tierA_mempos

theorem b196_comp_le :
    (bfsForest [genComputeRows seedZ alphaA (dotTree (K := DK))]).length
      ≤ 2 ^ executionOrbit.h := by
  rw [show genComputeRows seedZ alphaA (dotTree (K := DK)) = Batch167.tierACompute from by
    rw [genComputeRows, airReorder_dotTree]; rfl]
  exact Batch167.tierA_comp_le

theorem b196_mem_le :
    (bfsForest (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))).length
      ≤ 2 ^ executionOrbit.h := by
  rw [genMemoryForest_dot]; exact Batch167.tierA_mem_le

/-- **The orbit-capacity premise, met.**  `accAt ≤ 24` over eight rows at three records each, and
`orderOf alphaA = 192`.  This is the premise the chain builder's `hne` genuinely needs. -/
theorem b196_horbα :
    accAt (airReorder (dotTree (K := DK)))
        (bfsRows (airReorder (dotTree (K := DK)))).length < orderOf alphaA := by
  refine lt_of_le_of_lt Batch180.dot_accAt_le ?_
  rw [Batch180.alphaA_order_eq_192]
  norm_num

theorem b196_hz : (cfg seedZ alphaA).challenges.z = seedZ := rfl

theorem b196_hα : (cfg seedZ alphaA).challenges.α = alphaA := rfl

/-! ## 3. The generated carrier and its roots -/

/-- The generated configuration at Tier A's inputs, with Tier A's own committed memory forest. -/
def b196Cfg : ExactConfig DF DK :=
  genExactConfig (F := DF) (cfg seedZ alphaA).challenges 64 executionOrbit b196_horb
    (genComputeRows seedZ alphaA (dotTree (K := DK)))
    (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
    b196_mempos b196_comp_le b196_mem_le

def b196Exec : ExactExecution b196Cfg :=
  genExactExecutionA (F := DF) (cfg seedZ alphaA).challenges 64 executionOrbit b196_horb
    0 0 0 (genComputeRows seedZ alphaA (dotTree (K := DK)))
    (genMemoryForest seedZ alphaA MemoryTable.formRDefault (memInputs seedZ) (dotTree (K := DK)))
    b196_mempos b196_comp_le b196_mem_le

/-- **`roots`, at Tier A.**  Ten `RootTrace`s over the generated carrier. -/
def b196Roots : ∀ i : Fin b196Cfg.kMem, RootTrace b196Cfg b196Exec i :=
  genRoots (F := DF) seedZ alphaA 0 0 0 (cfg seedZ alphaA).challenges b196_hz b196_hα
    64 executionOrbit b196_horb (memInputs seedZ) (genComputeSkeleton_dot 0) b196_horbα
    b196_mempos b196_comp_le b196_mem_le

/-! ## 4. Not vacuous

Ten roots; each carries one or two services; each root therefore emits at least one `read_root`
record.  `RootTrace`'s `recordPartition` is what turns the second into the third. -/

/-- Ten forest roots — Tier A's own count (`DotConfig769.cfg.kMem = 10`). -/
theorem b196_kMem : b196Cfg.kMem = 10 := by
  rw [b196Cfg, genExactConfig_kMem, genMemoryForest_dot]
  exact Batch167.tierA_kMem

theorem b196_roots_services (i : Fin b196Cfg.kMem) :
    (b196Roots i).services.length = 1 ∨ (b196Roots i).services.length = 2 :=
  genRoots_services_length (F := DF) seedZ alphaA 0 0 0 (cfg seedZ alphaA).challenges
    b196_hz b196_hα 64 executionOrbit b196_horb (memInputs seedZ)
    (genComputeSkeleton_dot 0) b196_horbα b196_mempos b196_comp_le b196_mem_le i

/-- **Each root serves a record.**  This is the non-vacuity claim: an opaque choice would give
`services = []` and no served record at all. -/
theorem b196_roots_records (i : Fin b196Cfg.kMem) :
    rootResponseRecords b196Exec i ≠ [] :=
  genRoots_rootResponseRecords_ne_nil (F := DF) seedZ alphaA 0 0 0
    (cfg seedZ alphaA).challenges b196_hz b196_hα 64 executionOrbit b196_horb (memInputs seedZ)
    (genComputeSkeleton_dot 0) b196_horbα b196_mempos b196_comp_le b196_mem_le i

/-- **And each root's timestamp multiset is the classified tree's own.**  Either the one-record
shape `[α ^ e]` or the chained shape `[α ^ e₁, α ^ e₂]`, at the tree the classification named. -/
theorem b196_roots_timestampPowers (i : Fin b196Cfg.kMem) :
    (∃ r : MemRecordReq,
        (genMemForestFromTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
            (bfsAssign (airReorder (dotTree (K := DK)))))[(i : ℕ)]'
          (genRoot_index_lt (F := DF) seedZ alphaA (memInputs seedZ) (dotTree (K := DK))
            (cfg seedZ alphaA).challenges 64 executionOrbit b196_horb
            b196_mempos b196_comp_le b196_mem_le i)
            = genAnnotatedRecordTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
                r.root r.child r.axis r.recordExp ∧
        (b196Roots i).timestampPowers = [alphaA ^ r.recordExp]) ∨
      (∃ r1 r2 : MemRecordReq,
        genAnnotatedChainedTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault [r1, r2] =
            some ((genMemForestFromTree (encC seedZ) seedZ alphaA MemoryTable.formRDefault
              (bfsAssign (airReorder (dotTree (K := DK)))))[(i : ℕ)]'
              (genRoot_index_lt (F := DF) seedZ alphaA (memInputs seedZ) (dotTree (K := DK))
                (cfg seedZ alphaA).challenges 64 executionOrbit b196_horb
                b196_mempos b196_comp_le b196_mem_le i)) ∧
        (b196Roots i).timestampPowers = [alphaA ^ r1.recordExp, alphaA ^ r2.recordExp]) :=
  genRoots_timestampPowers (F := DF) seedZ alphaA 0 0 0 (cfg seedZ alphaA).challenges
    b196_hz b196_hα 64 executionOrbit b196_horb (memInputs seedZ)
    (genComputeSkeleton_dot 0) b196_horbα b196_mempos b196_comp_le b196_mem_le i

end

end Nock.RedTeam.Batch196

#print axioms Nock.RedTeam.Batch196.genMemoryForest_dot
#print axioms Nock.RedTeam.Batch196.b196_horbα
#print axioms Nock.RedTeam.Batch196.b196Roots
#print axioms Nock.RedTeam.Batch196.b196_kMem
#print axioms Nock.RedTeam.Batch196.b196_roots_services
#print axioms Nock.RedTeam.Batch196.b196_roots_records
#print axioms Nock.RedTeam.Batch196.b196_roots_timestampPowers
