/-
  Nock/RedTeam/Batch260Thm54LineAdvanceAtBroadProgram.lean

  **The generic line-number supplier, instantiated at the broad program — and measured.**

  So this module does not build a supplier.  It does the thing the supplier had never had done to
  it: instantiate it at a live configuration and check the witness is not vacuous.

  **The configuration is the broad program**, not Tier A — `Batch231`'s seventeen-row, eight-state
  program over `GaloisField 769 3`, seed `φ(8)`, `α = φ(4)`, coins `(0, 0, 1)`, `Ksz = 64`,
  `orbit.h = 8`.  Tier A has four states and no `.s0`/`.s5`/`cons` row; the broad program has
  `{cons, s0, s1, s3, s4, s5, s7, s8}`, so the one-hot `α^{1,2,3}` selection of
  the paper is exercised at all three of its classes rather than at one.

  **Three non-vacuity measurements, each read off the instantiated object:**

  * `b260_computeStamps_length = 17` and `b260_memoryStamps_length = 227` — the two `Forall₂`s are
    over seventeen and two hundred twenty-seven real conjuncts, not `Forall₂ [] []`.
  * `b260_lineAdvances` — at **every one** of the seventeen compute rows, `ln ≠ ln_prev`.  A
    relative recurrence with a zero exponent gap would read `ln = ln_prev · α^0 = ln_prev` and
    assert nothing; here `α^recordCount ≠ 1` because `orderOf α = 192 > 3 ≥ recordCount`.
  * `b260_specializesAt` — the whole `TimestampSpecializesAt`, both tables and both bridge
    equations, as a term at this configuration.

  **Scope.**  One configuration, one program.  Nothing here is a capstone: `Data`, `Inputs`,
  `buildFullPackage` and the mandatory `claimedResult = result` conjunct are untouched, no §J box
  moves, and no `redteam-status.json` `status` is flipped.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenLineAdvance
import Nock.RedTeam.Batch231Thm54BroadProgramSemanticData

set_option autoImplicit false
set_option maxRecDepth 40000

namespace Nock.RedTeam.Batch260

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy

abbrev DK := Batch231.DK
abbrev DF := Batch231.DF

/-! ## The two arithmetic facts about `α` -/

/-- `α = φ(4)` is nonzero: it has finite order `192`, and `0` has no finite order. -/
theorem b260_alphaA_ne_zero : (DotConfig769.alphaA : DK) ≠ 0 := by
  intro h
  have h1 : (DotConfig769.alphaA : DK) ^ orderOf (DotConfig769.alphaA : DK) = 1 :=
    pow_orderOf_eq_one _
  rw [Batch180.alphaA_order_eq_192, h] at h1
  simp at h1

/-- `3 < orderOf α`, the only orbit condition the line-advance measurement needs. -/
theorem b260_hord : Nock.NockVM.mem_record_arity < orderOf (DotConfig769.alphaA : DK) := by
  rw [Batch180.alphaA_order_eq_192]
  decide

/-! ## The supplier, instantiated -/

/-- The carrier this module measures: `Batch231`'s config/execution at the broad program. -/
noncomputable abbrev b260Exec :=
  genExactExecution (F := DF) Batch231.bpChal 64 DotConfig769.executionOrbit
    (by norm_num [DotConfig769.executionOrbit]) 0 0 1
    (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (bpTree (K := DK)))
    (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
      (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem

/-- **`genComputeTimestamps` at the broad program** — the relative recurrence
`ln = ln_prev · α^(lnExponent − lnPrevExponent)` at all seventeen rows. -/
theorem b260_computeTimestamps :
    List.Forall₂ (ComputeTimestampSpecializesAt (DotConfig769.alphaA : DK))
      (bfsStamps (bfsAssign (airReorder (bpTree (K := DK)))))
      b260Exec.computeRows :=
  genComputeTimestamps (F := DF) Batch231.bpChal 64 DotConfig769.executionOrbit
    (by norm_num [DotConfig769.executionOrbit])
    DotConfig769.seedZ DotConfig769.alphaA 0 0 1 (bpTree (K := DK)) _
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem

/-- **`genMemoryTimestamps` at the broad program.** -/
theorem b260_memoryTimestamps :
    List.Forall₂ (MemoryTimestampSpecializesAt (DotConfig769.alphaA : DK))
      (genMemoryStamps (genMemForestFromTree (encC DotConfig769.seedZ) DotConfig769.seedZ
        DotConfig769.alphaA MemoryTable.formRDefault (bfsAssign (airReorder (bpTree (K := DK))))))
      b260Exec.memoryRows :=
  genMemoryTimestamps (F := DF) Batch231.bpChal 64 DotConfig769.executionOrbit
    (by norm_num [DotConfig769.executionOrbit])
    DotConfig769.seedZ DotConfig769.alphaA 0 0 1 (genComputeSkeleton_bp 0)
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem

/-- **`TimestampSpecializesAt` at the broad program** — both tables and both bridge equations. -/
theorem b260_specializesAt :
    TimestampSpecializesAt DotConfig769.seedZ DotConfig769.alphaA
      (genTimestampSkeleton DF (airReorder (bpTree (K := DK)))
        (genMemForestFromTree (encC DotConfig769.seedZ) DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (bfsAssign (airReorder (bpTree (K := DK)))))
        (genComputeSkeleton_memForest_stampsWellFormed DotConfig769.seedZ DotConfig769.alphaA
          (genComputeSkeleton_bp 0)))
      (genExactConfig (F := DF) Batch231.bpChal 64 DotConfig769.executionOrbit
        (by norm_num [DotConfig769.executionOrbit])
        (genComputeRows DotConfig769.seedZ DotConfig769.alphaA (bpTree (K := DK)))
        (genMemoryForest DotConfig769.seedZ DotConfig769.alphaA MemoryTable.formRDefault
          (memInputs DotConfig769.seedZ) (bpTree (K := DK)))
        Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem)
      b260Exec :=
  genSpecializesAt (F := DF) DotConfig769.seedZ DotConfig769.alphaA
    DotConfig769.seedZ_ne_zero Batch231.bpChal
    (congrArg ComputeTable.Inputs.z Batch231.bp_hinp) rfl
    64 DotConfig769.executionOrbit (by norm_num [DotConfig769.executionOrbit]) 0 0 1
    (genComputeSkeleton_bp 0)
    Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem

/-! ## Non-vacuity, measured on the instantiated objects -/

/-- Seventeen compute conjuncts, not zero. -/
theorem b260_computeStamps_length :
    (bfsStamps (bfsAssign (airReorder (bpTree (K := DK))))).length = 17 := by
  rw [b260_computeTimestamps.length_eq, ExactExecution.computeRows_length]
  exact Batch231.bp_genComputeRows_len _ _

/-- Two hundred twenty-seven memory conjuncts, not zero. -/
theorem b260_memoryStamps_length :
    (genMemoryStamps (genMemForestFromTree (encC DotConfig769.seedZ) DotConfig769.seedZ
      DotConfig769.alphaA MemoryTable.formRDefault (bfsAssign (airReorder (bpTree (K := DK)))))).length = 227 := by
  rw [b260_memoryTimestamps.length_eq, ExactExecution.memoryRows_length]
  exact bp_memRowsLen _ _ _

/-- **Every compute row of the broad program moves the line number.**  So the relative recurrence
is not the degenerate `ln = ln_prev · α^0`. -/
theorem b260_lineAdvances :
    List.Forall₂ (fun _ (row : ComputeTable.State × ComputeTable.DTcomp DK) =>
        row.2.2.1.ln ≠ row.2.2.1.ln_prev)
      (bfsStamps (bfsAssign (airReorder (bpTree (K := DK)))))
      b260Exec.computeRows :=
  genComputeLineAdvances (F := DF) Batch231.bpChal 64 DotConfig769.executionOrbit
    (by norm_num [DotConfig769.executionOrbit])
    DotConfig769.seedZ DotConfig769.alphaA 0 0 1 b260_alphaA_ne_zero b260_hord
    (bpTree (K := DK)) _ Batch231.bp_hmempos Batch231.bp_hcomp Batch231.bp_hmem

/-- The advance list is the seventeen-row one, so `b260_lineAdvances` is neither `Forall₂ [] []`
nor a statement about one row. -/
theorem b260_lineAdvances_length :
    b260Exec.computeRows.length = 17 := by
  rw [← b260_lineAdvances.length_eq]
  exact b260_computeStamps_length

end Nock.RedTeam.Batch260

#print axioms Nock.RedTeam.Batch260.b260_alphaA_ne_zero
#print axioms Nock.RedTeam.Batch260.b260_computeTimestamps
#print axioms Nock.RedTeam.Batch260.b260_memoryTimestamps
#print axioms Nock.RedTeam.Batch260.b260_specializesAt
#print axioms Nock.RedTeam.Batch260.b260_computeStamps_length
#print axioms Nock.RedTeam.Batch260.b260_memoryStamps_length
#print axioms Nock.RedTeam.Batch260.b260_lineAdvances
#print axioms Nock.RedTeam.Batch260.b260_lineAdvances_length
