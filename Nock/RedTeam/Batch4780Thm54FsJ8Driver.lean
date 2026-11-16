/-
  Nock/RedTeam/Batch4780Thm54FsJ8Driver.lean

  Kernel, structural:
  * `pub_before_first_squeeze`: in the transcript schedule every public field and every claim field is absorbed before
    the first squeeze (`chi` coins); the schedule has exactly two squeezes;
  * the squeeze index lists are exactly the `frameJ8.sampledAfter = 0 / 1` fibres, and partition the 19 coins;
  * the driver's column-round maps are `TraceJ8`'s `crC crM crW crJ crA`.
-/
import Nock.DriverJ8.DriverJ8
import Nock.Driver.Tip5Vectors
import Nock.NockVMROM.Thm54.VclL.Handle.TraceJ8

set_option autoImplicit false

namespace Nock.RedTeam.Batch4780

open Nock.DriverJ8.TranscriptJ8 Nock.DriverJ8.DriverJ8
open Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8

theorem idxS0_spec : ∀ i : Fin frameJ8.n, (i : ℕ) ∈ idxS0 ↔ frameJ8.sampledAfter i = 0 := by decide
theorem idxS1_spec : ∀ i : Fin frameJ8.n, (i : ℕ) ∈ idxS1 ↔ frameJ8.sampledAfter i = 1 := by decide
theorem idx_partition : (idxS0 ++ idxS1).Nodup ∧ (idxS0 ++ idxS1).length = frameJ8.n ∧
    ∀ i ∈ idxS0 ++ idxS1, i < frameJ8.n := by decide

theorem cr_X : ∀ j : Fin 123, TraceJ8.crC j = rX j := fun j => by simp [TraceJ8.crC, rX]
theorem cr_C : ∀ j : Fin 242, TraceJ8.crM j = rC j := fun j => by simp [TraceJ8.crM, rC]
theorem cr_W : ∀ j : Fin 166, TraceJ8.crW j = rW j := fun j => by simp [TraceJ8.crW, rW]
theorem cr_J : ∀ j : Fin 71, TraceJ8.crJ j = rJ j := fun j => by simp [TraceJ8.crJ, rJ]
theorem cr_A : ∀ j : Fin 349, TraceJ8.crA j = rA j := fun j => by simp [TraceJ8.crA, rA]

#print axioms pub_before_first_squeeze
#print axioms squeezes_of_sched
#print axioms idxS0_spec
#print axioms idxS1_spec
#print axioms idx_partition
#print axioms cr_X
#print axioms cr_C
#print axioms cr_W
#print axioms cr_J
#print axioms cr_A

end Nock.RedTeam.Batch4780
