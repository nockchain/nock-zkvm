/-
  Nock/RedTeam/Batch4551Thm54J8nv3aAbsentV.lean

  * `iff_NV_of_pos`: at `1 ≤ krootsV`, `AcceptsJ8V ↔ AcceptsJ8''''`; `probJ8V_present`: the J-8 bound (< 2^-155,
    `probJ8NV_final`'s binders) over `AcceptsJ8V` at present layouts.
  * The bound at `krootsV = 0` is not derived.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.AcceptsJ8V

namespace Nock.RedTeam.Batch4551

open Nock.NockVMROM.Thm54.VclL.Handle

#check @AcceptsJ8V.AWChipOK
#check @AcceptsJ8V.AcceptsJ8V
#check @AcceptsJ8V.probJ8V_present
#print axioms AcceptsJ8V.aw_present_of_pos
#print axioms AcceptsJ8V.aw_absent_iff
#print axioms AcceptsJ8V.toNV_of_pos
#print axioms AcceptsJ8V.ofNV
#print axioms AcceptsJ8V.iff_NV_of_pos
#print axioms AcceptsJ8V.absent_fxA
#print axioms AcceptsJ8V.absent_trV_free
#print axioms AcceptsJ8V.nV_pos
#print axioms AcceptsJ8V.axReqs_reads_V
#print axioms AcceptsJ8V.probJ8V_present

end Nock.RedTeam.Batch4551
