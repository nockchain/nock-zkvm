/-
  Nock/RedTeam/Batch4755Thm54TgJ8Gen.lean

  The generator runs `genX` and fills every chip from the run; this receipt pins its first stage at the
  example `*[[0 0] [0 1]]`: the run is the inhabitant's one-row tree, its cell list is `[s0, f0]`, its handle map
  is the inhabitant's `H0`.  Native verdicts (example / toys / add / dec) are not
  kernel-checked here.
-/
import Nock.V1J8.GenJ8
import Nock.TraceGenExe.Syntax
import Nock.TraceGenExe.Demos

namespace Nock.RedTeam.Batch4755

open Nock Nock.V1J8.Gen Nock.Edit Nock.Edit.GenX
open Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Base (s0 f0 c0 t0 R0 gen0)
open Nock.NockVMROM.Thm54.VclL.Handle

theorem run_example :
    runX R0 1 s0 f0 = some ⟨t0, s0, [t0], #[InhabJ8Comp.r0]⟩ := by
  simp only [runX, gen0, InhabJ8Comp.bfs0]
  rfl

theorem cells_example : cellsOfRoots (rootsOf c0 #[InhabJ8Comp.r0]) = [s0, f0] := by decide

theorem hdl_example : V1J8.Gen.hdl [s0, f0] = InhabJ8MemDom.H0 Nock.Field.p := by
  funext n
  cases n with
  | atom v => rfl
  | cell a b =>
    show (1, idxOf [s0, f0] (.cell a b)) = (1, if Noun.cell a b = f0 then 1 else 0)
    by_cases h1 : Noun.cell a b = f0
    · rw [h1]; decide
    · by_cases h0 : Noun.cell a b = s0
      · rw [h0]; decide
      · have hm : Noun.cell a b ∉ [s0, f0] := by simp [h0, h1]
        simp [idxOf, hm, h1]

#print axioms run_example
#print axioms cells_example
#print axioms hdl_example

end Nock.RedTeam.Batch4755
