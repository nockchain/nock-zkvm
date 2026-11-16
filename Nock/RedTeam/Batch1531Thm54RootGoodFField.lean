/-
  Nock/RedTeam/Batch1531Thm54RootGoodFField.lean

  **`root_goodF` at the field join.**

  Receipts:
  * §A `#print axioms` of every step lemma, the induction and the root theorems.
  * `root_goodF` / `root_holdsF` /
    `good_of_inpW` reach none of `HonestCall`, `evalGBy`, `honestCall_kid`, `honestCall_inputs_le`,
    `c2_aligned_genuine`, `c2_aligned_eval`, `Batch1171.Inp`, `Ctx.hΛG`, `programLeafBound`,
    `genComputeSkeleton`; positive control `Batch1171.root_good`.
  * §C the statement of `root_goodF` and the window premise `CallsWithin` (`#check`).
-/
import Nock.NockVMROM.Thm54.P8Core.RootGoodFJoin
import Nock.RedTeam.Batch1530Thm54RootGoodFDayOne

set_option autoImplicit false

namespace Nock.RedTeam.Batch1531

/-! ## §A  Axioms -/

#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.slot0W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.head_atomW
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.tail_bind2W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.tail_bind3W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.kidRun
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.kidWin
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.kidBounded
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s0W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s1W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s2W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s3W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s4W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s5W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s6W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s7W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s8W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_s9W
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.step_consW
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.good_of_inpW
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.root_goodF
#print axioms Nock.NockVMROM.Thm54.RootGoodFJoin.root_holdsF

/-! ## §B  Honest-free -/

#assertHonestFree Nock.NockVMROM.Thm54.RootGoodFJoin.root_goodF
#assertHonestFree Nock.NockVMROM.Thm54.RootGoodFJoin.root_holdsF
#assertHonestFree Nock.NockVMROM.Thm54.RootGoodFJoin.good_of_inpW
#assertHonestFree Nock.NockVMROM.Thm54.RootGoodFJoin.CtxW
#assertHonestFree Nock.NockVMROM.Thm54.RootGoodFJoin.InpW
#assertHonestReached Nock.RedTeam.Batch1171.root_good

/-! ## §C  Statements -/

#check @Nock.NockVMROM.Thm54.RootGoodFJoin.CallsWithin
#check @Nock.NockVMROM.Thm54.RootGoodFJoin.root_goodF
#check @Nock.NockVMROM.Thm54.RootGoodFJoin.root_holdsF

end Nock.RedTeam.Batch1531
