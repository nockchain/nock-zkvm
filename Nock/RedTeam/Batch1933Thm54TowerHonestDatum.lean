/-
  Nock/RedTeam/Batch1933Thm54TowerHonestDatum.lean

  **The honest datum of the tower compute family, `GoodCFT` at the
  honest verifier datum, and `honest_staged`.**

  * `walkSat_closed`: the closed forms of `Walk.walkSat_exists` satisfy `WalkSat` (explicit, no choice);
    `honestWalkOf` / `walkT`: the explicit honest walk at `(α, γ) = (ι χ₀, ι χ₁)` over the generator's tree.
  * `goodCFT_honest`: `GoodCFT` at a datum with nodes `ω^i` (first `N` orbit points), `N ≤ 2^h`,
    `25 ≤ char F`, `3N < char K`, `ρ 0 = 0` (adjacency, injectivity, `hchar`, `N ≤ char`).
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerHonestT
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda
import Nock.NockVMROM.Thm54.TraceGen.GenGoodSeedExists
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL

namespace Nock.RedTeam.Batch1933
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD

#print axioms walkSat_closed
#print axioms goodCFT_honest
#print axioms hchar_of_hp
#print axioms injective_of_pow
#print axioms vclColT_congr_le1
#print axioms rowsT_ext_lt
#print axioms walkT_state
#print axioms honest_staged_T

end Nock.RedTeam.Batch1933
