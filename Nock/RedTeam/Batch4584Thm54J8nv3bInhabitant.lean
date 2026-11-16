/-
  Nock/RedTeam/Batch4584Thm54J8nv3bInhabitant.lean

  **4583 (`Handle/InhabJ8Base`, `InhabJ8Static`,
  `InhabJ8Comp`, `InhabJ8MemDom`, `InhabJ8MemCell`, `InhabJ8MemCellKW`, `InhabJ8MemWalk`, `InhabJ8MemMain`,
  `InhabJ8AtomCell`, `InhabJ8AtomChip`, `InhabJ8AtomDen`, `InhabJ8Atom`, `InhabJ8Main`).**  THE INHABITANT of the
  verifier predicate `AcceptsJ8V` (NV3a) for the TRUE claim `*[[0 0] [0 1]] = [0 0]` at Goldilocks: empty registry
  (J chip absent, `nJ = 0`), no big atoms (atom walk absent, `krootsV = 0`), atom table = one inert pad row, cell
  table `[0 0], [0 1]`, one compute row, one J-8 walk dummy root, coin `χ0` (every `√δ`-coordinate `0` except the
  two LogUp poles').  Every conjunct is proved from the per-chip honest theorems
  (`computeChipVCLHX_honest_sat_tree`, `cellChipHQKW_accepts_honest`, `walkTwinJ8_accepted`,
  `atomChipHQL_accepts_honest_pad`) and the cross-chip balances (`hGx0`, `hGp0`, `claimSum0`, `hfxC0`).
  NOT claimed: a staged trace map (`StJ8`) through the honest traces; the inhabitant is at one coin.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.InhabJ8Main

namespace Nock.RedTeam.Batch4584

open Nock.NockVMROM.Thm54.VclL.Handle

#check @InhabJ8Main.inhabitant
#check @InhabJ8Main.inhabitant_goldilocks
#print axioms InhabJ8Main.inhabitant
#print axioms InhabJ8Main.inhabitant_goldilocks
#print axioms InhabJ8Main.hGx0
#print axioms InhabJ8Main.coinsA0
#print axioms InhabJ8Comp.hsatX_c0_qX
#print axioms InhabJ8MemMain.memC_sat_simple
#print axioms InhabJ8MemMain.memW_sat_simple
#print axioms InhabJ8MemMain.claimSum0
#print axioms InhabJ8MemMain.hfxC0
#print axioms InhabJ8Atom.hsatL_A0
#print axioms InhabJ8Atom.hsatA_A0
#print axioms InhabJ8Static.hbud0

end Nock.RedTeam.Batch4584
