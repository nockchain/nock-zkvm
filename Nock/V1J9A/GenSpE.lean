/-
  Nock/V1J9A/GenSpE.lean

  Mirrors `ComplJ9ASplitH` (`baseS`, `d2`, `d3`, `rowT`, `accS`, `qv`, `roleV`, `colS`) at `ZMod P` / `K6`:
  * `vSE = splitVals9` (the field axis atoms), `mSE` = `mSA`'s formula (axis-chain keys + `s10B` rows),
  * base columns `0 .. 71` = `baseS`, `𝕂′` roles `72 .. 89` = `inv2, inv3, acc` (inclusive prefix sum of
    `mS · (inv2 + inv3)`) at the handle coins `γHE / ρHE`,
  * publics `0 / 1` = Re / Im of the terminal (`pubSPs`).
  Evidence class: executable (`#eval`); no theorem here.
-/
import Nock.V1J8.GenAtom
import Nock.NockVMROM.Thm54.VclL.Handle.SplitChipJ9
import Nock.NockVMROM.Thm54.VclL.Handle.J9A.ComplJ9AChainsRun

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace Nock.V1J9A.GenSpE

open Nock Nock.Field Nock.TraceGenExe Nock.V1J8 Nock.V1J8.Exe Nock.V1J8.Check Nock.V1J8.Gen Nock.V1J8.FillMem
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.VclL.Handle Nock.NockVMROM.Thm54.VclL.Handle.FrameJ8
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AGen (LX9 ChipSt9)
open Nock.NockVMROM.Thm54.VclL.Handle.ComplJ9AChainsRun (axKeys9 splitVals9)

/-- The split values: the field axis atoms (`splitVals9`). -/
def vSE (rows9 : Array LX9) : List ℕ := splitVals9 P rows9

/-- The split multiplicities (`mSA`'s formula): axis chains on the value plus `s10B` rows on it. -/
def mSE (rows9 : Array LX9) (vS : List ℕ) : List ℕ :=
  vS.map fun v =>
    ((axKeys9 rows9).filter (·.2 = v)).length +
      (rows9.toList.filter fun l => l.chip = ChipSt9.s10B ∧ l.n = v).length

/-- Bit `j` of `v` as a field element. -/
def bitE (v j : ℕ) : ZMod P := if v.testBit j then 1 else 0

/-- Base column `c` of row `i` (`ComplJ9ASplitH.baseS`), `n` the row count, `nA` the atom-row count. -/
def baseSE (nA n : ℕ) (vS mS : List ℕ) (c i : ℕ) : ZMod P :=
  let v := vS.getD i 0
  if c = 0 then (if i = 0 then 1 else 0)
  else if c = 1 then (if i = n - 1 then 1 else 0)
  else if c = 2 then (i : ZMod P)
  else if c = 3 then ((nA + i : ℕ) : ZMod P)
  else if c = 4 then ((v / 2 ^ 32 : ℕ) : ZMod P)
  else if c = 5 then ((v % 2 ^ 32 : ℕ) : ZMod P)
  else if c < 70 then bitE v (c - 6)
  else if c = 70 then (((v / 2 ^ 32 : ℕ) : ZMod P))⁻¹
  else ((mS.getD i 0 : ℕ) : ZMod P)

/-- The key denominator of `(id, tag, 0, limb)` at the handle coins: `ρH + RLC^γH`. -/
def dKeyE (χe : CoinsE) (id tag limb : ℕ) : K6 :=
  compressE (γHE χe) (ρHE χe) ![lq id, lq tag, 0, lq limb]

/-- `d2` (`(nA + i, 2, 0, lo)`) and `d3` (`(nA + i, 3, 0, hi)`) of row `i`. -/
def d2E (χe : CoinsE) (nA : ℕ) (v i : ℕ) : K6 := dKeyE χe (nA + i) 2 (v % 2 ^ 32)
def d3E (χe : CoinsE) (nA : ℕ) (v i : ℕ) : K6 := dKeyE χe (nA + i) 3 (v / 2 ^ 32)

/-- The row term `mS · (inv2 + inv3)`. -/
def rowTE (χe : CoinsE) (nA : ℕ) (v m i : ℕ) : K6 :=
  lq m * ((d2E χe nA v i)⁻¹ + (d3E χe nA v i)⁻¹)

/-- The inclusive prefix sums `accS`. -/
def accSE (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ) : List K6 :=
  scanK6 ((List.range vS.length).map fun i => rowTE χe nA (vS.getD i 0) (mS.getD i 0) i)

/-- **The split table** (90 columns) and its publics (`0 / 1` = Re / Im of the terminal).
Row count `vS.length` (callers guard the empty case with `zeroChip 90`). -/
def spGenE (χe : CoinsE) (nA : ℕ) (vS mS : List ℕ) : Array (Array (ZMod P)) × (ℕ → K3) :=
  let n := vS.length
  let acc := accSE χe nA vS mS
  let tbl := (List.range n).map fun i =>
    let v := vS.getD i 0
    let r6 : List K6 := [(d2E χe nA v i)⁻¹, (d3E χe nA v i)⁻¹, acc.getD i 0]
    let roles : ℕ → K3 := fun t => let w := r6.getD (t / 2) 0; if t % 2 = 0 then w.re else w.im
    Array.ofFn (n := 90) fun c =>
      if c.val < 72 then baseSE nA n vS mS c.val i else limbZ (roles ((c.val - 72) / 3)) ((c.val - 72) % 3)
  let T := lastK6 acc
  (tbl.toArray, fun j => if j = 0 then T.re else if j = 1 then T.im else 0)

end Nock.V1J9A.GenSpE
