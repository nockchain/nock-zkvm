/-
  Nock/RedTeam/Batch1916Thm54TowerAxHonest.lean

  **Item 5, the axis-gate leaf hypotheses at generated rows.**

  * `honest_ax_gen`: `honest_axGates'` and `honest_axImGates` at the honest trace row, from the row being
    `genRowVals`, the atom-fingerprint shape of `f_t` (OP0) / `f_th` (OP9), and `vcl 221 = a`.
  * `gen_ax_dec`: that shape at a generator node (`NodeAxisInFormula`), the axis being `honestAx`.
  * `honest_ax_of_gen`: the combination (honest fill `vcl 221 = honestAx skel`).
  * NC (discriminating): `nc_ax_off_by_one`: an axis column off by one fails the axis gate.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerAxHonest
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.TraceGen.GenFormRAxisLambda

set_option autoImplicit false

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honest_ax_gen
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms gen_ax_dec
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honest_ax_of_gen
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms nc_ax_off_by_one
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms firstReads_of_fill
