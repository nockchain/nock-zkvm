/-
  Nock/RedTeam/Batch1909Thm54TowerLookupHonest.lean

  **Lookup / ax / serial / accumulator gates at honest data.**
  Generic over named placement hypotheses.

  * `lookupGatesT_honest`: slot0/1/2 `Q.IsZero` at the honest inverse `(den')⁻¹`, one-hot state, under the
    named honestBad pole conditions (`den' ≠ 0` at the ACTIVE record).
  * `serialGates_honest` / `serialGates_honestQT`; `honest_axGates'` (leaf hypotheses conditional on the
    active state) / `honest_axImGates`.
  * `accGates_prefix`, `accGates_prefixK`, `accGatesT_honest`: the 36 accumulator gates at prefix sums.
  * `honestReqCF` (`0` at validity; `1`/`2` the closed form of `HonestVCL.req_eq`),
    `honestReqCF_eq_req`, `terminal_eq_closed`, `shallowSided_flatMap`, `deepFilter_flatMap`.
  * NCs: `slot1Q_wrong_inverse`, `serialStep_rejects_skip`, `accTerm_rejects_wrong_terminal`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.TowerLookupHonest
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.P8Core.SVWalk.ExpAlign
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1909

end Nock.RedTeam.Batch1909

open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms lookupGatesT_honest
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms slot1Q_wrong_inverse
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms serialGates_honest
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms serialGates_honestQT
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms serialStep_rejects_skip
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honest_axGates'
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honest_axImGates
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms accGates_prefix
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms accGatesT_honest
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms accTerm_rejects_wrong_terminal
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms honestReqCF_eq_req
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms terminal_eq_closed
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms shallowSided_flatMap
open Nock.NockVMROM.Thm54.VclL.Compute.TowerD in
#print axioms vclColT_imVcl
