/-
  Nock/RedTeam/Batch1808Thm54VclLSideSlot.lean

  Production `Thm54/VclL/Compute/ChipQ7S.lean`: slot 0's
  denominator `+ gamma^10 * 1` (`denVecS`, `slot0S_sound`), slots 1/2 side 0 (unchanged);
  `computeChipVCLQ7S` (tuple (3, 232, 321, 4, 2)); `recX11`; `exportReqFactsQ7S` at m = 11;
  `RowFactsQ7.of_satS` (WalkSatQ7 transfers); `recX11_view` at `RV.recordViewVCL`; NC `side_term_ne`.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.ChipQ7S
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.P8Core.SVCompute.QueueTwins
import Nock.NockVMROM.Thm54.Unhosted309Events

set_option autoImplicit false

namespace Nock.RedTeam.Batch1808

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms compress_snoc
#print axioms side_term_ne
#print axioms slot0S_sound
#print axioms vclGatesQ7S_degree
#print axioms vclRAPQ7S_fingerprint
#print axioms computeChipVCLQ7S_sat_iff
#print axioms VclSourceObligationsQ7.of_vclGatesQ7S
#print axioms export_invQ7S
#print axioms exportReqFactsQ7S
#print axioms pathReqFactsQ7S
#print axioms acceptedRowsQ7S_of_sat
#print axioms recX11_view
#print axioms WalkQ7.RowFactsQ7.of_satS

end Nock.RedTeam.Batch1808
