/-
  Nock/RedTeam/Batch1851Thm54VclLHonestMemReq.lean

  **`honestReq` is `Σ den⁻¹` over the honest compute requests.**
  Production:
  `VclL/Chips/HonestMemReq.lean`.

  * `HonestVCL.req_eq`: for every accumulator `a`, `H.req χ a = Σ_{r ∈ reqRecs χ a} (compress ⟨γ′,ρ′⟩ r)⁻¹`
    (`vTot_eq`: bound cells; `xTot_sub_yTot_eq`: depth-1 lookups with side; `pTot_eq`: deep reads at their slot).
  * `HonestVCL.msg2_eq`: `honestMsg2 = Σ_{path edges} den⁻¹`.
  * `HonestVCL.export_side_balance` (deviation (d) of LD2p-M3): the cell table's per-side export provides
    (`xs0` / `xs1`) = the path chip's `pxKey` consumes + the shallow lookups.
  * Generic: `cell_vTotal`, `cell_xTotal`, `path_yTotal`, `path_pTotal`, `pRecOf_chain_last`.

  Labelled: (i) `pTot_eq` / `req_eq` take `hslot` (every deep read of the demand is a defined slot; an honest
  compute run supplies it); (ii) the regrouping is by `sum_count_nsmul` (nodup closure + counts), not through
  `genMemTable_validity_balanced` / `export_balanced` (which are the multiset forms of the same identities);
  (iii) the request records are the MEMORY-side keys of the compute requests; identifying them with the compute
  family's `honestReq` (LD2p-C) is the next item.
-/
import Nock.NockVMROM.Thm54.VclL.Chips.HonestMemReq
import Nock.NockVMROM.Thm54.P8Core.Batch1090Thm54C2ReadyFuel
import Nock.NockVMROM.Thm54.P8Core.PartAEvents12
import Nock.NockVMROM.Thm54.Unhosted309Events

namespace Nock.RedTeam.Batch1851

open Nock.NockVMROM.Thm54.VclL.Chips.ChipRAP

#print axioms sum_count_nsmul
#print axioms cell_vTotal
#print axioms cell_xTotal
#print axioms path_yTotal
#print axioms path_pTotal
#print axioms pRecOf_chain_last
#print axioms HonestVCL.vTot_eq
#print axioms HonestVCL.xTot_eq
#print axioms HonestVCL.yTot_eq
#print axioms HonestVCL.export_side_balance
#print axioms HonestVCL.xTot_sub_yTot_eq
#print axioms HonestVCL.pTot_eq
#print axioms HonestVCL.req_eq
#print axioms HonestVCL.msg2_eq

end Nock.RedTeam.Batch1851
