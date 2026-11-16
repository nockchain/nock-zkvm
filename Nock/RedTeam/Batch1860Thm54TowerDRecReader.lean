/-
  Nock/RedTeam/Batch1860Thm54TowerDRecReader.lean

  **Record readers over an interface; node_records over (gather, reader).**
  `RecReader G K` (RecReaderQ7): the
  export / path records, activity flags, and the laws the node-records chain uses (roots/children are the
  decoded fingerprints of the gathered pull-back; shared-view key/axis clauses).  Instances: `recReaderOfBasis`
  (3-limb, laws by rfl / existing lemmas) and `TowerD.towerReader` (recXQ/recPQ/actXQ/actPQ, laws from
  TowerRecs; `natLift_algebraMap_eq` via `ringChar_quad`).  NodeRecQ7: `row_records_Q7G`, `node_records_Q7G`
  (acceptance facts as interface hypotheses); `row_records_Q7` / `node_records_Q7` are their `ofBasis`
  corollaries, statements unchanged.
-/
import Nock.NockVMROM.Thm54.VclL.Compute.CompSoundnessVCL
import Nock.NockVMROM.Thm54.VclL.Compute.TowerReader

set_option autoImplicit false

namespace Nock.RedTeam.Batch1860
end Nock.RedTeam.Batch1860

open Nock.NockVMROM.Thm54.VclL.Compute

#print axioms recReaderOfBasis
#print axioms TowerD.towerReader
#print axioms TowerD.natLift_algebraMap_eq
#print axioms NodeRecQ7.label_vcompG
#print axioms NodeRecQ7.row_records_Q7G
#print axioms NodeRecQ7.node_records_Q7G
#print axioms NodeRecQ7.row_records_Q7
#print axioms NodeRecQ7.node_records_Q7
#print axioms CoreQ7.rowFacts_Q7
#print axioms CompSoundnessVCL.compSoundnessVCL
