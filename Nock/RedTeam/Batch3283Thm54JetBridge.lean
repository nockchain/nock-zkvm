/-
  Nock/RedTeam/Batch3283Thm54JetBridge.lean

  * finding: `oldRegKey_recOK` / `oldValKey_recOK` (J-3b's tag-first in-chip keys ARE `walkRecA` /
    inc records of the merged service balance), `newKeys_recOK` (the fix carries no obligation);
  * `base_row`, `slot_val`, `jet_telescope`, `jet_tagged_sum`, `jet_export_sum`;
  * `bal_of_service`, `accepted_of_sat`, `accepted_of_service` (J chip RAP → J-3b `Accepted`);
  * `jetProvOK`, `jetProvOK_of_sat`, `rd_recOK`.
-/
import Nock.Jet.RapJetJ8

namespace Nock.RedTeam.Batch3283

open Nock.Jet.ChipJ8 Nock.Jet.RapJetJ8

#print axioms jetTemplateJ8T_width
#print axioms gatesJT_degree
#print axioms gatesJT_keyOK
#print axioms jetChipJ8_width
#print axioms oldRegKey_recOK
#print axioms oldValKey_recOK
#print axioms newKeys_recOK
#print axioms base_row
#print axioms slot_val
#print axioms jet_telescope
#print axioms jet_tagged_sum
#print axioms jet_export_sum
#print axioms bal_of_service
#print axioms accepted_of_sat
#print axioms accepted_of_service
#print axioms jetProvOK
#print axioms jetProvOK_of_sat
#print axioms rd_recOK

end Nock.RedTeam.Batch3283
