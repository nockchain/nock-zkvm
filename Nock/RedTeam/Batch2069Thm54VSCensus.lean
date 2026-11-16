/-
  Nock/RedTeam/Batch2069Thm54VSCensus.lean

  Additive.
  New module `Thm54/VclL/Handle/CensusVS.lean`:
  * `seedSpecVS` (coins `{2, 3}`), `zeroVS` (zero seed, weight 1);
  * `rowsVS` (round-0 cell rows from the B0 columns `< 129`), `rowsVS_const`, `rowsVS_at`;
  * `censusVS`: `tableCensusSummand` at `{2, 3}`, `dep = ∅`, skeleton `[s, f, e]`, fuel `claimFuel`,
    weight `pairCount (T + 3) · (2·claimFuel − 1)` (`censusVS_shape`);
  * `census_sub` (claim census ⊇ the plain table census at `fuelChip`), `census_good`;
  * `claim_handles_VS'`: outside `valSummand`, `zeroVS`, `censusVS`, every claim handle denotes its noun.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.CensusVS

namespace Nock.RedTeam.Batch2069

open Nock.NockVMROM.Thm54.VclL.Handle.CensusVS

#print axioms census_sub
#print axioms rowsVS_const
#print axioms mem_zeroVS
#print axioms mem_censusVS
#print axioms censusVS_shape
#print axioms rowsVS_at
#print axioms census_good
#print axioms claim_handles_VS'

end Nock.RedTeam.Batch2069
