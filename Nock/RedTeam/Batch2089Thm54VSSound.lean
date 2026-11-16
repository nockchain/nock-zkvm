/-
  Nock/RedTeam/Batch2089Thm54VSSound.lean

  **3: the compute-walk
  summands, the VS summand lists, `hsound` and `StandaloneG` at VS.**  Additive.  New module
  `Thm54/VclL/Handle/SoundVS.lean`:
  * `cwalkVS` (coins `{13, 14}`, `dep = ∅`, `cwEvent` of `rowsC`, weight `|𝕂|·6N`) and `ctileVS`
    (coin `{13}`, `dep = ∅`, the `α`-tiling set, weight `2N + 2`);
  * `sumCVS = [cwalkVS, ctileVS]`, `sumMVS = [dyckVS, walkChainVS, fpExportIOVS]`,
    `jointVS = [zeroVS, censusVS, valSummand, ioSummandHX, ioSummandHP]`;
  * **`hsoundVS`**: `V.Checks → AcceptsG → outside allSummandsG → HoldsF (ringChar K) V.claim`;
  * **`standaloneVS_sound`**: `StandaloneG (compCoreVS … sumCVS) (memCoreVS … sumMVS) jointVS`
    via `standaloneG_of_sound` (completeness vacuous: `Honest := Empty`).
  No hypothesis on accumulator 2 (`ρ₂`) is used: `GoodCVS` constrains `ρ₀`, `ρ₁`, `Im ρ₃`, `Im ρ₄`
  only, and `hsoundVS` takes nothing else about `msg.requests`.
-/
import Nock.NockVMROM.Thm54.VclL.Handle.SoundVS

namespace Nock.RedTeam.Batch2089

open Nock.NockVMROM.Thm54.VclL.Handle.SoundVS

#print axioms rowsC_staged
#print axioms mem_cwalkVS
#print axioms mem_ctileVS
#print axioms hsoundVS
#print axioms standaloneVS_sound

end Nock.RedTeam.Batch2089
