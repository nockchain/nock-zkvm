/-
  Nock/RedTeam/Batch2165Thm54VSHonestTerminals.lean

  New module
  `HonestTermH`; additive.

  `hpubX_honest` (`yH = Σ 1/dX`), `hpubP_honest` (`Re ρ₄ = Σ mL/dL + mR/dR` from `ρ₄ = accSumP`),
  `hpubC_honest` (`Re ρ₃ + yH = Σ mh/den` from `ρ₃ = accSumX`, `mh = mhH2`).
-/
import Nock.NockVMROM.Thm54.VclL.Handle.HonestTermH

namespace Nock.RedTeam.Batch2165

open Nock.NockVMROM.Thm54.VclL.Handle.FrameVS

#print axioms accSumX_eq
#print axioms accSumP_eq
#print axioms hpubX_honest
#print axioms hpubP_honest
#print axioms hpubC_honest

end Nock.RedTeam.Batch2165
