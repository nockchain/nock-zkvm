/-
  Nock/RedTeam/Batch490Thm54TopologyAssemblyStop.lean

  **`prefixBadGammas`.**

  The residual-circularity diagnosis is retracted.  At the deployed
  chip, `hFcommit_deployed` and whole-table `VecBFT` land (no
  `RawTopologyBindingResidual`).  `hseed` and the prefix `α`-event
  discharge from the priced walk-root event after tiling.  The exact
  failing statement is `Batch490.computeTopology_of_deployed`: it still
  needs `γ ∉ prefixBadGammas`.

  Memory `hFcommit_memory` lands (via `deployed_row_vmem_at` + `clabM`,
  carrying the existing per-row `hpole`).  Memory `ForestVecBFT` is
  blocked by prover-committed `seedW` and unpriced
  `forestPrefixBadGammas`.

  `Batch448.openConjunctsAfterVer` stays **7**.
-/
import Nock.RedTeam.Batch490Thm54TopologyAssembly
import Nock.RedTeam.Batch448Thm54VerTransfer

set_option autoImplicit false

namespace Nock.RedTeam.Batch490Stop

open Nock.RedTeam.Batch448
open Nock.RedTeam.Batch490

/-- Residual route is not required at the deployed chip. -/
def residualRetracted : List String :=
  ["hFcommit_deployed (Vcomp + clabOf, no residual)",
    "deployed_vecBFT (prefix + bfsValid + tiling + vecBFT_map)",
    "hFcommit_memory (Vmem + clabOfMem, hpole)"]

theorem residualRetracted_length : residualRetracted.length = 3 := by
  decide

/-- The compiled failing statement's extra hypothesis. -/
def failingStatement : String :=
  "Batch490.computeTopology_of_deployed — extra hγ : γ ∉ prefixBadGammas"

theorem failingStatement_name :
    failingStatement =
      "Batch490.computeTopology_of_deployed — extra hγ : γ ∉ prefixBadGammas" :=
  rfl

def openAfterAssemblyStop : List String :=
  openConjunctsAfterAssembly

theorem openAfterAssemblyStop_length : openAfterAssemblyStop.length = 7 :=
  openConjunctsAfterAssembly_length

theorem computeTopology_still_open :
    "computeTopology" ∈ openAfterAssemblyStop := by
  decide

theorem memoryTopology_still_open :
    "memoryTopology" ∈ openAfterAssemblyStop := by
  decide

end Nock.RedTeam.Batch490Stop

#print axioms Nock.RedTeam.Batch490Stop.openAfterAssemblyStop_length
#print axioms Nock.RedTeam.Batch490Stop.failingStatement_name
