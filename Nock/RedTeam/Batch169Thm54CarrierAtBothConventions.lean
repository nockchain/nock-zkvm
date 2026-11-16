/-
  Nock/RedTeam/Batch169Thm54CarrierAtBothConventions.lean

  **The coin-parameterised carrier, instantiated at both live conventions.**

  A grep for its theorems returns one hit
  outside their own file, and that hit is a docstring. `Batch167` exercises only `genExactConfig`,
  which `EF` deliberately left unparameterised, so `genExactExecution` — the coin-parameterised
  carrier — had been validated at **zero** configurations.

  That is uncomfortable given the history: `EE`'s own diagnosis was "a generic object validated at
  one configuration, where the one it does not fit is the other one", and `EF` answered it with
  statements validated at none. The lesson is *instantiate at the configuration
  least like the one you had in mind*; this module applies it to the fix itself.

  The two live conventions are:

  * `DotConfig769.computeTree` = `mapNTree GenComputeRow.row (renderRows …)` — the rendered coins
    `(0,0,0)` kept (`GenTierAConfig769.lean:81`);
  * `GenMatmulConfig.computeTree` = `mapNTree (setRowCoins 0 0 1 ∘ ·.row) (renderRows …)` — coins
    overwritten (`GenMatmulConfig.lean:102`).

  The matmul convention is what the carrier commits *by construction* at `(a,b,c) = (0,0,1)`, so it
  needs nothing. The Tier A convention needs the coin overwrite to be the identity at `(0,0,0)`, and
  that is what is proved here — the lemma nobody had written.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.RedTeam.Batch169

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open ComputeTable

variable {K : Type} [Field K]

/-- **At `(0,0,0)` the coin overwrite is the identity on a rendered row.**

Every `render*Row` writes inputs `⟨α, z, 0, 0, 0⟩`, so rebuilding them with zero coins changes
nothing. Eleven-way split, matching `setRowCoins_renderNode_inputs`. -/
theorem setRowCoins_zero_renderNode (z α : K) (g : GenComputeRow K) :
    setRowCoins 0 0 0 (renderNode z α g).row = (renderNode z α g).row := by
  cases hst : g.skel.state <;>
    simp [setRowCoins, renderNode, hst, renderOp0Row, renderOp1Row, renderOp2Row,
      renderOp3Row, renderOp4Row, renderOp5Row, renderOp6Row, renderOp7Row,
      renderOp8Row, renderOp9Row, renderConsRow]

/-- **The carrier at `(0,0,0)` commits exactly `DotConfig769`'s compute tree shape.**

So the coin parameter really does subsume the Tier A convention, rather than merely being
compatible with it in prose. -/
theorem carrier_at_tierA_convention (z α : K) (t : NTree (GenComputeRow K)) :
    mapNTree (fun g : GenComputeRow K => setRowCoins 0 0 0 g.row) (genComputeRows z α t) =
      mapNTree GenComputeRow.row (genComputeRows z α t) := by
  rw [genComputeRows, renderRows_eq_mapNTree, mapNTree_comp, mapNTree_comp]
  exact mapNTree_eq_of (fun g => setRowCoins_zero_renderNode z α g) _

/-- The matmul convention needs no lemma: it **is** the carrier's committed tree at `(0,0,1)`,
definitionally. Stated so both directions of `EF`'s claim are in the build. -/
theorem carrier_at_matmul_convention (z α : K) (t : NTree (GenComputeRow K)) :
    mapNTree (fun g : GenComputeRow K => setRowCoins 0 0 1 g.row) (genComputeRows z α t) =
      mapNTree (fun g : GenComputeRow K => setRowCoins (0 : K) 0 1 g.row)
        (renderRows z α (bfsAssign (airReorder t))) := rfl

end Nock.RedTeam.Batch169

#print axioms Nock.RedTeam.Batch169.setRowCoins_zero_renderNode
#print axioms Nock.RedTeam.Batch169.carrier_at_tierA_convention
#print axioms Nock.RedTeam.Batch169.carrier_at_matmul_convention
