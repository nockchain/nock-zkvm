/-
  Nock/RedTeam/Batch170Thm54PoleAtZeroOffset.lean

  **Why the LogUp pole does not degenerate at `β = γ = 0`.**

  `EL` escalated `memInputs z = ⟨z, 0, 0⟩` as possibly a delta against the paper ("Verifier
  responds with random elements `α, β ∈ K`"), on the grounds that `β = 0` is where the pole
  `RLC^γ(mem_record) − β` loses its offset. **That escalation was overstated**, and
  this module compiles the reason.

  Read at source, the paper supplies the answer itself. the paper:

  > performing cons should implicitly check that the sizes involved are nonzero, **since the sizes
  > are exponentiated values of `z`**

  and `encC z n |>.size = z ^ n.leaves` (`Encode.lean:49`) is exactly that. So:

  * at `γ = 0` every `recRLC` term but the first carries a positive power of `γ` and vanishes, leaving
    `recRLC 0 r = r.root.size`;
  * at `β = 0` the offset is gone, so `pole (memInputs z) r = r.root.size`;
  * and `r.root.size = z ^ leaves ≠ 0` whenever `z ≠ 0`.

  **So `MemoryTable.WF.pole_ne` is discharged structurally rather than probabilistically.** The paper
  gets pole non-vanishing from β's randomness; this construction gets it from the size-is-a-power-of-`z`
  fact the paper states at `1716`. `z ≠ 0` is already carried everywhere.

  **What the randomness is still needed for, and where it lives.** A symbolic identity implies the sampled one, so fixing the
  table's `β` does not weaken it.

  **Three different `β`s.**

  | paper | role | this tree |
  |---|---|---|
  | `Def:RAP` `(ω, β)` | evaluation-orbit coset shift | `OrbitDomain.βcoset`, with `βcoset_ne_zero` |
  | `Def:NMR` `𝒯 := β^k` | **timestamp base** | `ChallengeVector.α` |
  | pole offset | LogUp offset | `ChallengeVector.β` |

  Only the third is set to `0`. An earlier reading that conflated these is what made the
  escalation look sharper than it was.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenSemanticDataParts
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.RedTeam.Batch170

open Nock Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen
open MemoryTable ComputeTable

variable {K : Type} [Field K]

/-- At `γ = 0` the record RLC collapses to the root size: every other term carries `γ^(k≥1)`. -/
theorem recRLC_zero (r : MemRec K) : recRLC 0 r = r.root.size := by
  simp [recRLC]

/-- **The pole at the generated memory challenges is exactly the root size.** -/
theorem pole_memInputs (z : K) (r : MemRec K) :
    pole (memInputs z) r = r.root.size := by
  simp [pole, memInputs, recRLC_zero]

/-- **And it is nonzero whenever the seed is** — because sizes are powers of `z`.  This is `WF.pole_ne`'s content at these challenges,
discharged structurally rather than by randomness in `β`. -/
theorem pole_memInputs_ne_zero (z : K) (hz : z ≠ 0) (n : Noun)
    (child : ComputeTable.FP K) (axis ts : K) :
    pole (memInputs z) ⟨encC z n, child, axis, ts⟩ ≠ 0 := by
  rw [pole_memInputs]
  simpa using pow_ne_zero n.leaves hz

/-- The degenerate case is real and is exactly `z = 0`: at a zero seed the pole *does* vanish, so
`z ≠ 0` is load-bearing here and not decoration. -/
theorem pole_memInputs_zero_seed (n : Noun) (hn : n.leaves ≠ 0)
    (child : ComputeTable.FP K) (axis ts : K) :
    pole (memInputs (0 : K)) ⟨encC 0 n, child, axis, ts⟩ = 0 := by
  rw [pole_memInputs]
  show (0 : K) ^ n.leaves = 0
  exact zero_pow hn

end Nock.RedTeam.Batch170

#print axioms Nock.RedTeam.Batch170.pole_memInputs
#print axioms Nock.RedTeam.Batch170.pole_memInputs_ne_zero
#print axioms Nock.RedTeam.Batch170.pole_memInputs_zero_seed
