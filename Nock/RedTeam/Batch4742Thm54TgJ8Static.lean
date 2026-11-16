/-
  Nock/RedTeam/Batch4742Thm54TgJ8Static.lean

  **4741 (`V1J8/Static`, `V1J8/StaticExample`).**  The executable
  J-8 checker, first step: `checkStaticJ8` and `checkStaticJ8_iff` (every K-free conjunct of `AcceptsJ8V`), the
  split `acceptsJ8V_iff : AcceptsJ8V ↔ StaticJ8 ∧ PubEqJ8 ∧ ChipsJ8` and the partial iff `acceptsJ8V_iff_check`, and
  the static check at the J-8 example `*[[0 0] [0 1]] = [0 0]` (kernel, through the iff).
  NOT claimed: an executable `checkPubJ8` (`Quad.mk` is noncomputable; S2), any chip check (S3–S5), `checkJ8_iff`.
-/
import Nock.V1J8.StaticExample

namespace Nock.RedTeam.Batch4742

#check @Nock.V1J8.checkStaticJ8_iff
#check @Nock.V1J8.acceptsJ8V_iff
#check @Nock.V1J8.acceptsJ8V_iff_check
#check @Nock.V1J8.StaticExample.checkStaticJ8_example_goldilocks
#print axioms Nock.V1J8.checkStaticJ8_iff
#print axioms Nock.V1J8.acceptsJ8V_iff
#print axioms Nock.V1J8.acceptsJ8V_iff_check
#print axioms Nock.V1J8.checkPubJ8_iff
#print axioms Nock.V1J8.staticJ8_of_accepts
#print axioms Nock.V1J8.StaticExample.staticJ8_example
#print axioms Nock.V1J8.StaticExample.checkStaticJ8_example
#print axioms Nock.V1J8.StaticExample.checkStaticJ8_example_goldilocks

end Nock.RedTeam.Batch4742
