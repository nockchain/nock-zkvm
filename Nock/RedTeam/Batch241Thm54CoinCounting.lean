/-
  Nock/RedTeam/Batch241Thm54CoinCounting.lean

  **The fourth counted event, measured at both live generator programs.**

  A definition of a failure set is only worth
  what its instances say, so this module measures `computeCoinFailure` at the two programs that
  actually drive the generic chain, and the two answers are forced in opposite directions:

  * **Tier A (`dotTree`, coins `(0, 0, 0)`)** — the set is **empty**.  It has no `.s5` row, and
    `Batch180.dot_computeCoins` proves the condition `∀ a b c` there, so anything other than `∅`
    would contradict a compiled theorem.
  * **The broad program (`bpTree`, coins `(0, 0, 1)`)** — the set is **non-empty and contains
    `(0, 0, 0)`**, because `Batch233.bp_computeCoins_false` refutes the condition at exactly that
    vector; and it does **not** contain `(0, 0, 1)`, the vector `Batch231` commits.

  That is the route `GM` §7 said was missing.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenCoinCounting
import Nock.RedTeam.Batch233Thm54StateCoverageNonvacuity

set_option autoImplicit false

namespace Nock.RedTeam.Batch241

open Nock Nock.Walk
open Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.TraceGen
open Nock.NockVMROM.Thm54.SemanticStrategy
open Nock.TableWFBounds
open ComputeTable

/-- The table field of both programs, `GaloisField 769 3`. -/
abbrev DK := Batch231.DK

/-! ## The two instances the counted formulation forces

`computeCoinFailure` is a `Finset.univ.filter`/`biUnion` over `ComputeCoins K = K × K × K`, so it
carries `[Fintype K] [DecidableEq K]`, and instance search finds neither at `GaloisField 769 3`.
`local`, so nothing downstream inherits them. -/

noncomputable local instance : Fintype DK := Fintype.ofFinite _
noncomputable local instance : DecidableEq DK := Classical.decEq _

/-- The field size, at whichever `Fintype` instance is in scope: `Fintype.card` is
instance-independent through `Nat.card`. -/
theorem card_DK : Fintype.card DK = 769 ^ 3 := by
  rw [Fintype.card_eq_nat_card]
  exact GaloisField.card 769 3 (by norm_num)

/-! ## Tier A: the event is EMPTY

Sharp test.  `DotConfig769` commits `(0, 0, 0)` and `Batch180.dot_computeCoins` proves
`ComputeCoinsGeneric` there at **every** coin vector, so the failure set must be `∅`.  It is, and
for the structural reason: no `.s5` row, hence `needsRlc5` false at every BFS index. -/

/-- **The counted event is empty at Tier A.** -/
theorem tierA_coinFailure_empty (z α : DK) :
    computeCoinFailure z α (airReorder (dotTree (K := DK))) = ∅ :=
  computeCoinFailure_eq_empty_of_noOp5 z α _ Batch180.dot_air_noOp5

/-- Consistency with `Batch180.dot_computeCoins`: the counting recovers the `∀ a b c` verdict at
Tier A rather than merely coexisting with it. -/
theorem tierA_coins_all (z α a b c : DK) :
    ComputeCoinsGeneric z α a b c (airReorder (dotTree (K := DK))) := by
  refine computeCoinsGeneric_of_not_mem z α a b c _ ?_
  rw [tierA_coinFailure_empty z α]
  exact Finset.notMem_empty _

/-- In particular Tier A's own committed coin vector is outside the event. -/
theorem tierA_zero_not_mem (z α : DK) :
    ((0 : DK), (0 : DK), (0 : DK)) ∉
      computeCoinFailure z α (airReorder (dotTree (K := DK))) := by
  rw [tierA_coinFailure_empty z α]
  exact Finset.notMem_empty _

/-! ## The broad program: the event is NON-EMPTY and contains `(0, 0, 0)`

The other sharp test.  `Batch233.bp_computeCoins_false` refutes the condition at `(0, 0, 0)` for
every `z` and `α`, so that vector must be **in** the failure set. -/

/-- **Tier A's coin vector is in the broad program's failure set.** -/
theorem bp_zero_mem (z α : DK) :
    ((0 : DK), (0 : DK), (0 : DK)) ∈ computeCoinFailure z α (bpTreeAir (K := DK)) :=
  mem_computeCoinFailure_of_not_computeCoinsGeneric (Batch233.bp_computeCoins_false z α)

/-- **So the event is non-empty**, at every seed and timestamp base. -/
theorem bp_coinFailure_nonempty (z α : DK) :
    (computeCoinFailure z α (bpTreeAir (K := DK))).Nonempty :=
  ⟨_, bp_zero_mem z α⟩

/-- And the vector `Batch231` actually commits is **outside** it — the failure set separates the two
configurations' coin conventions exactly where `GM` §6 says it should. -/
theorem bp_one_not_mem (z α : DK) :
    ((0 : DK), (0 : DK), (1 : DK)) ∉ computeCoinFailure z α (bpTreeAir (K := DK)) := by
  refine (computeCoinsGeneric_iff_not_mem z α 0 0 1 _).mp ?_
  rw [← airReorder_bpTree]
  exact bp_computeCoins z α

/-! `bp_exists_coins` is the point of the module: it supplies good coins at a program where the `.s5`
row is live, from `17 < 769 ³` and nothing else.  It does not go through `op5C1Ready`, so it is not
subject to `GM` §7's tension (which is about `computeCoinsGeneric_c_one` needing the OP5 operands
equal or both atoms). -/

/-- The bound at the broad program: seventeen rows, one hyperplane each. -/
theorem bp_coinFailure_card_le (z α : DK) :
    (computeCoinFailure z α (bpTreeAir (K := DK))).card ≤ 17 * (769 ^ 3 * 769 ^ 3) := by
  have h := computeCoinFailure_card_le z α (bpTreeAir (K := DK))
  rwa [Batch233.bp_air_bfsForest_len, card_DK] at h

/-- **Good coins exist at the broad program, by counting.**  Side condition: seventeen compute rows
against a field of `769 ³` elements. -/
theorem bp_exists_coins (z α : DK) :
    ∃ a b c : DK, ComputeCoinsGeneric z α a b c (bpTreeAir (K := DK)) := by
  refine exists_computeCoinsGeneric z α _ ?_
  rw [Batch233.bp_air_bfsForest_len, card_DK]
  norm_num

/-- The same, at the tree the chain's hypotheses are literally stated at. -/
theorem bp_exists_coins_air (z α : DK) :
    ∃ a b c : DK, ComputeCoinsGeneric z α a b c (airReorder (bpTree (K := DK))) := by
  rw [airReorder_bpTree]
  exact bp_exists_coins z α

/-- And at Tier A, for the record — the same theorem, eight rows. -/
theorem tierA_exists_coins (z α : DK) :
    ∃ a b c : DK, ComputeCoinsGeneric z α a b c (airReorder (dotTree (K := DK))) :=
  ⟨0, 0, 0, tierA_coins_all z α 0 0 0⟩

end Nock.RedTeam.Batch241

#print axioms Nock.RedTeam.Batch241.card_DK
#print axioms Nock.RedTeam.Batch241.tierA_coinFailure_empty
#print axioms Nock.RedTeam.Batch241.tierA_coins_all
#print axioms Nock.RedTeam.Batch241.bp_zero_mem
#print axioms Nock.RedTeam.Batch241.bp_coinFailure_nonempty
#print axioms Nock.RedTeam.Batch241.bp_one_not_mem
#print axioms Nock.RedTeam.Batch241.bp_coinFailure_card_le
#print axioms Nock.RedTeam.Batch241.bp_exists_coins
#print axioms Nock.RedTeam.Batch241.bp_exists_coins_air
