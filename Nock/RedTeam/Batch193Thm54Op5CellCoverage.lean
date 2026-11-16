/-
  Nock/RedTeam/Batch193Thm54Op5CellCoverage.lean

  **The OP5 cell-operand case is covered, and it was never a coin problem.**

  `GS` §4 then called the counting discharge
  "bypassed, not dissolved" for the same reason.  **Both overstate the gap, and this batch is the
  correction.**

  The coin condition never sees the operand nouns.  `needsRlc5 pub` is
  `pub.state =.s5 ∧ pub.sf1_e ≠ pub.sf2_e` (`TableWFBounds.lean:101`) — a condition on the two
  result **fingerprints**.  So there are exactly two branches, and cells are covered in both:

  * fingerprints **agree** — `needsRlc5` is false and `rlc5Holds` is vacuous, whatever the nouns
    were.  Two distinct cell nouns colliding under `encC z` is precisely this branch.
    `badComputeAt_empty` (`:302`) already names it.
  * fingerprints **differ** — the delta vector is nonzero (`some_delta_of_fp_ne`, `:127`) and the
    hyperplane counting applies, which is `GS`'s `exists_computeCoinsGeneric`.  Its only hypothesis
    is the row count; it carries no seed condition and no `op5ResultsAgree`.

  `op5ResultsAgree` and `op5C1Ready` belong to the **seed** family, not the coin family — their
  consumers are `SeedGood` (`GenSeedGoodInstance.lean:17`) and `SeedOK`
  (`GenMatmulSeed.lean:41`), and `ComputeCoinsGeneric` never mentions either.  And the cell case
  there **is** a counted event with an error bound, already proved:
  `op5ResultsAgree_bad_card_le_of_ne` (`GenDyckBadSeed.lean:324`) bounds the failing seeds by
  `2 * Λ - 1` — the NPR degree bound — given the two results are distinct nouns, leaf-bounded by `Λ`
  and `q`-bounded.  `GenRowShape.lean:80-137` already unions that with the `cons`/dyck and OP3
  components into `RowSeedGood`'s failure set.

  So the cell case is discharged twice over, in two different families, and needs nothing new.
  `op5C1Ready`'s own docstring at `GenSeedGoodInstance.lean:55` says it "is not needed here" — it is
  a matmul-route conjunct, not a general requirement.
-/
import Nock.NockVMROM.Thm54.TraceGen.GenCoinCounting
import Nock.NockVMROM.Thm54.TraceGen.GenCommitmentBridge

set_option autoImplicit false

namespace Nock.RedTeam.Batch193

open Nock Nock.TableWFBounds
open Nock.NockVMROM.Thm54 Nock.NockVMROM.Thm54.TraceGen

variable {K : Type} [Field K]

/-- **The vacuous branch, named.**  Equal result fingerprints make `rlc5` vacuous at *every* coin
vector — so a pair of cell operands that collide under `encC z` is not a gap but this case. -/
theorem rlc5Holds_of_fp_eq (a b c : K) (pub : ComputeTable.Pub K)
    (h : pub.sf1_e = pub.sf2_e) : rlc5Holds a b c pub :=
  fun hneed => absurd h hneed.2

/-- **The coin condition is a function of the fingerprints alone.**  Two rows with the same two
result fingerprints have the same `rlc5Holds`, whatever nouns produced them — which is why the
atom/cell distinction cannot enter the coin argument. -/
theorem rlc5Holds_congr_of_fp (a b c : K) (p q : ComputeTable.Pub K)
    (hst : p.state = q.state) (h1 : p.sf1_e = q.sf1_e) (h2 : p.sf2_e = q.sf2_e) :
    rlc5Holds a b c p ↔ rlc5Holds a b c q := by
  unfold rlc5Holds needsRlc5 rlc5Form deltaSize deltaDyck deltaLeaf
  rw [hst, h1, h2]

/-- **Both branches, as one statement.**  Every `pub` is covered: either the fingerprints agree and
`rlc5Holds` is free, or they differ and the coin vectors that fail form the counted hyperplane
`badComputeAt`.  No third case, and no appeal to the operands being atoms. -/
theorem rlc5_dichotomy [Fintype K] [DecidableEq K] (a b c : K) (pub : ComputeTable.Pub K) :
    rlc5Holds a b c pub ∨ ((a, b, c) ∈ badComputeAt pub ∧ pub.sf1_e ≠ pub.sf2_e) := by
  by_cases h : rlc5Holds a b c pub
  · exact Or.inl h
  · have hmem : (a, b, c) ∈ badComputeAt pub := by
      by_contra hnm
      exact h ((rlc5Holds_iff_not_mem_bad a b c pub).mpr hnm)
    refine Or.inr ⟨hmem, ?_⟩
    intro hfp
    exact h (rlc5Holds_of_fp_eq a b c pub hfp)

end Nock.RedTeam.Batch193

#print axioms Nock.RedTeam.Batch193.rlc5Holds_of_fp_eq
#print axioms Nock.RedTeam.Batch193.rlc5Holds_congr_of_fp
#print axioms Nock.RedTeam.Batch193.rlc5_dichotomy
