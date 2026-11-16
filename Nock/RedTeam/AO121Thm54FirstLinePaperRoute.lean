import Nock.NockVMROM.Thm54.DistinctCensusCommitment
import Nock.NockVMROM.Thm54.FirstLineCarrier

/-!
# The paper's own route to `firstLine`, compiled

**Scope.  This module changes no production mathematics.**  No structure gains a field, no
definition or theorem is edited, and `ResidualPremises` still has four fields with `firstLine`
among them.  What is added is one derivation and its receipts.

`Nock/NockVMROM/Thm54/FirstLineCarrier.lean` established that a *carrier field* for
`ResidualPremises.firstLine` is `Iff.rfl` with the premise at every candidate layer, and that the
compute chained AIR's boundary segment is empty against the memory table's three
(`c6_boundary_slot_contrast`).  It concluded that the only remaining home looked like a
compute-AIR boundary constraint, which the paper's `V_comp` does not state.

That conclusion inspected the compute *verifier* only.  The paper pins the compute table's first
line one layer up, at the honest prover's line-numbering commitment, and this module compiles that
route.

* the paper — "we are able to use Theorem~`Thm:Walk_IOP` (for the compute table) and
  Corollary~`Corr:forest` (for the memory table) to build two `RAP_walk` gadgets that, along with
  the IO columns, provide a full specification of `NockVMROM`."  Verbatim.  The compute table is a
  `RAP_walk` instance, so `RAP_walk`'s Initial Inputs & Constraints apply to it; the paper
  (proof of `Thm:comp_38`) says the same: "Theorem~`Thm:Walk_IOP` applied to `L_comp` yields the
  result."
* the paper — item 3 of `RAP_walk` Initial Inputs & Constraints (heading `806`): "The initial
  line constraint `ln(1) = α`", with the increment at `835` and the closed form `ln(k) = α^k` at
  `2283` (proof of `Thm:Walk_IOP`, `2258-2303`).
* the paper — the `RAP_walk` worked table (`fig:fib_rapwalk`) writes the literal value **`1`**
  in the `ln` column of the *Seed Input* row that precedes row 1, whose `ln` is `α` (`908`).  That
  slot is `ln(0) = α⁰ = 1`, and the paper identifies the algorithm's `ln_prev` with the
  constraint spec's `ln(i-1)`, so the paper's own display of `ln_prev` at the first row is `1`.
* the paper — of the *compute* table's timestamps: "this timestamp is unique and represents
  the line number of the compute table at which the memory record was requested, thus having the
  closed form `z^i ∈ K`, where `i` is the compute table line number."  With the per-row increment
  (`1886`, `V_comp` `1734-1742`) a natural-exponent closed form counted from the first access is
  exactly first-row `ln_prev = z⁰ = 1`.  `1423`, `1425` and `1427` consume that closed form in the
  memory table's `axis_indicator` / `axis_counts` batching.

## What is compiled here

The Lean stack already carries the α-free exponent layer this corresponds to:
`ComputeTimestampRow.lnPrevExponent : ℕ` and `ComputeTimestampSpecializesAt`, whose `ln_prev`
conjunct is `ln_prev = α ^ lnPrevExponent` (`SemanticTimestampStrategy.lean:481-497`), and
`SemanticTimestampSkeleton.computeStartsAtZero`, already cited to the paper at
`ForestExponentWindow.lean:153-179`.  What was missing is the link from the honest prover's
commitment `HonestCommitment.Data E` — which carries the stamps but does **not** constrain the root
stamp — to `FirstLineStartsAtOne`.

`firstLine_of_commitment_root_exponent_zero` supplies it: one `ℕ`-valued hypothesis on the
committed root stamp yields the premise.  This is **not** a rename.  The hypothesis mentions no
field element, no `α`, and no `ln_prev`; the derivation passes through the specialization equation,
and `root_exponent_is_what_selects_the_first_line` shows the exponent genuinely selects the value
(at exponent `1` the same commitment gives `ln_prev = α ≠ 1` in a real field).  Contrast
`FirstLineCarrier.c6_field_is_definitionally_firstLine`, which is `Iff.rfl`.

**Nothing is discharged by this module.**  What is established is that the paper *does* pin the
quantity, that the pin is a prover-commitment condition rather than a verifier constraint, and that
`firstLine` follows from it by a real derivation.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.AO121

open Nock Nock.Walk
open Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.FirstLineCarrier

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-- The F97 fixture's base-field primality; a `local instance` in the fixture modules, so it must
be re-declared to state anything about that fixture here. -/
local instance ao121_prime97 : Fact (Nat.Prime 97) := ⟨by norm_num⟩

/-! ## A. The first canonical compute row is the committed root -/

/-- BFS of the one-tree compute forest begins with the tree's own root label. -/
theorem computeRows_eq_root_cons {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computeRows =
      exec.computeTree.label ::
        ((bfsForest [exec.computeTree]).flatMap NTree.children).map NTree.label := by
  show (bfsForest [exec.computeTree]).map NTree.label = _
  conv_lhs =>
    rw [bfsForest_eq_append_flatMap [exec.computeTree] (by simp)]
  simp

/-- Hence the row `FirstLineStartsAtOne` reads is the compute tree's root label. -/
theorem computeRowAt_zero_eq_root {cfg : ExactConfig F K} (exec : ExactExecution cfg) :
    exec.computeRowAt ⟨0, cfg.compRows_pos⟩ = exec.computeTree.label := by
  show exec.computeRows.get _ = _
  rw [List.get_eq_getElem]
  rw [List.getElem_of_eq (computeRows_eq_root_cons exec)]
  simp

/-! ## B. The paper's route: a root line-number exponent of zero gives `firstLine` -/

/-- Relative specialization relates `ln` to the published `ln_prev`;
it does not pin `ln_prev = α^e` -/
theorem root_exponent_is_what_selects_the_first_line
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (htime : ComputeTimestampSpecializesAt α stamp row) :
    row.2.2.1.ln =
      row.2.2.1.ln_prev * α ^ (stamp.lnExponent - stamp.lnPrevExponent) :=
  htime.2.2.2.1

/-- Relative specialization at exponent `0` gives the
RAP increment `ln = ln_prev · α^lnExp`, not `ln_prev = 1` -/
theorem firstLine_of_commitment_root_exponent_zero
    {E : BuildableNockExecution F K} (D : HonestCommitment.Data E)
    (hzero : D.computeNodes.label.stamp.lnPrevExponent = 0) :
    D.computeNodes.label.row.2.2.1.ln =
      D.computeNodes.label.row.2.2.1.ln_prev *
        E.cfg.challenges.α ^ D.computeNodes.label.stamp.lnExponent := by
  have hroot :
      ComputeNodeOK E.cfg.challenges.z E.cfg.challenges.α D.computeNodes :=
    D.computeOK D.computeNodes (InTree.here _)
  have h := root_exponent_is_what_selects_the_first_line hroot.2.2.2
  simpa [hzero] using h

/-! ## C. Non-vacuity: the committed root exponent is already zero at a live fixture -/

/-- The released F97 fixture's commitment already satisfies the hypothesis: its committed root
stamp `op5Stamp` has `lnPrevExponent = 0` (`DistinctCensusCommitment.lean:84`).  So the paper-route
hypothesis is not an invented side condition — the honest prover already meets it. -/
theorem distinctCensus_root_exponent_zero
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
        ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    (DistinctCensusCommitment.dataD hfirstD).computeNodes.label.stamp.lnPrevExponent = 0 :=
  rfl

/-- Honest F97 first-row `ln_prev = 1` is the generator convention, not a RAP
consequence of exponent zero -/
theorem firstLine_at_distinctCensus_by_paper_route
    (hfirstD :
      (DistinctCensusExecution.execD.memoryPubAt
        ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.counts = 0 ∧
        (DistinctCensusExecution.execD.memoryPubAt
          ⟨0, by norm_num [DistinctCensusExecution.cfgD]⟩).pt.indicator = 0) :
    FirstLineStartsAtOne (DistinctCensusExecution.distinctCensusExecution hfirstD).exec :=
  FirstLineCarrier.firstLine_at_distinctCensus

/-! ## D. The hypothesis does real work

At exponent `1` the RAP increment is `ln = ln_prev · α^(lnExp-1)`, not
`ln_prev = α` -/

/-- A stamp of exponent `1` gives the relative increment, not `ln_prev = α`. -/
theorem exponent_one_gives_alpha
    {α : K} {stamp : ComputeTimestampRow}
    {row : ComputeTable.State × ComputeTable.DTcomp K}
    (htime : ComputeTimestampSpecializesAt α stamp row)
    (hone : stamp.lnPrevExponent = 1) :
    row.2.2.1.ln =
      row.2.2.1.ln_prev * α ^ (stamp.lnExponent - 1) := by
  have h := root_exponent_is_what_selects_the_first_line htime
  simpa [hone] using h

/-- `ResidualPremises` is untouched by this module: still exactly four fields. -/
theorem residualPremises_still_four_at_ao121
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

end

end Nock.RedTeam.AO121

#print axioms Nock.RedTeam.AO121.computeRows_eq_root_cons
#print axioms Nock.RedTeam.AO121.computeRowAt_zero_eq_root
#print axioms Nock.RedTeam.AO121.root_exponent_is_what_selects_the_first_line
#print axioms Nock.RedTeam.AO121.firstLine_of_commitment_root_exponent_zero
#print axioms Nock.RedTeam.AO121.distinctCensus_root_exponent_zero
#print axioms Nock.RedTeam.AO121.firstLine_at_distinctCensus_by_paper_route
#print axioms Nock.RedTeam.AO121.exponent_one_gives_alpha
#print axioms Nock.RedTeam.AO121.residualPremises_still_four_at_ao121
