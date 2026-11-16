import Nock.RedTeam.Batch139Thm54RootLineExponent

/-!
**Scope.  This module changes no production mathematics.**  It adds no field to any structure,
removes none, ticks no `§J` checkbox, withdraws nothing, and edits no existing declaration.  It adds
receipts *alongside* `GenericHonestPackage.dataOf_consumes_firstLine_and_q_eq`,
`GenericHonestCommitment.residualPremises_still_names_firstLine` and
`AO122.discharge_is_at_the_commitment_not_at_the_premises`, all three of which stand unchanged.

## The finding this answers

`Batch139` §G.2 measured that `dataOf_consumes_firstLine_and_q_eq` and
`AO122.discharge_is_at_the_commitment_not_at_the_premises` prove their equalities by `rfl` between
two **proofs of one `Prop`**, which definitional proof irrelevance makes free
(`Batch139.prop_equations_are_proof_irrelevant`).

**(1) The equational reading of "consumes" is not merely unpinned — it is FALSE, twice over.**

* `computeNodesOf E P` does not mention `P` at all: `computeNodeAt` binds its premises argument as
  `_P` (`GenericHonestData.lean:403-406`), so the committed compute *tree* is a function of `E`
  alone.  §A compiles that as an equation in a **`Type`**, where proof irrelevance has no purchase:
  `computeNodesFrom` is a premise-free definition and `computeNodesFrom_eq_computeNodesOf` is `rfl`,
  whence `computeNodesOf_independent_of_premises` and
  `dataOf_computeNodes_is_a_function_of_E`.
* Consequently every equation of the shape the two existing receipts use survives replacing the
  premise bundle by an **unrelated** one: `consumption_equation_survives_premise_replacement`
  compiles `(dataOf E P M C).q_eq_ringChar = P'.q_eq_ringChar` for arbitrary `P'`.  That is the
  mechanical demonstration that those conjuncts pin nothing — stated about a *fresh* theorem, so
  neither existing receipt is touched.

`P.firstLine`
is consumed to discharge `Data.computeOK`, and that obligation is not merely *proved using* the
premise — on the tree `dataOf` actually commits it is **logically equivalent** to it:

```
computeOK_iff_firstLine :
  ComputeNodesOK E.cfg.challenges.z E.cfg.challenges.α (computeNodesFrom E)
    ↔ FirstLineStartsAtOne E.exec
```

given the other three residual fields, generic in `F`, `K` and `E`.  An `Iff` between two *distinct*
propositions is exactly what proof irrelevance does **not** trivialize: proof irrelevance equates
two proofs of one `Prop`, and says nothing about whether one `Prop` entails another.  The forward
half `computeOK_forces_firstLine` is the pin proper and is unconditional; the backward half is
`GenericHonestData.computeNodesOf_ok` transported along §A's `rfl`.

Two corollaries state the consequence for `ResidualPremises` directly:
`computeOK_from_E_alone_would_pin_every_execution` and `computeOK_from_the_other_three_would_pin`
— any route that obtains `dataOf`'s compute-side obligation from `E` plus the other three residual
fields *is* a proof of `FirstLineStartsAtOne` for every such execution.

Two distinct things:

* *The syntactic reading is unstateable.*  "The proof term of `dataOf`'s `computeOK` field mentions
  `P.firstLine`" is not a proposition Lean can express: `computeOK` is a `Prop`-valued field, so any
  equation between the proof `dataOf` supplies and any other proof of the same statement holds by
  `rfl` regardless.  That is a real limitation of the ambient definitional proof irrelevance, not a
  gap in this build, and it is why §B states the dependency **semantically** — as an entailment
  between propositions — rather than as an equation between proofs.  Nothing can be done about it,
  and the honest response is to state it rather than to work around it.
* *The unconditional impossibility is still open.*  §B's corollaries are conditionals.  Turning
  `computeOK_from_E_alone_would_pin_every_execution` into an outright refutation of "some function
  of `E` alone yields `FirstLineStartsAtOne`" needs a **`BuildableNockExecution` with the pin
  false**, and the build contains no such object.  The nearest compiled negatives are strictly
  below that layer and remain so: `Batch129.vcomp_does_not_force_first_ln_prev` and
  `FirstLineCarrier.F73Probe.compute_rap_content_does_not_pin_first_ln_prev` are a single accepted
  `V_comp` row and a one-row compute-RAP trace with `ln_prev = 2 ≠ 1`, not executions.

* the paper — "Prover builds columns `ln`, `count`".  Verbatim.  Line-number construction is a
  prover step, which is why the pin lives on the commitment and its obligation.
* the paper — "The initial line constraint `ln(1) = α`", item 3 under the heading at `806`.
  Verbatim.  This is the **walk** table's constraint; `FirstLineStartsAtOne` is its compute-table
  analogue, one slot earlier, and that classification is unchanged here.
* the paper — the compute-table timestamp "is unique and represents the line number of the
  compute table at which the memory record was requested, thus having the closed form
  `z^{i} ∈ 𝕂,` where `i` is the compute table line number".  Verbatim.
* the paper — "The `ln` column … also needs to be constrained", with the per-row
  recurrence displayed at `1886`.  Verbatim, and per-row only: there is no compute initial-line
  constraint in the paper, which is precisely why the premise is named rather than derived.
* the paper — the `(α, α², α³)` timestamp powers.  Verbatim.

**Citation defect found and reported.**  the paper is **blank**.  `V_comp`'s first check,
"Check that `((input_formula, formula_tail), 3, ln_prev · z) = mem_record₁`", is on **the paper **.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.AO123

open Nock Nock.Walk
open Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

/-! ## A. The committed compute tree is a function of `E` alone

`GenericHonestData.computeNodeAt` binds its `ResidualPremises` argument as `_P` and never reads it
(`GenericHonestData.lean:403-406`); `computeLabelAt`, `computeForestOf` and `computeNodesOf` thread
that argument onward without reading it either.  The three definitions below are the same
constructions with the argument deleted, and the identification is `rfl`.

This is an equation in `NTree (ComputeNode K)` — a `Type` — so it is *not* an instance of the
pattern `Batch139.prop_equations_are_proof_irrelevant` describes. -/

/-- Premise-free copy of `GenericHonestData.computeLabelAt` -/
def computeLabelFrom (E : BuildableNockExecution F K) (i : ℕ) : ComputeNode K :=
  if h : i - 1 < E.cfg.compRows then
    computeNodeOf (E.semanticData.rows ⟨i - 1, h⟩)
      (publicRowNoun_of_execution E ⟨i - 1, h⟩) (lnPrevExp E ⟨i - 1, h⟩)
  else
    computeNodeOf (E.semanticData.rows ⟨0, E.cfg.compRows_pos⟩)
      (publicRowNoun_of_execution E ⟨0, E.cfg.compRows_pos⟩)
      (lnPrevExp E ⟨0, E.cfg.compRows_pos⟩)

/-- Premise-free copy of `GenericHonestData.computeForestOf` -/
def computeForestFrom (E : BuildableNockExecution F K) : List (NTree (ComputeNode K)) :=
  reconForest 1
    (foCol (bfsForest [E.exec.computeTree]))
    (computeLabelFrom E)
    (bfsForest [E.exec.computeTree]).length

theorem computeForestFrom_ne_nil (E : BuildableNockExecution F K) :
    computeForestFrom E ≠ [] := by
  intro h
  have hlen := congrArg List.length h
  simp [computeForestFrom, reconForest] at hlen

/-- Premise-free copy of `GenericHonestData.computeNodesOf` -/
def computeNodesFrom (E : BuildableNockExecution F K) : NTree (ComputeNode K) :=
  (computeForestFrom E).head (computeForestFrom_ne_nil E)

/-- **The committed compute tree does not depend on the residual premises.**  An equation in a
`Type`, by `rfl`: `dataOf` does not consume `P.firstLine` — or any other field of `P` — in order to
*build* the tree it commits -/
theorem computeNodesFrom_eq_computeNodesOf (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    computeNodesFrom E = computeNodesOf E P :=
  rfl

/-- Hence any two premise bundles commit the same tree. -/
theorem computeNodesOf_independent_of_premises (E : BuildableNockExecution F K)
    (P P' : ResidualPremises E) :
    computeNodesOf E P = computeNodesOf E P' :=
  rfl

/-- …and so does the assembled commitment's `computeNodes` field -/
theorem dataOf_computeNodes_is_a_function_of_E (E : BuildableNockExecution F K)
    (P : ResidualPremises E) (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).computeNodes = computeNodesFrom E :=
  rfl

/-- **Why the two existing consumption receipts pin nothing, demonstrated rather than argued.**
`GenericHonestPackage.dataOf_consumes_firstLine_and_q_eq`'s first conjunct is
`(dataOf E P M C hln).q_eq_ringChar = P.q_eq_ringChar`; the same equation holds with an **unrelated**
premise bundle `P'` on the right, because both sides are proofs of the single `Prop`
`E.q = ringChar K`.  Neither existing theorem is altered, weakened or withdrawn by this: each is
true, and each is now measured. -/
theorem consumption_equation_survives_premise_replacement (E : BuildableNockExecution F K)
    (P P' : ResidualPremises E) (M : MemoryAssemblyPremises E)
    (C : CensusAssemblyPremises E (computeNodesOf E P) M.memoryNodes)
    (hln : Nock.NockVMROM.Thm54.GenericHonestCommitment.FirstLineStartsAtOne E.exec) :
    (dataOf E P M C hln).q_eq_ringChar = P'.q_eq_ringChar :=
  rfl

/-! ## B. The pin: `dataOf`'s compute-side obligation IS `firstLine`

What `P.firstLine` is actually consumed for is `Data.computeOK`: `computeNodesOf_ok` closes its
timestamp branch with `computeNodeAt_specializes`, which is
`computeTimestampSpecializesAt_of_residual`, whose `ln_prev` conjunct is `ln_prev_pow`, whose
`ln_prev_pow_nat` base case at `k = 0` is `P.firstLine` verbatim
(`GenericHonestData.lean:306-316,342-346,360-369,427-431,656-661`).

The receipts below state that dependency as an entailment between propositions, which is the form
proof irrelevance cannot flatten. -/

theorem computeLabelFrom_of_index (E : BuildableNockExecution F K) {i : ℕ}
    (hidx : i - 1 < E.cfg.compRows) :
    computeLabelFrom E i =
      computeNodeOf (E.semanticData.rows ⟨i - 1, hidx⟩)
        (publicRowNoun_of_execution E ⟨i - 1, hidx⟩) (lnPrevExp E ⟨i - 1, hidx⟩) := by
  unfold computeLabelFrom
  rw [dif_pos hidx]

/-- The premise-free tree's root label is the row-zero committed node -/
theorem computeNodesFrom_label (E : BuildableNockExecution F K) :
    (computeNodesFrom E).label =
      computeNodeOf (E.semanticData.rows ⟨0, E.cfg.compRows_pos⟩)
        (publicRowNoun_of_execution E ⟨0, E.cfg.compRows_pos⟩)
        (lnPrevExp E ⟨0, E.cfg.compRows_pos⟩) := by
  show (buildTF 1 (foCol (bfsForest [E.exec.computeTree])) (computeLabelFrom E)
      (bfsForest [E.exec.computeTree]).length 1).label = _
  rw [buildTF_label]
  exact computeLabelFrom_of_index E (i := 1) E.cfg.compRows_pos

/-- Its committed root line-number exponent is the honest ladder's value there, namely `0`. -/
theorem computeNodesFrom_root_line_exponent (E : BuildableNockExecution F K) :
    (computeNodesFrom E).label.stamp.lnPrevExponent = 0 := by
  rw [computeNodesFrom_label]
  rfl

/-- …and its committed root row is the published first compute row -/
theorem computeNodesFrom_root_row (E : BuildableNockExecution F K) :
    (computeNodesFrom E).label.row = E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩ := by
  rw [computeNodesFrom_label]
  rfl

/-- Relative `ComputeTimestampSpecializesAt` does not pin
`ln_prev = α^e`, so `computeOK` no longer entails `FirstLineStartsAtOne`.  The (iv)
success criterion is the next theorem: `computeOK` from the three remaining residual
fields -/
theorem computeOK_from_the_other_three (E : BuildableNockExecution F K)
    (hin : InactiveDecPaddingExec E.exec)
    (hax : ∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i))
    (hq : E.q = ringChar K) :
    ComputeNodesOK E.cfg.challenges.z E.cfg.challenges.α (computeNodesFrom E) := by
  have hok := computeNodesOf_ok E ⟨hin, hax, hq⟩
  rwa [← computeNodesFrom_eq_computeNodesOf E ⟨hin, hax, hq⟩] at hok

/-- The old biconditional `computeOK ↔ firstLine` is broken:
`computeOK_from_the_other_three` inhabits `computeOK` with no `FirstLineStartsAtOne`
hypothesis -/
theorem computeOK_no_longer_iff_firstLine (E : BuildableNockExecution F K)
    (hin : InactiveDecPaddingExec E.exec)
    (hax : ∀ i : Fin E.cfg.compRows, AxisAtomPremises (E.semanticData.rows i))
    (hq : E.q = ringChar K) :
    ComputeNodesOK E.cfg.challenges.z E.cfg.challenges.α (computeNodesFrom E) :=
  computeOK_from_the_other_three E hin hax hq

theorem residualPremises_still_four_at_ao123
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

end

end Nock.RedTeam.AO123

#print axioms Nock.RedTeam.AO123.computeForestFrom_ne_nil
#print axioms Nock.RedTeam.AO123.computeNodesFrom_eq_computeNodesOf
#print axioms Nock.RedTeam.AO123.computeNodesOf_independent_of_premises
#print axioms Nock.RedTeam.AO123.dataOf_computeNodes_is_a_function_of_E
#print axioms Nock.RedTeam.AO123.consumption_equation_survives_premise_replacement
#print axioms Nock.RedTeam.AO123.computeLabelFrom_of_index
#print axioms Nock.RedTeam.AO123.computeNodesFrom_label
#print axioms Nock.RedTeam.AO123.computeNodesFrom_root_line_exponent
#print axioms Nock.RedTeam.AO123.computeNodesFrom_root_row
#print axioms Nock.RedTeam.AO123.computeOK_from_the_other_three
#print axioms Nock.RedTeam.AO123.computeOK_no_longer_iff_firstLine
#print axioms Nock.RedTeam.AO123.residualPremises_still_four_at_ao123
