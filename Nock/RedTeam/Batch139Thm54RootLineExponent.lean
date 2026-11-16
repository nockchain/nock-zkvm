import Nock.RedTeam.AO122Thm54RootLineExponentGates

/-!
**Scope.  This module changes no production mathematics.**  It adds no field to any structure,
removes none, ticks no `§J` checkbox, and edits no production declaration.

Both the paper cites in this file (§`ln_prev`
> identification, and the `honest_ladder_pins_row_zero` neighbourhood) should be read as
> **the paper **: `1727` is **blank** — `\begin{algorithm}` for `V_comp` opens at `1720`,
> `\Procedure` is `1726`, and the first check, "`((input_formula, formula_tail), 3, ln_prev · z) =
> mem_record₁`", is on `1728`.  The *content* of the cite is correct and no statement, proof or
> measurement in this module changes.

## The three questions, and what this module settles

§B then settles whether the exclusion is **sound**, and it is, for a reason that is compiled rather
than argued: the excluded exponent is not a line number.  the paper fixes the meaning of the
committed exponent — the timestamp "represents the line number of the compute table at which the
memory record was requested, thus having the closed form `z^i ∈ K`, where `i` is the compute table
line number" — and the Lean stack's own honest ladder `GenericHonestData.lnPrevExp` is exactly that
line-number count.  The ladder
is `0` at row zero for **every** execution, and at F73 the ladder's whole range is `{0}`, so the
re-stamped exponent `9` is not the line number of any row of that table.  The excluded commitment is
one whose committed `ℕ` misdescribes the line number, not an honest prover's alternative numbering.
The `orderOf α` ambiguity that makes it invisible at the published `K`-columns is a property of the
*fixture's* small field, not a freedom the paper grants.

**The row is intact.**

So the field is strictly stronger, is not `Iff.rfl` with `firstLine` at
any layer, and `C6`'s failure mode is genuinely avoided.

## Verdict

The narrowing is **sound as a convention pin** and is **not empty**; the ticked row is **intact**;
gate (5) is **right**.  `narrowing_measured_exactly_at_f73` constructs it.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Nock.RedTeam.Batch139

open Nock Nock.Walk
open Nock.NockVMROM Nock.NockVMROM.Thm54
open Nock.NockVMROM.Thm54.SemanticTimestampStrategy
open Nock.NockVMROM.Thm54.HonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestCommitment
open Nock.NockVMROM.Thm54.GenericHonestData
open Nock.NockVMROM.Thm54.FirstLineCarrier
open Nock.NockVMROM.Thm54.ForestExponentWindow
open Nock.NockVMROM.Thm54.ForestExponentOrderClosure

noncomputable section

variable {F K : Type} [Field F] [Field K] [Algebra F K]

local instance b139_prime73 : Fact (Nat.Prime 73) := ⟨by norm_num⟩

/-! ## A. The narrowing, measured exactly

That is a statement about seven
definitions, not about the carrier.  What follows measures the carrier: it builds the excluded
object and shows precisely which obligations it meets.

`restampRoot d` adds `d` to the committed root's line-number exponent and changes nothing else — not
the root's skeleton, not its published row, not any child. -/

/-- Re-stamp the committed root's line-number exponent by `d`. -/
def restampRoot (d : ℕ) : NTree (ComputeNode K) → NTree (ComputeNode K)
  | .node lbl cs =>
      .node { lbl with
        stamp := { lbl.stamp with
          lnPrevExponent := lbl.stamp.lnPrevExponent + d
          lnExponent := lbl.stamp.lnExponent + d
          recordExponent := fun i => lbl.stamp.recordExponent i + d } } cs

theorem restampRoot_exponent (d : ℕ) (T : NTree (ComputeNode K)) :
    (restampRoot d T).label.stamp.lnPrevExponent = T.label.stamp.lnPrevExponent + d := by
  cases T
  rfl

/-- `compute_rows` is untouched: the published rows are literally `T`'s. -/
theorem restampRoot_row (d : ℕ) (T : NTree (ComputeNode K)) :
    mapNTree ComputeNode.row (restampRoot d T) = mapNTree ComputeNode.row T := by
  cases T with
  | node lbl cs => simp only [restampRoot, mapNTree]

/-- …and so is the committed skeleton, which every remaining `Data` obligation reads through
`skeletonOfNodes`. -/
theorem restampRoot_skel (d : ℕ) (T : NTree (ComputeNode K)) :
    mapNTree ComputeNode.skel (restampRoot d T) = mapNTree ComputeNode.skel T := by
  cases T with
  | node lbl cs => simp only [restampRoot, mapNTree]

theorem restampRoot_skeletonOfNodes (d : ℕ) (T : NTree (ComputeNode K))
    (mf : List (NTree (MemoryNode K))) :
    skeletonOfNodes (restampRoot d T) mf = skeletonOfNodes T mf := by
  simp only [skeletonOfNodes, restampRoot_skel]

/-- **`computeOK` survives re-stamping.**  `ComputeNodesOK` is purely per-node — there is no
parent/child exponent chain in it (`HonestCommitment.lean:421-436`) — and the one conjunct that
reads `lnPrevExponent` reads it only through `α ^ ·`.  So a full period is invisible. -/
theorem restampRoot_computeNodesOK {z α : K} {d : ℕ} {T : NTree (ComputeNode K)}
    (h : ComputeNodesOK z α T) :
    ComputeNodesOK z α (restampRoot d T) := by
  cases T with
  | node lbl cs =>
      obtain ⟨hshape, hstate, hbind, htime⟩ := h _ (InTree.here _)
      simp only [NTree.label_node, NTree.children_node] at hshape hstate hbind htime
      refine ComputeNodesOK.mk' ?_ ?_
      · refine ⟨hshape, hstate, hbind, ?_⟩
        exact AO122.computeTimestampSpecializesAt_lnPrev_add_period htime
      · intro c hc
        exact h.child (by simpa using hc)

/-! ### A.1 The excluded object, at the live F73 fixture -/

namespace F73

open ConcreteStrictPackage BuildableConcrete HonestCommitment.Concrete

noncomputable local instance : Fintype K73cubic := Fintype.ofFinite K73cubic
noncomputable local instance : DecidableEq K73cubic := Classical.decEq K73cubic
local instance : CharP K73cubic (ringChar K73cubic) := ringChar.charP K73cubic

/-- F73's `α` has multiplicative order `9`, so a re-stamp by `9` is invisible to `α`. -/
theorem alpha_pow_nine : concreteExecution.cfg.challenges.α ^ 9 = 1 := by
  have hord : orderOf concreteExecution.cfg.challenges.α = 9 :=
    ForestExponentOrderClosure.Concrete.f73_orderOf_alpha
  rw [← hord]
  exact pow_orderOf_eq_one _

/-- The excluded committed compute tree: F73's own, with the root re-stamped by `orderOf α = 9`. -/
def restamped73 : NTree (ComputeNode K73cubic) :=
  restampRoot 9 HonestCommitment.Concrete.data73.computeNodes

/-- **THE NARROWING, MEASURED EXACTLY.**

Read the five conjuncts against the structure (`HonestCommitment.lean:658-742`):

* `compute_rows` — conjunct 1, verbatim;
* `computeOK` — conjunct 2, verbatim;
* `slotSemantics`, `recordEquations`, `census`, `sizeWindowBound`, `skeletonBounded`,
  `combinedBounded` — conjunct 3: all six read `computeNodes` only through `skeletonOfNodes`, and
  that is unchanged, so each transports by `▸` exactly as `reExpData` transports them;
* `memoryNodes`, `memory_rows`, `memoryOK`, `nounSizeBound`, `Λ`, `q_eq_ringChar` — do not mention
  `computeNodes` at all, so `data73`'s own values serve;
* conjunct 4 is `FirstLineStartsAtOne`, still true, because the *execution* is not a function of the
  commitment's stamps;
* conjunct 5 is the sixteenth field, false.

So the exclusion is not vacuous, and — reading conjuncts 4 and 5 together — the field is **strictly
stronger than `firstLine` at the whole-commitment layer**, not merely at the specialization equation
where `AO122.F73Probe.converse_fails_at_concrete` refuted the converse. -/
theorem narrowing_measured_exactly_at_f73 :
    mapNTree ComputeNode.row restamped73 = concreteExecution.exec.computeTree ∧
      ComputeNodesOK concreteExecution.cfg.challenges.z concreteExecution.cfg.challenges.α
        restamped73 ∧
      skeletonOfNodes restamped73 HonestCommitment.Concrete.data73.memoryNodes =
        skeletonOfNodes HonestCommitment.Concrete.data73.computeNodes
          HonestCommitment.Concrete.data73.memoryNodes ∧
      FirstLineStartsAtOne concreteExecution.exec ∧
      restamped73.label.stamp.lnPrevExponent ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show mapNTree ComputeNode.row
      (restampRoot 9 HonestCommitment.Concrete.data73.computeNodes) = _
    rw [restampRoot_row]
    exact HonestCommitment.Concrete.data73.compute_rows
  · exact restampRoot_computeNodesOK HonestCommitment.Concrete.data73.computeOK
  · exact restampRoot_skeletonOfNodes 9 _ _
  · exact FirstLineCarrier.firstLine_at_concrete
  · have h : restamped73.label.stamp.lnPrevExponent = 9 := by
      simp only [restamped73, restampRoot_exponent, AO122.root_exponent_zero_at_concrete]
    rw [h]
    decide

end F73

/-! ## B. Is the exclusion SOUND?  Yes — the excluded exponent is not a line number

The timestamp "is unique and represents the line
number of the compute table at which the memory record was requested, thus having the closed form
`z^{i} \in \mathbb{K},` where `i` is the compute table line number."  So the committed exponent is
not free data with a `K`-valued shadow — the paper *defines* it to be the line number.

The Lean stack's honest ladder is exactly that count: `GenericHonestData.lnPrevExpNat` starts at `0`
and adds `Nock.Framework.recordCount` per row (`GenericHonestData.lean:170-191`), which is the α-free
content of the compute `ln` recurrence at the paper — `ln(i-1) · (α·Σ_{j∈{1,3,4}} op_j + α²·…
+ α³·…) = ln(i)` — under the identification of the algorithm's `ln_prev` at row `i` with the
constraint spec's `ln(i-1)`.

Two receipts.  The first is general and is the convention itself; the second is the concrete
exclusion. -/

/-- **The paper's own ladder pins the root at zero, for every execution.**  So the sixteenth field
asserts of the committed root exactly the ladder's value there — it is the convention, not a choice
among convention-compatible options -/
theorem honest_ladder_pins_row_zero (E : BuildableNockExecution F K) :
    lnPrevExp E ⟨0, E.cfg.compRows_pos⟩ = 0 :=
  lnPrevExp_zero E

/-- …and the named-premises constructor stamps the committed root with precisely that ladder value,
so `dataOf` meets the field because the ladder does, not because a side condition was arranged. -/
theorem dataOf_root_stamp_is_the_ladder_value (E : BuildableNockExecution F K)
    (P : ResidualPremises E) :
    (computeNodesOf E P).label.stamp.lnPrevExponent = lnPrevExp E ⟨0, E.cfg.compRows_pos⟩ := by
  rw [AO122.computeNodesOf_root_exponent_zero E P, lnPrevExp_zero]

namespace F73

open ConcreteStrictPackage BuildableConcrete HonestCommitment.Concrete

/-- **The excluded exponent is not the line number of any row.**  F73's compute table has one row,
whose ladder value is `0`; `9` is not in the ladder's range.  So `restamped73` commits an `ℕ` that
does not describe the compute table line number at which the record was requested, which is what
the paper says the quantity *is*.  The exclusion is therefore the paper's own convention
asserting itself, and not the removal of an honest prover's legitimate alternative.

Note what this does **not** say: it does not say `restamped73` is detectable at the published
columns.  It is not — that is exactly `narrowing_measured_exactly_at_f73`'s conjunct 4, and it is
why the field has to be a *commitment* condition rather than something a verifier recovers from acceptance -/
theorem excluded_exponent_is_not_a_line_number :
    concreteExecution.cfg.compRows = 1 ∧
      ∀ i : Fin concreteExecution.cfg.compRows, lnPrevExp concreteExecution i ≠ 9 := by
  refine ⟨rfl, ?_⟩
  intro i
  have hrows : concreteExecution.cfg.compRows = 1 := rfl
  have hlt : (i : ℕ) < concreteExecution.cfg.compRows := i.isLt
  have hi : (i : ℕ) = 0 := by omega
  simp only [lnPrevExp, hi, lnPrevExpNat]
  decide

end F73

/-! ## C. Is the ticked `ForestExponentOrder` row intact?  Verified independently — YES

That is necessary but not sufficient: what the
ticked row needs is that its two witnesses still inhabit the sixteen-field `Data`.  The checks below
are at that level, and they are stated so that they would fail if either map had been altered to
touch the compute side.

The two witnesses are `wrapDataExponents D` (the counterexample carrying
`ForestExponentWindow.no_universal_forestExponentOrder`, which the ticked row's scope statement
explicitly retains as `forall_data_shape_still_refuted`) and `normData D` (the positive side,
`forestExponentOrder_normData_of_ne_zero`). -/

section Ticked

variable [FiniteDimensional F K] [Fintype K] [DecidableEq K] [CharP K (ringChar K)]

/-- The wrapping map's compute nodes are `D`'s **as a tree**, not merely at the root exponent.
So no re-stamp of any committed compute node happens anywhere in the counterexample witness. -/
theorem wrapDataExponents_computeNodes {E : BuildableNockExecution F K} (D : Data E) :
    (wrapDataExponents D).computeNodes = D.computeNodes :=
  rfl

/-- Same for the general relabelling, of which wrapping and `normData` are instances. -/
theorem reExpData_computeNodes {E : BuildableNockExecution F K} (f : ℕ → ℕ)
    (hf : ∀ e : ℕ, E.cfg.challenges.α ^ f e = E.cfg.challenges.α ^ e) (D : Data E) :
    (reExpData f hf D).computeNodes = D.computeNodes :=
  rfl

theorem normData_computeNodes {E : BuildableNockExecution F K} (D : Data E) :
    (normData D).computeNodes = D.computeNodes :=
  rfl

/-- **The counterexample still exists.**  Stated at the theorem itself, not at its witness: the
`∀ D'` shape that the ticked row's scope statement explicitly does *not* close is still refuted,
after the carrier addition, for a `D` inhabiting the **sixteen**-field `Data`. -/
theorem ticked_row_counterexample_survives {E : BuildableNockExecution F K} (D : Data E)
    {i : Fin (configTemplateOf E E.cfg.challenges.z).kMem}
    (hne : Nock.AxisBridge.readExps
      (ProductionAxisStructureVerifier.alphaFreeRoot
        (D.executionTemplate E.cfg.challenges.z) i) ≠ []) :
    ¬ ∀ D' : Data E,
        GenericHonestPackage.ForestExponentOrder
          (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α :=
  ForestExponentWindow.no_universal_forestExponentOrder D hne

/-- **The ticked positive still exists**, likewise stated at the theorem: for every commitment with
`α ≠ 0` there is a commitment of the same execution — `normData D`, an inhabitant of the
sixteen-field `Data` by `normData_computeNodes` plus `reExpData`'s `root_line_exponent :=
D.root_line_exponent` — whose window holds -/
theorem ticked_row_positive_survives {E : BuildableNockExecution F K} (D : Data E)
    (hα : E.cfg.challenges.α ≠ 0) :
    ∃ D' : Data E, D'.computeNodes = D.computeNodes ∧ D'.skeleton = D.skeleton ∧
      GenericHonestPackage.ForestExponentOrder
        (D'.executionTemplate E.cfg.challenges.z) E.cfg.challenges.α :=
  ⟨normData D, normData_computeNodes D, normData_skeleton D,
    forestExponentOrder_normData_of_ne_zero D hα⟩

/-- **The narrowing cannot bite on either witness, at the level of the field itself.**  Both maps
carry an arbitrary `D`'s root exponent across unchanged, so a `Data` satisfying the sixteenth field
maps to a `Data` satisfying it — for every `D`, not only for the fixtures. -/
theorem both_witnesses_preserve_the_field {E : BuildableNockExecution F K} (D : Data E) :
    (wrapDataExponents D).computeNodes.label.stamp.lnPrevExponent = 0 ∧
      (normData D).computeNodes.label.stamp.lnPrevExponent = 0 :=
  ⟨D.root_line_exponent, D.root_line_exponent⟩

end Ticked

/-! ## D. Gate (5) restated at the layer that matters, and the `C6` contrast

`C6` failed because `FirstLineCarrier.c6_field_is_definitionally_firstLine` is `Iff.rfl`: the field
*was* the premise.  Here the two are not even the same type — the field is an `ℕ` equation on a
committed stamp, the premise a `K` equation on a published column — and §A.1 shows they are not
equivalent either, at the whole-commitment layer.

The receipt below is the one-line statement of the asymmetry, with both directions named. -/

/-- Forward: origin-1 published root yields the premise.  Backward: restamping
the Nat exponents leaves the published row (and so `firstLine`) untouched. -/
theorem gate_five_asymmetry {E : BuildableNockExecution F K} (D : Data E)
    (horigin : D.computeNodes.label.row.2.2.1.ln_prev = 1) :
    FirstLineStartsAtOne E.exec ∧
      mapNTree ComputeNode.row (restampRoot 9 D.computeNodes) =
        mapNTree ComputeNode.row D.computeNodes :=
  ⟨D.firstLine horigin, restampRoot_row 9 D.computeNodes⟩

/-! ## E.

* **the paper is the Seed-Input row of a seven-column table whose fifth column is `ln`.**
  Checked: the tabular preamble at `893` is `{@{}l l l l l l l@{}}` — seven columns — and the header
  cells at `895-901` are `State`, `Label`, `Left Child`, `Right Child`, `ln`, `count`, `acc_walk`.
  Line `903` reads `\textit{Seed Input} & $\bot$ & $\bot$ & $\bot$ & $1$ & …`, so the fifth cell is
  the `ln` cell and it is the literal `1`.  The first real row is `decompose` at `907`, whose `ln`
  cell is `α` on `908`.  Correct as cited.

* **the paper is inside the `Thm:Walk_IOP` proof, not a compute-table statement.**  Checked:
  the sentence "from the initial line constraint `ln(1) = α` and the line number increment
  constraint `ln(i) = α · ln(i-1)` it holds that `ln(k) = α^k`" sits in the `\begin{proof}[Proof of
  \ref{Thm:Walk_IOP}]` block.  Correct as cited, and the composition that brings it to the compute
  table is the paper and the paper ("Theorem~`Thm:Walk_IOP` applied to `L_comp` yields
  the result"), both verbatim.

**The `α¹` question, settled.**  `ln(1) = α` is a constraint on the walk table's
`ln` column at row 1.  `FirstLineStartsAtOne` is a condition on the compute table's **`ln_prev`**
column at row 0, and the paper against the paper identifies `ln_prev` at row `i`
with `ln(i-1)`.  So the slot the Lean premise reads is `ln(0)`, the pre-first slot — which the
paper's closed form `ln(k) = α^k` (`2283`) evaluates at `k = 0` to `α⁰ = 1` and which the worked
table displays as the literal `1` (`903`).  Neither cite admits a commitment starting at `α¹`:
`α¹` is the value of a *different* slot.  Both readings agree with the paper's `z^i` counted
from the first access.

**No citation defect found this round.**

## F. Structural receipts -/

theorem data_eta_at_batch139
    {E : BuildableNockExecution F K} (D : HonestCommitment.Data E) :
    D =
      { computeNodes := D.computeNodes
        memoryNodes := D.memoryNodes
        compute_rows := D.compute_rows
        memory_rows := D.memory_rows
        computeOK := D.computeOK
        memoryOK := D.memoryOK
        root_line_exponent := D.root_line_exponent
        root_line_origin := D.root_line_origin
        nounSizeBound := D.nounSizeBound
        Λ := D.Λ
        slotSemantics := D.slotSemantics
        recordEquations := D.recordEquations
        census := D.census
        sizeWindowBound := D.sizeWindowBound
        q_eq_ringChar := D.q_eq_ringChar
        skeletonBounded := D.skeletonBounded
        combinedBounded := D.combinedBounded } := by
  cases D
  rfl

/-- `ResidualPremises` still has exactly **four** fields, `firstLine` among them.  The carrier
addition discharges the premise for a holder of a *commitment*; it does not remove it from the
named-premises route, which is why the `§J` `firstLine` box does not move. -/
theorem residualPremises_still_four_at_batch139
    {E : BuildableNockExecution F K} (P : ResidualPremises E) :
    P =
      { inactiveDec := P.inactiveDec
        axisAtoms := P.axisAtoms
        q_eq_ringChar := P.q_eq_ringChar } := by
  cases P
  rfl

/-- `E` still has exactly **fourteen** fields. -/
theorem buildableExecution_eta_at_batch139 (E : BuildableNockExecution F K) :
    E =
      { q := E.q
        q_gt_one := E.q_gt_one
        Λ := E.Λ
        cfg := E.cfg
        execA := E.execA
        exec := E.exec
        exec_encode := E.exec_encode
        semanticData := E.semanticData
        memoryTrace := E.memoryTrace
        requestNodup := E.requestNodup
        recordCountBalance := E.recordCountBalance
        q_le_ringChar := E.q_le_ringChar
        two_ne_zero := E.two_ne_zero
        Ksz_lt_ringChar := E.Ksz_lt_ringChar
        programIOCapacity := E.programIOCapacity
        memoryIOCapacity := E.memoryIOCapacity } := by
  cases E
  rfl

/-! ## G. Section 2 items 6 and 7 — two disclosure findings, both compiled

### G.1 The `Data → firstLine` projection now EXISTS, so a hypothesis is carried unnecessarily

`Batch129.data_has_no_firstLine_projection` takes as a hypothesis exactly

```
g : ∀ (E : BuildableNockExecution F K), Data E → FirstLineStartsAtOne E.exec
```

and its docstring calls that projection *hypothetical* — "`Data` has no projection to
`FirstLineStartsAtOne`.  A hypothetical such projection would force …".  So the theorem's
hypothesis is now **inhabited**, its conclusion is provable **without** it, and its name and
docstring assert of the build something that has stopped being true. -/

/-- Relative `computeOK` does not pin `ln_prev = 1`.
The projection needs the published origin -/
theorem data_firstLine_projection_exists :
    ∀ (E : BuildableNockExecution F K) (D : Data E),
      D.computeNodes.label.row.2.2.1.ln_prev = 1 →
        FirstLineStartsAtOne E.exec :=
  fun _ D h => D.firstLine h

/-- Origin-1 published first row *is* `FirstLineStartsAtOne` -/
theorem batch129_hypothesis_is_now_redundant :
    ∀ (E : BuildableNockExecution F K) (D : Data E),
      D.computeNodes.label.row.2.2.1.ln_prev = 1 →
        (E.exec.computePubAt ⟨0, E.cfg.compRows_pos⟩).ln_prev = 1 :=
  fun E D h => data_firstLine_projection_exists E D h

/-! ### G.2 `firstLine` IS recoverable from the constructed `Data`, and the two consumption
receipts are weaker than their names

`dataOf_recovers_firstLine` below is the one-line refutation of the sentence.

Both that receipt and
`AO122.discharge_is_at_the_commitment_not_at_the_premises` are proved `⟨rfl, …⟩`, and their `rfl`
conjuncts are equations between two **proofs of a `Prop`**.  Lean has definitional proof
irrelevance, so such an equation holds whatever the two proofs are and however `dataOf` is defined —
`prop_equations_are_proof_irrelevant` makes that mechanical.  Neither conjunct therefore compiles
what its name suggests; the load-bearing content of "`dataOf` consumes `P.firstLine`" is the
*definition* of `computeNodesOf`, which no receipt in the build pins. -/

/-- `dataOf` does not recover `firstLine`; the pin
is the published first-row column of `E.exec` -/
theorem dataOf_recovers_firstLine (E : BuildableNockExecution F K)
    (horigin :
      (E.exec.computeRowAt ⟨0, E.cfg.compRows_pos⟩).2.2.1.ln_prev = 1) :
    FirstLineStartsAtOne E.exec := by
  unfold FirstLineStartsAtOne ExactExecution.computePubAt
  exact horigin

/-- Why the two `rfl` conjuncts carry no information: any two proofs of one `Prop` are equal by
`rfl`, so an equation of that shape is true before anything about `dataOf` is known. -/
theorem prop_equations_are_proof_irrelevant (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl

end

end Nock.RedTeam.Batch139

#print axioms Nock.RedTeam.Batch139.restampRoot_exponent
#print axioms Nock.RedTeam.Batch139.restampRoot_row
#print axioms Nock.RedTeam.Batch139.restampRoot_skel
#print axioms Nock.RedTeam.Batch139.restampRoot_skeletonOfNodes
#print axioms Nock.RedTeam.Batch139.restampRoot_computeNodesOK
#print axioms Nock.RedTeam.Batch139.F73.alpha_pow_nine
#print axioms Nock.RedTeam.Batch139.F73.narrowing_measured_exactly_at_f73
#print axioms Nock.RedTeam.Batch139.honest_ladder_pins_row_zero
#print axioms Nock.RedTeam.Batch139.dataOf_root_stamp_is_the_ladder_value
#print axioms Nock.RedTeam.Batch139.F73.excluded_exponent_is_not_a_line_number
#print axioms Nock.RedTeam.Batch139.wrapDataExponents_computeNodes
#print axioms Nock.RedTeam.Batch139.reExpData_computeNodes
#print axioms Nock.RedTeam.Batch139.normData_computeNodes
#print axioms Nock.RedTeam.Batch139.ticked_row_counterexample_survives
#print axioms Nock.RedTeam.Batch139.ticked_row_positive_survives
#print axioms Nock.RedTeam.Batch139.both_witnesses_preserve_the_field
#print axioms Nock.RedTeam.Batch139.gate_five_asymmetry
#print axioms Nock.RedTeam.Batch139.data_eta_at_batch139
#print axioms Nock.RedTeam.Batch139.residualPremises_still_four_at_batch139
#print axioms Nock.RedTeam.Batch139.buildableExecution_eta_at_batch139
#print axioms Nock.RedTeam.Batch139.data_firstLine_projection_exists
#print axioms Nock.RedTeam.Batch139.batch129_hypothesis_is_now_redundant
#print axioms Nock.RedTeam.Batch139.dataOf_recovers_firstLine
#print axioms Nock.RedTeam.Batch139.prop_equations_are_proof_irrelevant
